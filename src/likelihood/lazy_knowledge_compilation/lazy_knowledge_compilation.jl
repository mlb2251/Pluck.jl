export normalize, compile, LazyKCState, LazyKCConfig, get_time_limit, set_time_limit!, LazyKCStats, CompileResult, deterministic_world, is_deterministic, wmc, find_world, find_true_world, true_weight, true_bdd, free_state, toplevel_compile, toplevel_evaluate, full_dist, force_thunks

const Callstack = Vector{Int}
const WorldT{T} = Tuple{T, BDD}
const World = WorldT{Any}
const GuardedWorldsT{T} = Tuple{Vector{WorldT{T}}, BDD}
const GuardedWorlds = GuardedWorldsT{Any}
const EMPTY_ENV::Env = EnvNil()

Base.@kwdef mutable struct LazyKCConfig
    max_depth::Union{Int, Nothing} = nothing
    sample_after_max_depth::Bool = false
    use_strict_order::Bool = true
    use_reverse_order::Bool = false
    use_thunk_unions::Bool = true
    disable_used_information::Bool = false
    disable_path_conditions::Bool = false
    singleton_cache::Bool = true
    log::Bool = false
    time_limit::Union{Nothing, Float64} = nothing
    ite_limit::Union{Nothing, Int} = nothing
    stacktrace::Bool = true
    vector_size::Int = 0
    dual::Bool = false
end


set_time_limit!(cfg::LazyKCConfig, time_limit::Float64) = (cfg.time_limit = time_limit)
get_time_limit(cfg::LazyKCConfig) = cfg.time_limit


mutable struct LazyKCStats
    time::Union{TimeState, Nothing}
    num_forward_calls::Int
    hit_limit::Bool
    num_recursive_calls::Int
end
LazyKCStats() = LazyKCStats(nothing, 0, false, 0)
function Base.:+(a::LazyKCStats, b::LazyKCStats)
    LazyKCStats(a.time + b.time, a.num_forward_calls + b.num_forward_calls, a.hit_limit || b.hit_limit, a.num_recursive_calls + b.num_recursive_calls)
end

function Base.show(io::IO, stats::LazyKCStats)
    print(io, "LazyKCStats(time=$(stats.time), num_forward_calls=$(stats.num_forward_calls), hit_limit=$(stats.hit_limit), num_recursive_calls=$(stats.num_recursive_calls))")
end

mutable struct LazyKCState
    callstack::Callstack
    var_of_callstack::Dict{Tuple{Callstack, Float64}, BDD}
    sorted_callstacks::Vector{Tuple{Callstack, Float64}}
    stacktrace_of_callstack::Dict{Tuple{Callstack, Float64}, Vector{PExpr}}
    sorted_var_labels::Vector{Int}
    manager::RSDD.Manager
    depth::Int
    thunk_cache::Dict{Tuple{PExpr, Env, Callstack}, Any}
    stats::LazyKCStats
    viz::Any # Union{Nothing, BDDJSONLogger}
    cfg::LazyKCConfig
    var2metaparam::Dict{Int, Int}
    timer::Ttimer
    stacktrace::Vector{PExpr}
end

get_timer(state::LazyKCState) = state.timer

function LazyKCState(;kwargs...)
    cfg = LazyKCConfig(;kwargs...)
    LazyKCState(cfg)
end

function LazyKCState(cfg::LazyKCConfig)
    manager = RSDD.Manager(; vector_size=cfg.vector_size, dual=cfg.dual)
    state = LazyKCState(
        Callstack(),
        Dict{Tuple{Callstack, Float64}, BDD}(),
        Tuple{Callstack, Float64}[],
        Dict{Tuple{Callstack, Float64}, Vector{PExpr}}(),
        Int[],
        manager,
        0,
        Dict{Tuple{PExpr, Env, Callstack}, Any}(),
        LazyKCStats(),
        nothing,
        cfg,
        Dict{Int, Int}(),
        Ttimer(),
        PExpr[]
    )

    if cfg.log
        state.viz = BDDJSONLogger(state)
    end
    return state
end

get_config(state::LazyKCState) = state.cfg

function traced_compile_inner(expr, env, path_condition, state::LazyKCState, strict_order_index)
    # Check whether path_condition is false.
    if bdd_is_false(path_condition) &&!state.cfg.disable_used_information
        return false_path_condition_worlds(state)
    end

    if state.cfg.max_depth !== nothing && state.depth > state.cfg.max_depth && !state.cfg.sample_after_max_depth
        state.stats.hit_limit = true
    end

    if check_time_limit_lower_bound(state.timer)
        state.stats.hit_limit = true
    end

    if bdd_ite_limit_exceeded(state.manager)
        state.stats.hit_limit = true
    end

    state.stats.hit_limit && return inference_error_worlds(state)

    state.depth += 1
    push!(state.callstack, strict_order_index)

    if state.cfg.log
        record_forward!(state.viz, expr, env, path_condition, strict_order_index)
    end

    print_enter(expr, env, state)
    result, used_information = compile_inner(expr, env, path_condition, state)
    print_exit(expr, result, env, state)

    if state.cfg.log
        record_result!(state.viz, result, used_information)
    end

    pop!(state.callstack)
    state.depth -= 1
    state.stats.num_forward_calls += 1

    if bdd_time_limit_exceeded(state.manager)
        state.stats.hit_limit = true
    end

    if bdd_ite_limit_exceeded(state.manager)
        state.stats.hit_limit = true
    end

    state.stats.hit_limit && return inference_error_worlds(state)

    return result, used_information
end

function with_stacktrace(f::F, state::LazyKCState, expr::Union{PExpr, Nothing}) where F <: Function
    push!(state.stacktrace, expr)
    res = f()
    pop!(state.stacktrace)
    return res
end

function with_stacktrace(f::F, state, expr::Union{PExpr, Nothing}) where F <: Function
    f() # no stacktrace implemented
end

struct LazyKCResult
    worlds::Union{Nothing, Vector{Tuple{Any, BDD}}} # `Nothing` means some depth/time/etc limit was hit
    used_information::BDD
    state::LazyKCState
end

function toplevel_compile(expr::PExpr; cfg=LazyKCConfig(), state=LazyKCState(cfg), env=EMPTY_ENV, path_condition=state.manager.BDD_TRUE)::LazyKCResult
    thunk = make_thunk(expr, env, 0, state)
    toplevel_evaluate(thunk, state; path_condition)
end

function toplevel_compile(expr::String; kwargs...)
    toplevel_compile(parse_expr(expr); kwargs...)
end

function toplevel_evaluate(thunk, state::LazyKCState; path_condition=state.manager.BDD_TRUE)

    tstart = ttime()
    start!(get_timer(state), state.cfg.time_limit)
    bdd_set_time_limit(state.manager, get_timer(state))
    bdd_start_ite_limit(state.manager, state.cfg.ite_limit)

    pluck_error = nothing

    try 
        worlds, used_information = evaluate(thunk, path_condition, state)
    catch e
        if e isa StackOverflowError
            println("StackOverflowError in pluck when compiling $thunk")
            state.stats.hit_limit = true
        elseif e isa PluckError
            # dont throw error here or stack trace will be really long, just set flag
            pluck_error = e
        else
            rethrow(e)
        end
    end
    stop!(get_timer(state))
    bdd_stop_ite_limit(state.manager)

    if !isnothing(pluck_error)
        # throw error here so the stack trace isn't super long
        showerror(stderr, pluck_error)
        throw("Pluck Error encountered during execution of $thunk, see stack trace above for details")
    end

    if state.stats.hit_limit
        worlds = nothing
        used_information = state.manager.BDD_TRUE
    end

    state.stats.num_recursive_calls = bdd_num_recursive_calls(state.manager)
    state.stats.time = ttime() - tstart

    return LazyKCResult(worlds, used_information, state)
end

function free_state(state::LazyKCState)
    RSDD.free_bdd_manager(state.manager)
    RSDD.free_wmc_params(state.manager.weights)
end


function deterministic_world(ret::LazyKCResult)
    return deterministic_world(ret.worlds)
end

function deterministic_world(worlds)
    isnothing(worlds) && return nothing
    isempty(worlds) && return nothing
    # @assert length(worlds) == 1 "Expected a single deterministic world, got $(length(worlds)) worlds"
    (val, bdd) = worlds[1]
    @assert is_deterministic(bdd) "Expected either weight 1.0 or True BDD, got $bdd"
    return val
end

function is_deterministic(bdd::BDD)
    return bdd_is_true(bdd)
end
function is_deterministic(weight::Float64)
    return isapprox(weight, 1.0)
end

function normalize(weighted_worlds)
    isempty(weighted_worlds) && return weighted_worlds
    weights = [weight for (_, weight) in weighted_worlds]
    total = sum(weights)
    return [(world, weight / total) for (world, weight) in weighted_worlds]
end

function normalize_dual(results)
    isempty(results) && return results
    duals = [dual for (_, dual) in results]
    primals = [primal for (primal, _) in duals]
    derivs = [deriv for (_, deriv) in duals]
    total_primal = sum(primals)
    total_deriv = sum(derivs)

    return [(world, (primal / total_primal, (total_primal*deriv - primal*total_deriv)/(total_primal^2))) for (world, (primal, deriv)) in results]
end



function wmc(ret::LazyKCResult)
    return wmc(ret.worlds)
end
function wmc(worlds::Vector{Tuple{Any, BDD}})
    return Tuple{Any, Float64}[(val, bdd_wmc(bdd)) for (val, bdd) in worlds]
end

function find_world(worlds, constructor::Symbol)
    for (i, (val, _)) in enumerate(worlds)
        if val isa Value && val.constructor == constructor
            return i
        end
    end
    return nothing
end

function find_true_world(worlds)
    return find_world(worlds, :True)
end

true_weight(ret::LazyKCResult) = true_weight(ret.worlds)
function true_weight(worlds::Vector{Tuple{Any, Float64}})
    index = find_true_world(worlds)
    isnothing(index) && return 0.0
    return worlds[index][2]
end

function true_bdd(ret::LazyKCResult)
    index = find_true_world(ret.worlds)
    isnothing(index) && return ret.state.manager.BDD_FALSE
    return ret.worlds[index][2]
end