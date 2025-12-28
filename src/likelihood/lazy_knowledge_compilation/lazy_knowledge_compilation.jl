export normalize, compile, LazyKCState, LazyKCConfig, get_time_limit, set_time_limit!, LazyKCStats, CompileResult

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
    show_bdd_size::Bool = false
    record_bdd_json::Bool = false
    record_json::Bool = false
    free_manager::Bool = true
    free_weights::Bool = true
    results_file::Union{Nothing, String} = nothing
    time_limit::Union{Nothing, Float64} = nothing
    ite_limit::Union{Nothing, Int} = nothing
    state_vars::StateVars = StateVars()
    full_dist::Bool = false
    detailed_results::Bool = false
    stacktrace::Bool = true
    vector_size::Int = 0
    dual::Bool = false
    state = nothing
    path_condition = nothing
    env = EMPTY_ENV
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

    if cfg.record_json
        state.viz = BDDJSONLogger(state)
    end
    return state
end

get_config(state::LazyKCState) = state.cfg

struct CompileResult
    worlds
    stats
    raw_worlds
    state
end


"""
Top-level compile function for lazy knowledge compilation.
"""
function compile(expr::PExpr, cfg::LazyKCConfig)
    state = cfg.state === nothing ? LazyKCState(cfg) : cfg.state
    state.cfg = cfg

    tstart = ttime()
    start!(get_timer(state), cfg.time_limit)
    bdd_set_time_limit(state.manager, get_timer(state))
    bdd_start_ite_limit(state.manager, cfg.ite_limit)

    path_condition = isnothing(cfg.path_condition) ? state.manager.BDD_TRUE : cfg.path_condition
    threw_error = false

    try 
        worlds, used_information = traced_compile_inner((expr), cfg.env, path_condition, state, 0)
    catch e
        if e isa StackOverflowError
            println("StackOverflowError in pluck when compiling $expr")
            worlds = []
            state.stats.hit_limit = true
        elseif e isa PluckError
            # dont throw error here or stack trace will be really long, just set flag
            threw_error=true
        else
            rethrow(e)
        end
    end
    stop!(get_timer(state))
    # bdd_stop_ite_limit(state.manager)

    if threw_error
        # throw error here so the stack trace isn't super long
        throw("Pluck Error")
    end

    if state.stats.hit_limit
        worlds, used_information = inference_error_worlds(state)
    end

    if state.cfg.full_dist
        worlds = infer_full_distribution(worlds, state)
    end

    # expand IntDists into their 2^N possible values
    if length(worlds) == 1 && worlds[1] isa IntDist
        (val, bdd) = worlds[1]
        worlds = enumerate_int_dist(val, bdd, state.manager)
    end

    if state.cfg.show_bdd_size
        summed_size = sum(Int(RSDD.bdd_size(bdd)) for (val, bdd) in worlds)
        num_vars = length(state.sorted_callstacks)
        printstyled("vars & nodes: $num_vars & $summed_size\n"; color=:blue)
        println("BDD sizes: $([(val, Int(RSDD.bdd_size(bdd))) for (val, bdd) in worlds])")
    end

    if state.cfg.record_bdd_json
        bdd = get_true_result(worlds, nothing)
        if isnothing(bdd)
            @warn "No true result found to record"
        else
            record_bdd(state, bdd)
        end
    end

    if state.cfg.record_json
        dir = timestamp_dir(; base = "out/bdd")
        write_out(state.viz, joinpath(dir, "compile_inner.json"))
        println(webaddress("html/compile_inner.html", joinpath(dir, "compile_inner.json"), false))
    end

    # weighted model count to get the actual probabilities
    weighted_results = [(val, RSDD.bdd_wmc(bdd)) for (val, bdd) in worlds]

    state.stats.num_recursive_calls = bdd_num_recursive_calls(state.manager)
    state.stats.time = ttime() - tstart

    state.cfg.free_manager && free_bdd_manager(state.manager)
    state.cfg.free_weights && free_wmc_params(state.manager.weights)

    if state.cfg.detailed_results
        worlds = state.cfg.free_manager ? nothing : worlds # they'd be invalid otherwise
        return CompileResult(weighted_results, state.stats, worlds, state)
    end

    return weighted_results
end

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

    if state.cfg.record_json
        record_forward!(state.viz, expr, env, path_condition, strict_order_index)
    end

    if state.cfg.stacktrace
        push!(state.stacktrace, expr)
    end

    print_enter(expr, env, state)
    result, used_information = compile_inner(expr, env, path_condition, state)
    print_exit(expr, result, env, state)

    if state.cfg.stacktrace
        pop!(state.stacktrace)
    end

    if state.cfg.record_json
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
