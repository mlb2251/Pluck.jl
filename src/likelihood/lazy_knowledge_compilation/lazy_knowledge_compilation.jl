export normalize, compile, LazyKCState, LazyKCConfig, LazyKCStateDual, get_time_limit, set_time_limit!, LazyKCStats, CompileResult

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
    # use_thunk_cache::Bool = false
    use_thunk_unions::Bool = true
    disable_used_information::Bool = false
    disable_path_conditions::Bool = false
    singleton_cache::Bool = true
    show_bdd_size::Bool = false
    record_bdd_json::Bool = false
    record_json::Bool = false
    free_manager::Bool = true
    results_file::Union{Nothing, String} = nothing
    time_limit::Union{Nothing, Float64} = nothing
    state_vars::StateVars = StateVars()
    full_dist::Bool = false
    detailed_results::Bool = false
    stacktrace::Bool = true
end

set_time_limit!(cfg::LazyKCConfig, time_limit::Float64) = (cfg.time_limit = time_limit)
get_time_limit(cfg::LazyKCConfig) = cfg.time_limit


"""
Top-level compile function for lazy knowledge compilation.
"""
function compile(expr::PExpr, cfg::LazyKCConfig)
    state = LazyKCState(cfg)
    state.query = expr

    start!(get_timer(state), cfg.time_limit)
    bdd_set_time_limit(state.manager, get_timer(state))

    try 
        worlds, used_information = traced_compile_inner((expr), Pluck.EMPTY_ENV, state.manager.BDD_TRUE, state, 0)
    catch e
        if e isa StackOverflowError
            worlds = []
            state.stats.hit_limit = true
        else
            rethrow(e)
        end
    end
    stop!(get_timer(state))
    bdd_stop_time_limit(state.manager)

    if state.stats.hit_limit
        worlds = []
    end

    if state.cfg.full_dist
        worlds = infer_full_distribution(worlds, state)
    end

    # expand IntDists into their 2^N possible values
    if length(worlds) == 1 && worlds[1] isa IntDist
        (val, bdd) = worlds[1]
        worlds = enumerate_int_dist(val, bdd)
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

    state.cfg.free_manager && free_bdd_manager(state.manager)

    if state.cfg.detailed_results
        return CompileResult(weighted_results, state.stats)
    end

    return weighted_results
end

const global_lazykc_kwargs = Dict{Symbol, Any}()
function set_config!(;kwargs...)
    empty!(global_lazykc_kwargs)
    for (k, v) in kwargs
        global_lazykc_kwargs[k] = v
    end
end
get_config() = global_lazykc_kwargs

function set_outpath!()
    set_config!(results_file = timestamp_path("results.json"))
end

mutable struct LazyKCStats
    time::Float64
    num_forward_calls::Int
    hit_limit::Bool
end
LazyKCStats() = LazyKCStats(0.0, 0, false)
function Base.:+(a::LazyKCStats, b::LazyKCStats)
    LazyKCStats(a.time + b.time, a.num_forward_calls + b.num_forward_calls, a.hit_limit || b.hit_limit)
end

mutable struct LazyKCState
    callstack::Callstack
    var_of_callstack::Dict{Tuple{Callstack, Float64}, BDD}
    sorted_callstacks::Vector{Tuple{Callstack, Float64}}
    sorted_var_labels::Vector{Int}
    manager::RSDD.Manager
    depth::Int
    thunk_cache::Dict{Tuple{PExpr, Env, Callstack}, Any}
    stats::LazyKCStats
    viz::Any # Union{Nothing, BDDJSONLogger}
    cfg::LazyKCConfig
    param2metaparam::Dict{Int, Int}
    timer::Ttimer
    query::Union{Nothing, PExpr}
    stacktrace::Vector{PExpr}
end

struct CompileResult
    worlds
    stats
end

get_timer(state::LazyKCState) = state.timer


function LazyKCState(;kwargs...)
    cfg = LazyKCConfig(;kwargs...)
    LazyKCState(cfg)
end

function LazyKCState(cfg::LazyKCConfig)
    manager = RSDD.Manager()
    state = LazyKCState(
        Callstack(),
        Dict{Tuple{Callstack, Float64}, BDD}(),
        Tuple{Callstack, Float64}[],
        Int[],
        manager,
        0,
        Dict{Tuple{PExpr, Env, Callstack}, Any}(),
        LazyKCStats(),
        nothing,
        cfg,
        Dict{Int, Int}(),
        Ttimer(),
        nothing,
        PExpr[]
    )

    if cfg.record_json
        state.viz = BDDJSONLogger(state)
    end
    return state
end

function LazyKCStateDual(vector_size::Integer; kwargs...)
    cfg = LazyKCConfig(;kwargs...)
    LazyKCStateDual(vector_size, cfg)
end

function LazyKCStateDual(vector_size::Integer, cfg::LazyKCConfig)
    manager = RSDD.ManagerDual(vector_size)
    state = LazyKCState(
        Callstack(),
        Dict{Tuple{Callstack, Float64}, BDD}(),
        Tuple{Callstack, Float64}[],
        Int[],
        manager,
        0,
        Dict{Tuple{PExpr, Env, Callstack}, Any}(),
        0,
        nothing,
        cfg,
        Dict{Int, Int}(),
        Ttimer(),
        nothing,
        PExpr[]
    )

    if cfg.record_json
        state.viz = BDDJSONLogger(state)
    end
    return state
end

get_config(state::LazyKCState) = state.cfg

function traced_compile_inner(expr, env, path_condition, state::LazyKCState, strict_order_index)
    # Check whether path_condition is false.
    if !state.cfg.disable_used_information && bdd_is_false(path_condition)
        return false_path_condition_worlds(state)
    end

    if state.cfg.max_depth !== nothing && state.depth > state.cfg.max_depth && !state.cfg.sample_after_max_depth
        state.stats.hit_limit = true
        return inference_error_worlds(state)
    end

    if check_time_limit_lower_bound(state.timer)
        state.stats.hit_limit = true
        return inference_error_worlds(state)
    end

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
    state.stats.num_forward_calls += 1
    state.depth -= 1

    if bdd_time_limit_exceeded(state.manager)
        state.stats.hit_limit = true
        return inference_error_worlds(state)
    end

    return result, used_information
end

"""
When compiling a thunk, we assume it is a Thunk that will return a NativeValue{PExpr}, so
we first evaluate that thunk (callstack doesnt matter) then use the result to compile the PExpr
at the given callstack / strict_order_index.
"""
function compile_inner(thunk::Thunk, env, path_condition, state)
    bind_evaluate(thunk, env, path_condition, state) do e, path_condition
        @assert e isa NativeValue && e.value isa PExpr "Thunk must be evaluated to a NativeValue{PExpr}, got $(e) :: $(typeof(e))"
        return compile_inner(e.value, env, path_condition, state)
    end
end

"""
Returns the single-variable BDD corresponding to the current callstack and probability, creating
the variable if it doesn't exist yet.
"""
function current_address(state::LazyKCState, p::Float64)
    if haskey(state.var_of_callstack, (state.callstack, p))
        return state.var_of_callstack[(state.callstack, p)]
    end
    callstack = copy(state.callstack)

    if !state.cfg.use_strict_order
        # Lazy order
        addr = RSDD.bdd_new_var(state.manager, true)
    else
        # Strict order
        # Find position in the variable order in which to create the new variable.
        # This is based on where in state.sorted_callstacks this callstack should go.
        # We want to do a binary search over the sorted list. The order on callstacks
        # is lexicographic, so we can do this with a binary search.
        i = searchsortedfirst(state.sorted_callstacks, (state.callstack, p); by = x -> x[1], rev = state.cfg.use_reverse_order)
        # Insert the callstack in the sorted list.
        addr = RSDD.bdd_new_var_at_position(state.manager, i - 1, true) # Rust uses 0-indexing
        insert!(state.sorted_callstacks, i, (callstack, p))
        insert!(state.sorted_var_labels, i, Int(bdd_topvar(addr)))
    end
    state.var_of_callstack[(callstack, p)] = addr
    return addr
end


function pretty_callstack(callstack, strict_order_index=nothing)
    if !isnothing(strict_order_index)
        callstack = vcat(callstack, strict_order_index)
    end
    return "." *join(callstack, ".")
end

const VERBOSE = Ref{Bool}(false)
set_verbose!(verbose::Bool) = (VERBOSE[] = verbose)
get_verbose()::Bool = VERBOSE[]

function print_enter(expr, env, state)
    get_verbose() || expr isa PExpr{PrintOp} || return
    cs = pretty_callstack(state.callstack)
    printstyled("$cs $expr :: $(typeof(expr))\n", color=:yellow)
end

function pretty_worlds(worlds::Vector; weights=false)
    res = "["
    for (i, (val, bdd)) in enumerate(worlds)
        res *= string(val)
        weights && (res *= " (P=" * @sprintf("%.1e", RSDD.bdd_wmc(bdd)) * ")")
        i < length(worlds) && (res *= ", ")
    end
    return res * "]"
end

function pretty_result(result; weights=false)
    if result isa Vector
        return "-> " * pretty_worlds(result; weights=weights)
    else
        return "-> $result :: $(typeof(result))"
    end
end

function print_exit(expr, result, env, state)
    get_verbose() || expr isa PExpr{PrintOp} || return
    cs = pretty_callstack(state.callstack)
    green = "$cs $expr :: $(typeof(expr)) "
    blue = pretty_result(result; weights=true)
    printstyled(green, color=:green)
    length(green) + length(blue) > 80 && print("\n")
    printstyled(blue * "\n", color=:blue)
end