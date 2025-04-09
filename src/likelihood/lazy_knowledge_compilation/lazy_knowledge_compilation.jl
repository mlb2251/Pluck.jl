export normalize, compile, LazyKCState, LazyKCConfig

const Callstack = Vector{Int}
const Env = Vector{Any}
const World = Tuple{Any, BDD}
const ForwardResult = Tuple{Vector{World}, BDD}
const EMPTY_ENV::Env = Any[]

Base.@kwdef struct LazyKCConfig
    max_depth::Union{Int, Nothing} = nothing
    sample_after_max_depth::Bool = false
    use_strict_order::Bool = true
    use_reverse_order::Bool = false
    use_thunk_cache::Bool = false
    use_thunk_unions::Bool = true
    record_json::Bool = false
    disable_used_information::Bool = false
    disable_path_conditions::Bool = false
    singleton_cache::Bool = true
    show_bdd_size::Bool = false
    record_bdd_json::Bool = false
end

"""
Top-level compile function for lazy knowledge compilation.
"""
function compile(expr::PExpr, cfg::LazyKCConfig)
    state = LazyKCState(cfg)

    inner_ret, used_information = traced_compile_inner((expr), Pluck.EMPTY_ENV, state.manager.BDD_TRUE, state, 0)

    # expand IntDists into their 2^N possible values
    ret = []
    for (val, bdd) in inner_ret
        if val isa IntDist
            append!(ret, enumerate_int_dist(val, bdd))
        else
            push!(ret, (val, bdd))
        end
    end

    if state.cfg.show_bdd_size
        summed_size = sum(Int(RSDD.bdd_size(bdd)) for (ret, (bdd)) in ret)
        num_vars = length(state.sorted_callstacks)
        printstyled("vars: $num_vars nodes: $summed_size\n"; color=:blue)
        println("BDD sizes: $([(ret, Int(RSDD.bdd_size(bdd))) for (ret, (bdd)) in ret])")
    end

    if state.cfg.record_bdd_json
        bdd = get_true_result(results, nothing)
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
    weighted_results = [(v, RSDD.bdd_wmc(bdd)) for (v, bdd) in ret]

    free_bdd_manager(state.manager)

    return weighted_results
end

mutable struct LazyKCState
    callstack::Callstack
    var_of_callstack::Dict{Tuple{Callstack, Float64}, BDD}
    sorted_callstacks::Vector{Tuple{Callstack, Float64}}
    sorted_var_labels::Vector{Int}
    manager::RSDD.Manager
    depth::Int
    thunk_cache::Dict{Tuple{PExpr, Env, Callstack}, Any}
    num_forward_calls::Int
    viz::Any # Union{Nothing, BDDJSONLogger}
    cfg::LazyKCConfig

    function LazyKCState(;kwargs...)
        cfg = LazyKCConfig(;kwargs...)
        LazyKCState(cfg)
    end

    function LazyKCState(cfg::LazyKCConfig)
        manager = RSDD.Manager()
        state = new(
            Callstack(),
            Dict{Tuple{Callstack, Float64}, BDD}(),
            Tuple{Callstack, Float64}[],
            Int[],
            manager,
            0,
            Dict{Tuple{PExpr, Env, Callstack}, Any}(),
            0,
            nothing,
            cfg
        )

        if cfg.record_json
            state.viz = BDDJSONLogger(state)
        end
        return state
    end
end

function traced_compile_inner(expr::PExpr, env::Env, available_information::BDD, state::LazyKCState, strict_order_index::Int)
    # println(repeat(" ", state.depth) * "traced_compile_inner: $expr")
    # Check whether available_information is false.
    if !state.cfg.disable_used_information && bdd_is_false(available_information)
        return [], state.manager.BDD_FALSE
    end

    if state.cfg.max_depth !== nothing && state.depth > state.cfg.max_depth && !state.cfg.sample_after_max_depth
        return [], state.manager.BDD_TRUE
    end

    state.depth += 1
    push!(state.callstack, strict_order_index)

    if state.cfg.record_json
        record_forward!(state.viz, expr, env, available_information, strict_order_index)
    end

    result, used_information = compile_inner(expr, env, available_information, state)

    if state.cfg.record_json
        record_result!(state.viz, result, used_information)
    end

    pop!(state.callstack)
    state.num_forward_calls += 1
    state.depth -= 1
    return result, used_information
end


"""
Returns the single-variable BDD corresponding to the current callstack and probability, creating
the variable if it doesn't exist yet.
"""
function current_bdd_address(state::LazyKCState, p::Float64, available_information::BDD)
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

