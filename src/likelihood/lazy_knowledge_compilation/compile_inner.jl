
function compile_inner(expr::PExpr{FlipOp}, env, path_condition, state)
    if state.cfg.dual
        return compile_flip_dual(expr, env, path_condition, state)
    end

    bind_compile(expr.args[1], env, path_condition, state, 0) do p, path_condition

        p = p.value

        @assert p isa Float64 "p is not a Float64, got $(typeof(p))"

        isapprox(p, 0.0) && return pure_monad(Pluck.FALSE_VALUE, path_condition, state)
        isapprox(p, 1.0) && return pure_monad(Pluck.TRUE_VALUE, path_condition, state)

        # If we are past the max depth, AND we are sampling after the max depth, AND 
        # this flip is new (not previously instantiated), THEN sample a value.
        if state.cfg.max_depth !== nothing && state.depth > state.cfg.max_depth && state.cfg.sample_after_max_depth && !haskey(state.var_of_callstack, (state.callstack, p))
            sampled_value = rand() < p ? Pluck.TRUE_VALUE : Pluck.FALSE_VALUE
            return pure_monad(sampled_value, path_condition, state)
        end

        # Otherwise, we perform the usual logic.
        # BDDs do not represent quantitative probabilities. Therefore, for each 
        # different probability `p`, we need to create a new variable in the BDD.
        push!(state.callstack, 1)
        addr = current_address(state, p)

        RSDD.set_weight(state.manager, bdd_topvar(addr), 1.0 - p, p)
        pop!(state.callstack)
        return if_then_else_monad(Pluck.TRUE_VALUE, Pluck.FALSE_VALUE, addr, path_condition, state)
    end
end

"""
Returns the single-variable BDD corresponding to the current callstack and probability, creating
the variable if it doesn't exist yet.
"""
function current_address(state::LazyKCState, p::Float64)
    if haskey(state.var_of_callstack, (state.callstack, p))
        # @assert length(state.stacktrace_of_callstack[(state.callstack, p)]) == length(state.stacktrace)
        # for (e1, e2) in zip(state.stacktrace_of_callstack[(state.callstack, p)], state.stacktrace)
        #     @assert objectid(e1) == objectid(e2)
        # end
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
        inner_bdd = RSDD.bdd_new_var_at_position(state.manager, i - 1, true)
        label = Int(RSDD.bdd_topvar(inner_bdd))
        addr = var_bdd(inner_bdd, label) # Rust uses 0-indexing
        insert!(state.sorted_callstacks, i, (callstack, p))
        insert!(state.sorted_var_labels, i, label)
    end
    state.var_of_callstack[(callstack, p)] = addr
    # state.stacktrace_of_callstack[(callstack, p)] = copy(state.stacktrace)
    return addr
end