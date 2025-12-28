function compile_inner(expr::PExpr{FlipOp}, env, path_condition, state)
    npartials = state.manager.vector_size

    bind_compile(expr.args[1], env, path_condition, state, 0) do p, path_condition
        # handle dual number mode
        if state.cfg.dual
            # println("p: $p expr: $expr")
            if p isa Value
                pluck_error(state, "FlipOp: expected NativeValue, got $(p) :: $(typeof(p)) in $expr")
            end
            metaparam = p.value isa Int ? p.value : nothing
            p = isnothing(metaparam) ? p.value : 0.5 # default value used in dual mode, can swap out for another later

            push!(state.callstack, 1)
            addr = current_address(state, p)

            topvar = bdd_topvar(addr)
            partials_hi = zeros(Float64, npartials)
            partials_lo = zeros(Float64, npartials)

            if !isnothing(metaparam)
                state.var2metaparam[topvar] = metaparam
                partials_hi[metaparam+1] = 1.0
                partials_lo[metaparam+1] = -1.0
            end
            set_weight_deriv(state.manager.weights, topvar, 1.0 - p, partials_lo, p, partials_hi)
            pop!(state.callstack)
            return if_then_else_monad(Pluck.TRUE_VALUE, Pluck.FALSE_VALUE, addr, path_condition, state)
        end

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