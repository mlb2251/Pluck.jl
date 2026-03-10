function compile_inner(expr::PExpr{FlipOp}, env::Env, null::Nothing, state::SampleValueState)
    p = traced_compile_inner(expr.args[1], env, null, state, 0)
    (p isa NativeValue) || pluck_error(state, "FlipOp: expected NativeValue, got $(p) :: $(typeof(p)) in $expr")
    p = p.value
    isapprox(p, 0.0) && return Pluck.FALSE_VALUE
    isapprox(p, 1.0) && return Pluck.TRUE_VALUE

    callstack_to_check = ([state.callstack..., 1], p)

    # check if we've already set this value
    if haskey(state.trace, callstack_to_check)
        return state.trace[callstack_to_check] ? Pluck.TRUE_VALUE : Pluck.FALSE_VALUE
    end

    if state.constraint === nothing || state.var_of_callstack === nothing || !haskey(state.var_of_callstack, callstack_to_check)
        # Freely sample a value. 
        result = rand() < p
        state.trace[callstack_to_check] = result
        return result ? Pluck.TRUE_VALUE : Pluck.FALSE_VALUE
    end


    # check if the value is constrained by our constraint
    var = state.var_of_callstack[callstack_to_check]
    bdd_is_true(bdd_implies(state.constraint, var)) && return Pluck.TRUE_VALUE
    bdd_is_true(bdd_implies(state.constraint, !var)) && return Pluck.FALSE_VALUE
    result = rand() < p
    state.trace[callstack_to_check] = result
    return result ? Pluck.TRUE_VALUE : Pluck.FALSE_VALUE
end
