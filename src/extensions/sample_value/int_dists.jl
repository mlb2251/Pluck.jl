function compile_inner(expr::PExpr{MkIntOp}, env::Env, null::Nothing, state::SampleValueState)
    bitwidth = traced_compile_inner(expr.args[1], env, null, state, 0)
    val = traced_compile_inner(expr.args[2], env, null, state, 1)
    width = bitwidth.value
    v = val.value
    bools = digits(Bool, v, base = 2, pad = width)
    return IntDist(bools)
end

function compile_inner(expr::PExpr{UniformIntOp}, env::Env, null::Nothing, state::SampleValueState)
    bitwidth = traced_compile_inner(expr.args[1], env, null, state, 0)
    width = bitwidth.value
    bits = Vector{Bool}(undef, width)

    for i = 1:width
        callstack_to_check = ([state.callstack..., i], 0.5)
        addr = nothing
        if state.var_of_callstack !== nothing && haskey(state.var_of_callstack, callstack_to_check)
            addr = state.var_of_callstack[callstack_to_check]
        end

        bit_val = rand(Bool)
        # If we have a constraint and a BDD var for this bit, respect it.
        if addr !== nothing && state.constraint !== nothing
            if bdd_is_true(bdd_implies(state.constraint, addr))
                bit_val = true
            elseif bdd_is_true(bdd_implies(state.constraint, !addr))
                bit_val = false
            end
        end

        if addr !== nothing
            state.trace[callstack_to_check] = bit_val
        end
        bits[i] = bit_val
    end

    return IntDist(bits)
end

function compile_inner(expr::PExpr{IntDistEqOp}, env::Env, null::Nothing, state::SampleValueState)
    first_int_dist = traced_compile_inner(expr.args[1], env, null, state, 0)
    second_int_dist = traced_compile_inner(expr.args[2], env, null, state, 1)
    @assert length(first_int_dist.bits) == length(second_int_dist.bits)
    are_equal = all(first_int_dist.bits[i] == second_int_dist.bits[i] for i in eachindex(first_int_dist.bits))
    return are_equal ? Pluck.TRUE_VALUE : Pluck.FALSE_VALUE
end

function compile_inner(expr::PExpr{UniformIntRangeOp}, env::Env, null::Nothing, state::SampleValueState)
    bitwidth = traced_compile_inner(expr.args[1], env, null, state, 0)
    lo = traced_compile_inner(expr.args[2], env, null, state, 1)
    hi = traced_compile_inner(expr.args[3], env, null, state, 2)
    width = bitwidth.value
    start = lo.value
    stop = hi.value
    @assert start isa Int && stop isa Int "uniform_int_range expects native Int bounds"
    @assert width isa Int "uniform_int_range expects native Int bitwidth"
    @assert stop >= start "uniform_int_range upper bound must be >= lower bound"

    function sample_range(lo_val::Int, hi_val::Int, depth::Int)
        if lo_val == hi_val
            return lo_val
        end
        mid = lo_val + (hi_val - lo_val) ÷ 2
        lower_size = mid - lo_val + 1
        upper_size = hi_val - mid
        p = lower_size / (lower_size + upper_size)
        callstack_to_check = ([state.callstack..., depth], p)

        result = if haskey(state.trace, callstack_to_check)
            state.trace[callstack_to_check]
        elseif state.constraint !== nothing && state.var_of_callstack !== nothing && haskey(state.var_of_callstack, callstack_to_check)
            var = state.var_of_callstack[callstack_to_check]
            if bdd_is_true(bdd_implies(state.constraint, var))
                true
            elseif bdd_is_true(bdd_implies(state.constraint, !var))
                false
            else
                rand() < p
            end
        else
            rand() < p
        end

        state.trace[callstack_to_check] = result
        return result ? sample_range(lo_val, mid, depth + 1) : sample_range(mid + 1, hi_val, depth + 1)
    end

    val = sample_range(start, stop, 0)
    bools = digits(Bool, val, base = 2, pad = width)
    return IntDist(bools)
end