


function compile_inner(expr::PExpr{FlipOp}, env, trace, state::LazyEnumeratorEvalState)
    ps = traced_compile_inner(expr.args[1], env, trace, state, 0)
    bind_monad(ps, trace, state) do p, trace
        p = p.value
        isapprox(p, 0.0) && return pure_monad(Pluck.FALSE_VALUE, trace, state)
        isapprox(p, 1.0) && return pure_monad(Pluck.TRUE_VALUE, trace, state)

        push!(state.callstack, 1)
        addr = current_address(state, p)
        pop!(state.callstack)

        # check if we already have this choice in the trace
        choice = get_choice(trace, addr, state)
        if choice !== nothing
            val = choice.val ? Pluck.TRUE_VALUE : Pluck.FALSE_VALUE
            return pure_monad(val, trace, state)
        end

        return if_then_else_monad(Pluck.TRUE_VALUE, Pluck.FALSE_VALUE, (addr, p), trace, state)
    end
end


#####################
# Eager compilation #
#####################


function compile_inner(expr::PExpr{App}, env, trace, state::LazyEnumeratorEvalState{EagerMode})
    # in strict semantics its safe to evaluate xs independently of f instead of nesting
    # it within the bind call.
    fs = traced_compile_inner(expr.args[1], env, trace, state, 0)
    xs = traced_compile_inner(expr.args[2], env, Trace(), state, 1)
    results = []
    for (f, ftrace) in fs
        for (x, xtrace) in xs
            state.hit_limit && return inference_error_worlds(state)
            new_env = EnvCons(f.name, x, f.env)
            new_trace = cat_trace(ftrace, xtrace)
            for result in traced_compile_inner(f.expr, new_env, new_trace, state, 2)
                push!(results, result)
            end
        end
    end
    return results
end

function compile_inner(expr::PExpr{Construct}, env, trace, state::LazyEnumeratorEvalState{EagerMode})
    # in strict semantics its safe to evaluate all arguments independently of each other.
    options_of_arg = []
    for (i, arg) in enumerate(expr.args)
        push!(options_of_arg, traced_compile_inner(arg, env, Trace(), state, i))
    end
    results = []
    for args in Iterators.product(options_of_arg...)
        if check_time_limit(state)
            state.hit_limit = true
            return inference_error_worlds(state)
        end
        new_trace = trace
        new_args = []
        for (arg, arg_trace) in args
            new_trace = cat_trace(new_trace, arg_trace)
            push!(new_args, arg)
        end
        push!(results, (Value(expr.head.constructor, new_args), new_trace))
    end
    return results
end

function compile_inner(expr::PExpr{NativeEqOp}, env, trace, state::LazyEnumeratorEvalState{EagerMode})
    # in strict semantics its safe to evaluate second argument independently of first
    # instead of nesting it within the bind call.   
    first_arg_results = traced_compile_inner(expr.args[1], env, trace, state, 0)
    second_arg_results = traced_compile_inner(expr.args[2], env, trace, state, 1)
    return bind_monad(first_arg_results, trace, state) do arg1, trace
        return bind_monad(second_arg_results, trace, state) do arg2, trace
            if arg1.value == arg2.value
                return [(Pluck.TRUE_VALUE, trace)]
            else
                return [(Pluck.FALSE_VALUE, trace)]
            end
        end
    end
end

function compile_inner(expr::PExpr{MkIntOp}, env, trace, state::LazyEnumeratorEvalState)
    bind_monad(traced_compile_inner(expr.args[1], env, trace, state, 0), trace, state) do bitwidth, trace1
        bind_monad(traced_compile_inner(expr.args[2], env, trace1, state, 1), trace1, state) do val, trace2
            width = bitwidth.value
            v = val.value
            bools = digits(Bool, v, base = 2, pad = width)
            return pure_monad(IntDist(bools), trace2, state)
        end
    end
end

function compile_inner(expr::PExpr{UniformIntOp}, env, trace, state::LazyEnumeratorEvalState)
    bitwidth_worlds = traced_compile_inner(expr.args[1], env, trace, state, 0)
    results = bind_monad(bitwidth_worlds, trace, state) do bitwidth, tr
        width = bitwidth.value
        @assert width isa Int "uniform_int expects a native Int bitwidth, got $(typeof(width))"

        initial = [(Bool[], tr)]
        res = initial
        for i = 1:width
            res = bind_monad(res, tr, state) do bits_so_far, tr2
                push!(state.callstack, i)
                addr = current_address(state, 0.5)
                pop!(state.callstack)

                choice = get_choice(tr2, addr, state)
                if choice !== nothing
                    new_bits = [bits_so_far...; choice.val]
                    return pure_monad(new_bits, tr2, state)
                end

                bit_true = [bits_so_far...; true]
                bit_false = [bits_so_far...; false]
                return if_then_else_monad(bit_true, bit_false, (addr, 0.5), tr2, state)
            end
        end

        return res
    end
    return bind_monad(results, trace, state) do bits, tr
        pure_monad(IntDist(bits), tr, state)
    end
end

function compile_inner(expr::PExpr{UniformIntRangeOp}, env, trace, state::LazyEnumeratorEvalState)
    bw_worlds = traced_compile_inner(expr.args[1], env, trace, state, 0)
    return bind_monad(bw_worlds, trace, state) do bw, tr1
        lo_worlds = traced_compile_inner(expr.args[2], env, tr1, state, 1)
        bind_monad(lo_worlds, tr1, state) do lo, tr2
            hi_worlds = traced_compile_inner(expr.args[3], env, tr2, state, 2)
            bind_monad(hi_worlds, tr2, state) do hi, tr3
                width = bw.value
                start = lo.value
                stop = hi.value
                @assert start isa Int && stop isa Int "uniform_int_range expects native Int bounds"
                @assert width isa Int "uniform_int_range expects native Int bitwidth"
                @assert stop >= start "uniform_int_range upper bound must be >= lower bound"
                function encode_range(lo_val, hi_val, tr_acc, depth_idx)
                    if lo_val == hi_val
                        bools = digits(Bool, lo_val, base = 2, pad = width)
                        return [(IntDist(bools), tr_acc)]
                    end
                    mid = lo_val + (hi_val - lo_val) ÷ 2
                    lower_size = mid - lo_val + 1
                    upper_size = hi_val - mid
                    p = lower_size / (lower_size + upper_size)
                    push!(state.callstack, depth_idx)
                    addr = current_address(state, p)
                    pop!(state.callstack)

                    choice = get_choice(tr_acc, addr, state)
                    if choice !== nothing
                        return choice.val ?
                            encode_range(lo_val, mid, tr_acc, depth_idx + 1) :
                            encode_range(mid + 1, hi_val, tr_acc, depth_idx + 1)
                    else
                        ttrace = extend_trace(tr_acc, Choice(addr, true, log(p)), state)
                        ftrace = extend_trace(tr_acc, Choice(addr, false, log1p(-p)), state)
                        return vcat(
                            encode_range(lo_val, mid, ttrace, depth_idx + 1),
                            encode_range(mid + 1, hi_val, ftrace, depth_idx + 1),
                        )
                    end
                end

                return encode_range(start, stop, tr3, 0)
            end
        end
    end
end

function compile_inner(expr::PExpr{IntDistEqOp}, env, trace, state::LazyEnumeratorEvalState)
    bind_monad(traced_compile_inner(expr.args[1], env, trace, state, 0), trace, state) do first_int_dist, trace1
        bind_monad(traced_compile_inner(expr.args[2], env, trace1, state, 1), trace1, state) do second_int_dist, trace2
            @assert length(first_int_dist.bits) == length(second_int_dist.bits)
            are_equal = all(first_int_dist.bits[i] == second_int_dist.bits[i] for i in eachindex(first_int_dist.bits))
            return pure_monad(are_equal ? Pluck.TRUE_VALUE : Pluck.FALSE_VALUE, trace2, state)
        end
    end
end
