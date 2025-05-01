


function compile_inner(expr::PExpr{FlipOp}, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    ps = traced_compile_inner(expr.args[1], env, trace, state, 0)
    bind_monad(ps, trace, state) do p, trace
        p = p.value
        if isapprox(p, 0.0)
            return [(Pluck.FALSE_VALUE, trace)]
        elseif isapprox(p, 1.0)
            return [(Pluck.TRUE_VALUE, trace)]
        else
            addr = make_address(state)

            # check if we already have this choice in the trace
            choice = get_choice(trace, addr, state)
            if choice !== nothing
                return [(choice.val, trace)]
            end


            trace_true = extend_trace(trace, Choice(addr, Pluck.TRUE_VALUE, log(p)), state)
            trace_false = extend_trace(trace, Choice(addr, Pluck.FALSE_VALUE, log1p(-p)), state)
            return [(Pluck.TRUE_VALUE, trace_true), (Pluck.FALSE_VALUE, trace_false)]
        end
    end
end


#####################
# Eager compilation #
#####################


function compile_inner(expr::PExpr{App}, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState{EagerMode})
    # in strict semantics its safe to evaluate xs independently of f instead of nesting
    # it within the bind call.
    fs = traced_compile_inner(expr.args[1], env, trace, state, 0)
    xs = traced_compile_inner(expr.args[2], env, Trace(), state, 1)
    results = []
    for (f, ftrace) in fs
        for (x, xtrace) in xs
            state.hit_limit && return []
            new_env = copy(f.env)
            pushfirst!(new_env, x)
            new_trace = cat_trace(ftrace, xtrace)
            for result in traced_compile_inner(f.expr, new_env, new_trace, state, 2)
                push!(results, result)
            end
        end
    end
    return results
end

function compile_inner(expr::PExpr{Construct}, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState{EagerMode})
    # in strict semantics its safe to evaluate all arguments independently of each other.
    options_of_arg = []
    for (i, arg) in enumerate(expr.args[2])
        push!(options_of_arg, traced_compile_inner(arg, env, Trace(), state, i))
    end
    results = []
    for args in Iterators.product(options_of_arg...)
        if check_time_limit(state)
            state.hit_limit = true
            return []
        end
        new_trace = trace
        new_args = []
        for (arg, arg_trace) in args
            new_trace = cat_trace(new_trace, arg_trace)
            push!(new_args, arg)
        end
        push!(results, (Value(expr.args[1], new_args), new_trace))
    end
    return results
end

function compile_inner(expr::PExpr{NativeEqOp}, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState{EagerMode})
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