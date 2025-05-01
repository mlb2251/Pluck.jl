
function compile_inner(expr::PExpr{App}, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    fs = traced_compile_inner(expr.args[1], env, trace, state, :app_f)

    if state.strict
        # in strict semantics its safe to evaluate xs independently of f instead of nesting
        # it within the bind call.
        xs = traced_compile_inner(expr.args[2], env, Trace(), state, :app_x)
        results = []
        for (f, ftrace) in fs
            for (x, xtrace) in xs
                state.hit_limit && return []
                new_env = copy(f.env)
                pushfirst!(new_env, x)
                new_trace = cat_trace(ftrace, xtrace)
                for result in traced_compile_inner(f.expr, new_env, new_trace, state, :app_closure)
                    push!(results, result)
                end
            end
        end
        return results
        # same thing but with bind:
        # return lazy_enumerator_bind(fs, state) do f, trace
        #     lazy_enumerator_bind(xs, state) do x, trace
        #         new_env = copy(f.env)
        #         pushfirst!(new_env, x)
        #         return traced_compile_inner(f.expr, new_env, trace, state, :app_closure)
        #     end
        # end
    end

    thunked_argument = LazyEnumeratorThunk(expr.args[2], env, state, :app_x)
    return lazy_enumerator_bind(fs, state) do f, trace
        new_env = copy(f.env)
        x = Pluck.var_is_free(f.expr, 1) ? thunked_argument : nothing
        pushfirst!(new_env, x)
        return traced_compile_inner(f.expr, new_env, trace, state, :app_closure)
    end
end

function compile_inner(expr::PExpr{Abs}, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    # A lambda term deterministically evaluates to a closure.
    return [(Closure(expr.args[1], env), trace)]
end

# function bind_recursive(args, state)
#     length(args) == 1 && return args[1]
#     lazy_enumerator_bind(args[1], state) do arg1, trace
#         bind_recursive(args[2:end], state)
#     end
# end
function compile_inner(expr::PExpr{Construct}, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    # Constructors deterministically evaluate to a WHNF value, with their arguments thunked.
    # Look up type of this constructor.
    # spt = Pluck.spt_of_constructor[expr.constructor]

    if state.strict
        options_of_arg = []
        for (i, arg) in enumerate(expr.args[2])
            push!(options_of_arg, traced_compile_inner(arg, env, Trace(), state, Symbol("$(expr.args[1]).arg$i")))
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

    # Create a thunk for each argument.
    thunked_arguments = [LazyEnumeratorThunk(arg, env, state, Symbol("$(expr.args[1]).arg$i")) for (i, arg) in enumerate(expr.args[2])] # TODO: use global args_syms to avoid runtime cost of Symbol?
    # Return the constructor and its arguments.
    return [(Value(expr.args[1], thunked_arguments), trace)]
end

function compile_inner(expr::PExpr{ConstNative}, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    return [(expr.args[1], trace)]
end

function compile_inner(expr::PExpr{CaseOf}, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    scrutinee_values = traced_compile_inner(expr.args[1], env, trace, state, :case_scrutinee)
    lazy_enumerator_bind(scrutinee_values, state) do scrutinee, trace
        idx = findfirst(c -> c[1] == scrutinee.constructor, expr.args[2])
        if !isnothing(idx)
            case_expr = expr.args[2][idx][2]
            num_args = length(args_of_constructor[scrutinee.constructor])
            if num_args == 0
                return traced_compile_inner(case_expr, env, trace, state, scrutinee.constructor)
            else
                for _ = 1:num_args
                    @assert case_expr isa PExpr{Abs} "case expression branch for constructor $(scrutinee.constructor) must have as many lambdas as the constructor has arguments ($(num_args) arguments)"
                    case_expr = case_expr.args[1]
                end
                new_env = vcat(reverse(scrutinee.args), env)
                return traced_compile_inner(case_expr, new_env, trace, state, scrutinee.constructor)
            end
        else
            return []
        end
    end
end

function compile_inner(expr::PExpr{Y}, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    @assert expr.args[1] isa PExpr{Abs} && expr.args[1].args[1] isa PExpr{Abs} "y-combinator must be applied to a double-lambda"
 
    closure = Pluck.make_self_loop(expr.args[1].args[1].args[1], env)

    # set up a closure with a circular reference
    return [(closure, trace)]
end

function compile_inner(expr::PExpr{FlipOp}, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    ps = traced_compile_inner(expr.args[1], env, trace, state, :flip_arg)
    lazy_enumerator_bind(ps, state) do p, trace
        if isapprox(p, 0.0)
            return [(Pluck.FALSE_VALUE, trace)]
        elseif isapprox(p, 1.0)
            return [(Pluck.TRUE_VALUE, trace)]
        else
            addr = lazy_enumerator_make_address(state)

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

function compile_inner(expr::PExpr{GetConstructorOp}, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    lazy_enumerator_bind(traced_compile_inner(expr.args[1], env, trace, state, :get_constructor_arg), state) do arg, trace
        return [(NativeValue(arg.constructor), trace)]
    end
end


function compile_inner(expr::PExpr{NativeEqOp}, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)

    # Evaluate both arguments.  
    first_arg_results = traced_compile_inner(expr.args[1], env, trace, state, :constructor_eq_arg1)

    if state.strict
        # in strict semantics its safe to evaluate second argument independently of first
        # instead of nesting it within the bind call.   
        second_arg_results = traced_compile_inner(expr.args[2], env, trace, state, :constructor_eq_arg2)
        return lazy_enumerator_bind(first_arg_results, state) do arg1, trace
            return lazy_enumerator_bind(second_arg_results, state) do arg2, trace
                if arg1.value == arg2.value
                    return [(Pluck.TRUE_VALUE, trace)]
                else
                    return [(Pluck.FALSE_VALUE, trace)]
                end
            end
        end
    end

    lazy_enumerator_bind(first_arg_results, state) do arg1, trace
        second_arg_results = traced_compile_inner(expr.args[2], env, trace, state, :constructor_eq_arg2)
        lazy_enumerator_bind(second_arg_results, state) do arg2, trace
            if arg1.value == arg2.value
                return [(Pluck.TRUE_VALUE, trace)]
            else
                return [(Pluck.FALSE_VALUE, trace)]
            end
        end
    end
end

function compile_inner(expr::PExpr{Var}, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    # Look up the variable in the environment.
    if expr.args[1] > length(env)
        @warn "Variable $expr not found in environment; shaving off probability."
        return []
    end

    v = env[expr.args[1]]
    if v isa LazyEnumeratorThunk
        return evaluate(v, trace, state)
    else
        return [(v, trace)]
    end
end

function compile_inner(expr::PExpr{Defined}, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    # Execute Defined with a blanked out environment.
    return traced_compile_inner(lookup(expr.args[1]).expr, Pluck.EMPTY_ENV, trace, state, expr.args[1])
end