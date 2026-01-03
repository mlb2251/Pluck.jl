function compile_inner(expr::PExpr{App}, env, path_condition, state)
    # println("compile_inner App: $expr with args $(expr.args[2])")
    thunked_argument = make_thunk(expr.args[2], env, 1, state)

    return bind_compile(expr.args[1], env, path_condition, state, 0) do f, path_condition
        f isa Closure || pluck_error(state, "App must be applied to a Closure, got $(f) :: $(typeof(f)) at $(expr)")
        new_env = EnvCons(f.name, thunked_argument, f.env)
        with_stacktrace(state, f.origin) do
            res = traced_compile_inner(f.expr, new_env, path_condition, state, 2)
            mutate_values(res) do val
                if val isa Closure
                    val.origin = f.origin
                end
            end
        end
    end
end

function mutate_values(f::F, compile_result) where F <: Function
    worlds, _ = compile_result
    for (value, _) in worlds
        f(value)
    end
    return compile_result
end


function compile_inner(expr::PExpr{Abs}, env, path_condition, state)
    # A lambda term deterministically evaluates to a closure.
    with_stacktrace(state, expr) do
        pure_monad(Closure(expr.args[1], env, expr.head.var, expr), path_condition, state)
    end
end

function compile_inner(expr::PExpr{Construct}, env, path_condition, state)
    # Constructors deterministically evaluate to a WHNF value, with their arguments thunked.
    # Create a thunk for each argument.
    # println("compile_inner Construct: $expr with args $(expr.args[2])")
    thunked_arguments = [make_thunk(arg, env, i, state) for (i, arg) in enumerate(expr.args)]
    # Return the constructor and its arguments.
    return pure_monad(Value(expr.head.constructor, thunked_arguments), path_condition, state)
end

function compile_inner(expr::PExpr{CaseOf}, env, path_condition, state)
    # caseof_type = type_of_constructor[first(keys(expr.cases))]
    bind_compile(getscrutinee(expr), env, path_condition, state, 0) do scrutinee, path_condition
        # value_type = type_of_constructor[scrutinee.constructor]
        # if !isempty(expr.cases) && !(value_type == caseof_type)
        #     @warn "TypeError: Scrutinee constructor $(scrutinee.constructor) of type $value_type is not the same as the case statement type $caseof_type"
        # end

        scrutinee isa Value || pluck_error(state, "at $expr: scrutinee must a Value not a $(typeof(scrutinee))\nScrutinee: $scrutinee")

        idx = findfirst(g -> g.constructor == scrutinee.constructor, expr.head.branches)
        if isnothing(idx)
            # println("Scrutinee not in case expression: $(scrutinee) in $(expr)")
            # pluck_error(state, "Scrutinee not in case expression: $(scrutinee) in $(expr)")
            return program_error_worlds(state)
        end

        case_expr = getbranch(expr, idx)
        @assert length(scrutinee.args) == length(getguard(expr, idx).args) "wrorng number of arguments in caseof: guard is $(getguard(expr, idx))"

        # In each of the scrutinee arguments, filter out options that contradict the available information.
        for (arg, name) in zip(scrutinee.args, getguard(expr, idx).args)
            env = EnvCons(name, arg, env)
        end
        return traced_compile_inner(case_expr, env, path_condition, state, idx)
    end
end

function compile_inner(expr::PExpr{Var}, env, path_condition, state)

    v = getenv(env, expr.head.name)
    if v isa Thunk
        return evaluate(v, path_condition, state)
    end

    return pure_monad(v, path_condition, state)
end

function compile_inner(expr::PExpr{Defined}, env, path_condition, state)
    body = Pluck.lookup(expr.head.name).expr
    # Execute Defined with an empty environment.
    with_stacktrace(state, expr) do
        res = traced_compile_inner(body, Pluck.EMPTY_ENV, path_condition, state, 0)
        mutate_values(res) do val
            if val isa Closure
                val.origin = expr
            end
        end
    end
end

function compile_inner(expr::PExpr{Y}, env, path_condition, state)
    rec_lambda = expr.args[1] :: PExpr{Abs}
    arg_lambda = rec_lambda.args[1] :: PExpr{Abs}
    closure = make_self_loop(arg_lambda.args[1], env, rec_lambda.head.var, arg_lambda.head.var, expr)

    return pure_monad(closure, path_condition, state)
end

function compile_inner(expr::PExpr{ErrorOp}, env, path_condition, state)
    pluck_error(state, "ErrorOp: $expr")
end

"""
Given a Value, returns a Cons-list of its arguments.
"""
function compile_inner(expr::PExpr{GetArgsOp}, env, path_condition, state)
    bind_compile(expr.args[1], env, path_condition, state, 0) do val, path_condition
        res = Value(:Nil)
        for arg in reverse(val.args)
            res = Value(:Cons, [arg, res])
        end
        return pure_monad(res, path_condition, state)
    end
end

function compile_inner(expr::PExpr{GetConstructorOp}, env, path_condition, state)
    bind_compile(expr.args[1], env, path_condition, state, 0) do val, path_condition
        val isa Value || pluck_error(state, "getconstructor must be applied to a Value, not: $val :: $(typeof(val))")
        return pure_monad(NativeValue(val.constructor), path_condition, state)
    end
end
