function compile_inner(expr::PExpr{App}, env, path_condition, state)
    # println("compile_inner App: $expr with args $(expr.args[2])")
    thunked_argument = make_thunk(expr.args[2], env, 1, state)

    return bind_compile(expr.args[1], env, path_condition, state, 0) do f, path_condition
        f isa Closure || pluck_error(state, "App must be applied to a Closure, got $(f) :: $(typeof(f)) at $(expr)")
        new_env = EnvCons(f.name, thunked_argument, f.env)
        with_stacktrace(state, f.origin) do
            res = traced_compile_inner(f.expr, new_env, path_condition, state, 2)
            mutate_values(res, state) do val
                if val isa Closure
                    val.origin = f.origin
                end
            end
        end
    end
end

function mutate_values(f::F, compile_result, state) where F <: Function
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

function compile_inner(expr::PExpr{If}, env, path_condition, state)
    bind_compile(expr.args[1], env, path_condition, state, 0) do cond, path_condition
        cond isa Value || pluck_error(state, "at $expr: cond must a Value not a $(typeof(cond))\nCond: $cond")
        if isgiven(cond) || iserror(cond)
            return pure_monad(cond, path_condition, state)
        end

        cond.constructor === :True || cond.constructor === :False || pluck_error(state, "at $expr: cond must be True or False not a $(cond.constructor)")

        strict_order_index = cond.constructor == :True ? 1 : 2
        branch_expr = cond.constructor == :True ? expr.args[2] : expr.args[3]
        return traced_compile_inner(branch_expr, env, path_condition, state, strict_order_index)
    end
end

function compile_inner(expr::PExpr{CaseOf}, env, path_condition, state)
    bind_compile(getscrutinee(expr), env, path_condition, state, 0) do scrutinee, path_condition
        scrutinee isa Value || pluck_error(state, "at $expr: scrutinee must a Value not a $(typeof(scrutinee))\nScrutinee: $scrutinee")

        if isgiven(scrutinee) || iserror(scrutinee)
            return pure_monad(scrutinee, path_condition, state)
        end

        idx = findfirst(g -> g.constructor == scrutinee.constructor, expr.head.branches)
        if isnothing(idx)
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
    body = Pluck.DEFINITIONS[expr.head.name].expr
    # Execute Defined with an empty environment.
    with_stacktrace(state, expr) do
        res = traced_compile_inner(body, Pluck.EMPTY_ENV, path_condition, state, 0)
        mutate_values(res, state) do val
            if val isa Closure
                val.origin = expr
            end
        end
    end
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

function compile_inner(expr::PExpr{AbstractTypeOp}, env, path_condition, state)
    bind_compile(expr.args[1], env, path_condition, state, 0) do val, path_condition
        if val isa Value
            return pure_monad(Value(:Value), path_condition, state)
        elseif val isa NativeValue
            inner_type = Symbol(typeof(val.value))
            return pure_monad(Value(:NativeValue, [NativeValue(inner_type)]), path_condition, state)
        elseif val isa Closure
            return pure_monad(Value(:Closure), path_condition, state)
        else
            error("AbstractTypeOp: expected Value, NativeValue, or Closure, got $(val) :: $(typeof(val)) in $expr")
        end
    end
end

function compile_inner(expr::PExpr{ConstNative}, env, path_condition, state)
    return pure_monad(NativeValue(expr.head.val), path_condition, state)
end

function compile_inner(expr::PExpr{NativeEqOp}, env, path_condition, state)
    bind_compile(expr.args[1], env, path_condition, state, 0) do arg1, path_condition
        bind_compile(expr.args[2], env, path_condition, state, 1) do arg2, path_condition
            return pure_monad(arg1.value == arg2.value ? Pluck.TRUE_VALUE : Pluck.FALSE_VALUE, path_condition, state)
        end
    end
end