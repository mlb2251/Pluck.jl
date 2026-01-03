function compile_inner(expr::PExpr{LookupOp}, env, path_condition, state)
    bind_compile(expr.args[1], env, path_condition, state, 0) do name, path_condition
        @assert name isa NativeValue{Symbol} "LookupOp: NativeValue{Symbol} expected, got $(name) :: $(typeof(name)) in $expr"
        return traced_compile_inner(Pluck.lookup(name.value).expr, env, path_condition, state, 1)
    end
end

function compile_inner(expr::PExpr{PBoolOp}, env, path_condition, state)
    cond = traced_compile_inner(expr.args[1], env, path_condition, state, 0)

    p_true = -Inf
    p_false = -Inf

    @assert length(cond[1]) <= 2 "should only be true or false, at most one of each"
    for (world, guard) in cond[1]
        if world.constructor == :True
            p_true = logaddexp(p_true, log(bdd_wmc(guard)))
        elseif world.constructor == :False
            p_false = logaddexp(p_false, log(bdd_wmc(guard)))
        else
            error("PBoolOp: condition must be a boolean, got $(world)")
        end
    end

    logtotal = logaddexp(p_true, p_false)

    p_true_thunk = make_thunk(ConstNative(exp(p_true - logtotal))(), Pluck.EMPTY_ENV, 1, state)
    true_thunk = make_thunk(Construct(:True)(), Pluck.EMPTY_ENV, 2, state)
    false_thunk = make_thunk(Construct(:False)(), Pluck.EMPTY_ENV, 3, state)
    bind_monad(cond, path_condition, state) do cond, path_condition
        if cond.constructor == :True
            return pure_monad(Value(:PBool, Any[p_true_thunk, true_thunk]), path_condition, state)
        elseif cond.constructor == :False
            return pure_monad(Value(:PBool, Any[p_true_thunk, false_thunk]), path_condition, state)
        else
            error("PBoolOp: condition must be a boolean, got $(cond)")
        end
    end
end

function compile_inner(expr::PExpr{PrintOp}, env, path_condition, state)
    val = traced_compile_inner(expr.args[1], env, path_condition, state, 0)
    return val
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