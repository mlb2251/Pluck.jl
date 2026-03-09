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
