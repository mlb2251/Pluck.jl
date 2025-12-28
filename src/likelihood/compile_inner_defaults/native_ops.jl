"""
Compile a unary native operation.
"""
function compile_native_unop(f::F, expr::PExpr{T}, env, path_condition, state) where {T <: Head, F <: Function}
    bind_compile(expr.args[1], env, path_condition, state, 0) do arg1, path_condition
        val = f(arg1.value)
        return pure_monad(NativeValue(val), path_condition, state)
    end
end

"""
Compile a binary native operation.
"""
function compile_native_binop(f::F, expr::PExpr{T}, env, path_condition, state) where {T <: Head, F <: Function}
    bind_compile(expr.args[1], env, path_condition, state, 0) do arg1, path_condition
        bind_compile(expr.args[2], env, path_condition, state, 1) do arg2, path_condition
            val = f(arg1.value, arg2.value)
            return pure_monad(NativeValue(val), path_condition, state)
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

function compile_inner(expr::PExpr{FDivOp}, env, path_condition, state)
    compile_native_binop(/, expr, env, path_condition, state)
end

function compile_inner(expr::PExpr{FMulOp}, env, path_condition, state)
    compile_native_binop(*, expr, env, path_condition, state)
end

function compile_inner(expr::PExpr{FAddOp}, env, path_condition, state)
    compile_native_binop(+, expr, env, path_condition, state)
end

function compile_inner(expr::PExpr{FSubOp}, env, path_condition, state)
    compile_native_binop(-, expr, env, path_condition, state)
end

function compile_inner(expr::PExpr{IsApproxOp}, env, path_condition, state)
    bind_compile(expr.args[1], env, path_condition, state, 0) do arg1, path_condition
        bind_compile(expr.args[2], env, path_condition, state, 1) do arg2, path_condition
            return pure_monad(isapprox(arg1.value, arg2.value) ? Pluck.TRUE_VALUE : Pluck.FALSE_VALUE, path_condition, state)
        end
    end
end