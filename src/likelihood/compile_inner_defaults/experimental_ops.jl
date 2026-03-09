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