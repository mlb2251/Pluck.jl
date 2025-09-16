
"""
Convert a Value of type `pexpr` to a PExpr.
"""
function pexpr_from_value(x::Value)
    if x.constructor == :App
        f, x = x.args
        return App()(pexpr_from_value(f), pexpr_from_value(x))
    elseif x.constructor == :Defined
        return Defined(x.args[1].value)()
    elseif x.constructor == :Var
        return Var(x.args[1].value)()
    elseif x.constructor == :Abs
        return Abs(x.args[1].value)(pexpr_from_value(x.args[2]))
    else
        return Construct(x.constructor)([pexpr_from_value(arg) for arg in x.args]...)
    end
end

"""
Convert a PExpr to a Value of type `pexpr`.
"""
value_from_pexpr(e::PExpr{App}) = Value(:App, [value_from_pexpr(e.args[1]), value_from_pexpr(e.args[2])])
value_from_pexpr(e::PExpr{Defined}) = Value(:Defined, [NativeValue(e.head.name)])
value_from_pexpr(e::PExpr{Var}) = Value(:Var, [NativeValue(e.head.name)])
value_from_pexpr(e::PExpr{Abs}) = Value(:Abs, [NativeValue(e.head.var), value_from_pexpr(e.args[1])])
value_from_pexpr(e::PExpr{Construct}) = Value(e.head.constructor, [value_from_pexpr(arg) for arg in e.args])


