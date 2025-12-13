function JSON.lower(x::Closure)
    env =
        is_self_loop(x) ? vcat(["[recursive reference to this closure]"], x.env[2:end]) :
        x.env
    Dict(
        "type" => "Closure",
        "expr" => x.expr,
        "env" => [var_is_free(x.expr, i + 1) ? v : "unused" for (i, v) in enumerate(env)], # +1 bc of shifting when prepending the closure arg
    )
end

JSON.lower(e::PExpr) = string(e)

function JSON.lower(x::Value)
    # v, concrete = from_value(x)
    # !(v isa Value) && return string(v)
    # return [x.constructor, x.args...]
    OrderedDict("type" => "Value", "constructor" => x.constructor, "args" => x.args)
end

function JSON.lower(x::NativeValue)
    OrderedDict("type" => "NativeValue", "value" => x.value)
end