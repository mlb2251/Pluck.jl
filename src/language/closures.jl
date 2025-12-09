
# result of evaluating a lambda. Takes 1 argument.
mutable struct Closure <: AbstractValue
    expr::Union{PExpr, Thunk}
    env::Env
    name::Symbol
    origin::PExpr # debug / stacktrace info
end

function Base.:(==)(x::Closure, y::Closure)
    x.name == y.name || return false
    x.expr == y.expr || return false
    is_self_loop(x) && is_self_loop(y) && return tailenv(x.env) == tailenv(y.env)
    x.env == y.env
end
function Base.hash(x::Closure, h::UInt)
    h = hash(x.expr, h)
    h = hash(x.name, h)
    h = hash(length(x.env), h) # bleh having trouble stopping the self loops
    return h
end
function Base.show(io::IO, c::Closure)
    print(io, "(Closure from $(c.origin) name=$(c.name) body=$(c.expr))")
end

function make_self_loop(body, env, recname, nonrecname, origin)
    new_env = EnvCons(recname, missing, env)
    closure = Closure(body, new_env, nonrecname, origin)
    new_env.val = closure # overwrite the Missing with the closure itself
    closure
end

is_self_loop(x::Closure) = !isempty(x.env) && fst(x.env) === x

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