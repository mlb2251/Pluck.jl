
# result of evaluating a lambda. Takes 1 argument.
mutable struct Closure <: AbstractValue
    expr::PExpr
    env::Vector{Any}
end

function Base.:(==)(x::Closure, y::Closure)
    x.expr == y.expr || return false
    is_self_loop(x) && is_self_loop(y) && return @views x.env[2:end] == y.env[2:end]
    x.env == y.env
end
function Base.hash(x::Closure, h::UInt)
    h = hash(x.expr, h)
    h = hash(length(x.env), h) # bleh having trouble stopping the self loops
    return h
end
function Base.show(io::IO, c::Closure)
    print(io, "Closure((λ ", c.expr, "), env=[#arg")
    for v in c.env
        if v === c
            print(io, ", [recursive reference to this closure]")
        else
            print(io, ", ", v)
        end
    end
    print(io, "]")
end

function make_self_loop(body, env)
    new_env = copy(env)
    pushfirst!(new_env, missing) # placeholder for the self-reference
    closure = Closure(body, new_env)
    closure.env[1] = closure # overwrite the Missing with the closure itself
    closure
end

is_self_loop(x::Closure) = !isempty(x.env) && x.env[1] === x

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