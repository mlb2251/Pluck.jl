export pluck_list

# result of evaluating a lambda. Takes 1 argument.
mutable struct Closure
    expr::PExpr
    env::Vector{Any}
end

function make_self_loop(body, env)
    new_env = copy(env)
    pushfirst!(new_env, missing) # placeholder for the self-reference
    closure = Closure(body, new_env)
    closure.env[1] = closure # overwrite the Missing with the closure itself
    closure
end

is_self_loop(x::Closure) = !isempty(x.env) && x.env[1] === x

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

function JSON.lower(x::Closure)
    is_ycombinator = !isempty(x.env) && x.env[1] === x
    env =
        is_ycombinator ? vcat(["[recursive reference to this closure]"], x.env[2:end]) :
        x.env
    Dict(
        "type" => "Closure",
        "expr" => x.expr,
        "env" => [var_is_free(x.expr, i + 1) ? v : "unused" for (i, v) in enumerate(env)], # +1 bc of shifting when prepending the closure arg
    )
end

# A lazily evaluated expression. Takes zero arguments. May yield more than one
# actual value, so this is not itself a value – it's a construct that can only
# appear within an env or under a constructor, and will be enumerated or logprob'd 
# when pulled from the env or constructor as necessary.
# Currently not stateful: independent uses of a variable that points to the thunk,
# e.g., are not tied to take the same value.
struct Thunk
    expr::PExpr
    env::Vector{Any}
    callstack::Vector{Symbol} # if empty: not memoizing this expression.
    name::Symbol
    memoizing::Bool
    function Thunk(expr::PExpr, env::Vector, callstack, name, memoizing)
        # remove a layer of thunk if the expr is a var pointing to a thunk
        # (this helps caching and makes things less convoluted)
        if expr isa Var && env[expr.idx] isa Thunk
            return env[expr.idx]
        end
        new(expr, env, copy(callstack), name, memoizing)
    end
end

Base.:(==)(x::Thunk, y::Thunk) =
    x.expr == y.expr &&
    x.callstack == y.callstack &&
    x.env == y.env &&
    x.name == y.name &&
    x.memoizing == y.memoizing
# dont hash the env just its length for speed
Base.hash(x::Thunk, h::UInt) =
    hash(x.expr, hash(length(x.env), hash(x.callstack, hash(x.name, hash(x.memoizing, h)))))

JSON.lower(x::Thunk) = Dict(
    "type" => "Thunk",
    "expr" => x.expr,
    "env" => [var_is_free(x.expr, i) ? v : "unused" for (i, v) in enumerate(x.env)],
    "callstack" => x.callstack,
    "name" => x.name,
    "memoizing" => x.memoizing,
)

pluck_nat(n::Int) = foldr((_, acc) -> "(S " * acc * ")", 1:n; init = "(O)")

function pluck_list(l::AbstractVector)
    if isempty(l)
        return "(Nil)"
    else
        head = l[1]
        tail = pluck_list(l[2:end])
        return "(Cons $head $tail)"
    end
end

struct Value
    constructor::Symbol
    args::Vector{Any}
end
Value(constructor) = Value(constructor, [])
Value(constructor, args...) = Value(constructor, collect(args))
Base.hash(x::Value, h::UInt) = hash(x.constructor, hash(x.args, h))
Base.:(==)(x::Value, y::Value) = x.constructor === y.constructor && x.args == y.args
Base.:(==)(x::Value, y::Any) = error("Cannot compare Value with $(typeof(y))")
Base.:(==)(x::Any, y::Value) = error("Cannot compare $(typeof(x)) with Value")


function to_value(n::Int)
    @assert n >= 0
    n == 0 && return Value(:O)
    Value(:S, to_value(n - 1))
end

to_value(::Tuple{}) = Value(:Unit)
to_value(x::Bool) = x ? Value(:True) : Value(:False)
to_value(x::Value) = x

function to_value(xs::Vector)
    isempty(xs) && return Value(:Nil)
    return Value(:Cons, to_value(xs[1]), to_value(xs[2:end]))
end

TRUE_VALUE::Value = Value(:True)
FALSE_VALUE::Value = Value(:False)

from_value(x) = x
function from_value(x::Value)
    if x.constructor === :True
        return true
    elseif x.constructor === :False
        return false
    elseif x.constructor == :O
        return 0
    elseif x.constructor == :S
        (x.args[1] isa Thunk || x.args[1] isa LazyEnumeratorThunk || x.args[1] isa BDDThunk) && return x
        return 1 + from_value(x.args[1])
    elseif x.constructor == :Nil || x.constructor == :SNil
        return []
    elseif x.constructor == :Cons
        (x.args[1] isa Thunk || x.args[2] isa Thunk || x.args[1] isa BDDThunk || x.args[2] isa BDDThunk) && return x
        (x.args[1] isa Nothing || x.args[2] isa Nothing) && return nothing # aaack my temp fix for neg nats
        return [from_value(x.args[1]); from_value(x.args[2])]
    elseif x.constructor == :Snoc
        (x.args[1] isa Thunk || x.args[2] isa Thunk || x.args[1] isa BDDThunk || x.args[2] isa BDDThunk) && return x
        (x.args[1] isa Nothing || x.args[2] isa Nothing) && return nothing # aaack my temp fix for neg nats
        head_list = from_value(x.args[1])
        tail_elem = from_value(x.args[2])
        return vcat(head_list, [tail_elem])
    end
    return x
end

convert(::Type{Value}, x) = value(x)
function Base.show(io::IO, x::Value)
    (x.constructor === :Nil || x.constructor === :SNil) && return print(io, "[]") # prettier than "Any[]"
    v = from_value(x)
    if !(v isa Value)
        print(io, v)
    else
        print(io, "(", x.constructor)
        for arg in x.args
            print(io, " ")
            print(io, arg)
        end
        print(io, ")")
    end
end

function JSON.lower(x::Value)
    v = from_value(x)
    !(v isa Value) && return string(v)
    Dict("type" => "Value", "constructor" => x.constructor, "args" => x.args)
end


function string_repr(x::Value)
    res = "(" * string(x.constructor)
    for arg in x.args
        res *= " " * string_repr(arg)
    end
    return res * ")"
end

