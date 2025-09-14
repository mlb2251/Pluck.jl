export pluck_list, StateVars, Value, get_true_result, Thunk, EnvCons, EnvNil, from_value
using Printf

abstract type Env end
@auto_hash_equals mutable struct EnvCons <: Env
    var::Symbol
    val::Any
    tail::Env
end
@auto_hash_equals struct EnvNil <: Env end

getenv(env::EnvCons, var::Symbol) = env.var === var ? env.val : getenv(env.tail, var)
getenv(env::EnvNil, var::Symbol) = error("Variable $var not found in environment")

tailenv(env::EnvCons) = env.tail
tailenv(env::EnvNil) = error("Empty environment has no tail")

Base.isempty(env::EnvNil) = true
Base.isempty(env::EnvCons) = false

fst(env::EnvCons) = env.val
fst(env::EnvNil) = error("Empty environment has no first variable")

Base.length(env::EnvNil) = 0
Base.length(env::EnvCons) = 1 + length(env.tail)

parse_env(env::EnvNil) = []
parse_env(env::EnvCons) = [string(env.var); parse_env(env.tail)]

# function env_of_list(xs)
#     env = EnvNil()
#     for x in reverse(xs)
#         env = EnvCons(x, env)
#     end
#     return env
# end



abstract type AbstractValue end
abstract type Thunk end

Base.:(==)(x::AbstractValue, y::Any) = error("Cannot compare Value with $(typeof(y))")
Base.:(==)(x::Any, y::AbstractValue) = error("Cannot compare $(typeof(x)) with Value")

mutable struct NativeValue{T} <: AbstractValue
    value::T
end
Base.:(==)(x::NativeValue{T}, y::NativeValue{U}) where {T, U} = T == U && x.value == y.value
Base.hash(x::NativeValue{T}, h::UInt) where T = hash(T, hash(x.value, h))
Base.show(io::IO, x::NativeValue{T}) where T = print(io, x.value)
Base.show(io::IO, x::NativeValue{Symbol}) = print(io, "'", x.value)

mutable struct Value <: AbstractValue
    constructor::Symbol
    args::Vector{Any}
end
Value(constructor::Symbol) = Value(constructor, [])

Base.:(==)(x::Value, y::Value) = x.constructor === y.constructor && x.args == y.args
Base.hash(x::Value, h::UInt) = hash(x.constructor, hash(x.args, h))

TRUE_VALUE::Value = Value(:True)
FALSE_VALUE::Value = Value(:False)


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

"""
    from_value(x::Value)

Convert a Value to a native Julia value. Returns flag true is value
is fully concrete and doesn't have any thunks
"""
from_value(x::Any) = x, false
from_value(x::AbstractValue) = x, true

function from_value(x::Value)
    converted_args = []
    concrete = true
    for arg in x.args
        arg, arg_concrete = from_value(arg)
        push!(converted_args, arg)
        concrete &= arg_concrete
    end

    base_val =
    # if x.constructor === :True
    #     true
    # elseif x.constructor === :False
    #     false
    # # elseif x.constructor === :Unit
    #     nothing
    if x.constructor == :O
        0
    elseif x.constructor == :S
        concrete ? 1 + converted_args[1] : x
    elseif x.constructor == :Nil
        Any[]
    elseif x.constructor == :Cons
        Any[[converted_args[1]]; converted_args[2]]
    elseif x.constructor == :Pair
        converted_args[1], converted_args[2]
    else
        x
    end
    return base_val, concrete
end


function rawstring(x::Value)
    s = "(" * string(x.constructor)
    for arg in x.args
        s *= " "
        s *= rawstring(arg)
    end
    s *= ")"
    return s
end
rawstring(x::Any) = string(x)

function Base.show(io::IO, x::Value)
    return print(io, rawstring(x))
    if x.constructor == :Cons || x.constructor == :Nil
        print(io, "[")
        while x isa Value && x.constructor == :Cons
            head, tail = x.args
            print(io, head)
            if tail isa Value && tail.constructor == :Cons
                print(io, ", ")
            end
            x = tail
        end
        print(io, "]")
    elseif x.constructor === :Prob
        prob, constructor, args = x.args
        prob = prob.value # NativeValue{Float64} -> Float64
        args, _ = from_value(args) # Value -> Vector{Any}
        if prob ≈ 1.0
            print(io, "(", constructor)
        else
            print(io, "(", constructor, "{", @sprintf("%.2f", prob), "}")
        end
        for arg in args
            print(io, " ")
            show_value_inner(io, arg)
        end
        print(io, ")")
    elseif x.constructor == :App
        f, x = x.args
        args = [x]
        while f isa Value && f.constructor == :App
            f, x = f.args
            push!(args, x)
        end
        if length(args) == 1 && args[1] isa Value && args[1].constructor == :Unit
            print(io, "(", f, ")") # (f (Unit)) is written as (f)
            return
        end
        print(io, "(", f)
        for arg in reverse(args)
            print(io, " ", arg)
        end
        print(io, ")")
    elseif x.constructor == :Defined
        print(io, x.args[1])
    else
        print(io, "(", x.constructor)
        for arg in x.args
            print(io, " ", arg)
        end
        print(io, ")")
    end
end

show_value_inner(io::IO, x::Any) = print(io, x)
function show_value_inner(io::IO, x::Vector{Any})
    print(io, "[")
    for i in 1:length(x)
        show_value_inner(io, x[i])
        i != length(x) && print(io, ", ")
    end
    print(io, "]")
end

function show_value_inner(io::IO, x::Tuple)
    print(io, "(")
    for i in 1:length(x)
        show_value_inner(io, x[i])
        i != length(x) && print(io, ", ")
    end
    length(x) == 1 && print(io, ", ")
    print(io, ")")
end


function JSON.lower(x::Value)
    # v, concrete = from_value(x)
    # !(v isa Value) && return string(v)
    # return [x.constructor, x.args...]
    OrderedDict("type" => "Value", "constructor" => x.constructor, "args" => x.args)
end

function JSON.lower(x::NativeValue)
    OrderedDict("type" => "NativeValue", "value" => x.value)
end


Base.@kwdef mutable struct StateVars
    fuel::Int = 0 # 0 means infinite
end

function list_to_value(xs::AbstractVector)
    res = Value(:Nil)
    for x in reverse(xs)
        res = Value(:Cons, [x, res])
    end
    return res
end