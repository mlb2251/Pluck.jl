export pluck_list

abstract type AbstractValue end

Base.:(==)(x::AbstractValue, y::Any) = error("Cannot compare Value with $(typeof(y))")
Base.:(==)(x::Any, y::AbstractValue) = error("Cannot compare $(typeof(x)) with Value")

struct FloatValue <: AbstractValue
    value::Float64
end
Base.:(==)(x::FloatValue, y::FloatValue) = x.value == y.value
Base.hash(x::FloatValue, h::UInt) = hash(x.value, h)
Base.show(io::IO, x::FloatValue) = print(io, x.value)

struct UIntValue <: AbstractValue
    value::UInt64
end
Base.:(==)(x::UIntValue, y::UIntValue) = x.value == y.value
Base.hash(x::UIntValue, h::UInt) = hash(x.value, h)
Base.show(io::IO, x::UIntValue) = print(io, x.value)

struct Value <: AbstractValue
    constructor::Symbol
    args::Vector{Any}
end
Value(constructor) = Value(constructor, [])
Value(constructor, args...) = Value(constructor, collect(args))

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

    base_val = if x.constructor === :True
        true
    elseif x.constructor === :False
        false
    elseif x.constructor === :Unit
        ()
    elseif x.constructor == :O
        0
    elseif x.constructor == :S
        1 + converted_args[1]
    elseif x.constructor == :Nil || x.constructor == :SNil
        []
    elseif x.constructor == :Cons
        [converted_args[1]; converted_args[2]]
    else
        x
    end
    return base_val, concrete
end

function Base.show(io::IO, x::Value)
    x.constructor === :Nil && return print(io, "[]") # prettier than "Any[]"
    v, concrete = from_value(x)
    show_value_inner(io, v)
end

function show_value_inner(io::IO, x::Any)
    print(io, x)
end

function show_value_inner(io::IO, x::Value)
    print(io, "(", x.constructor)
    for arg in x.args
        print(io, " ")
        print(io, arg)
    end
    print(io, ")")
end

function JSON.lower(x::Value)
    v = from_value(x)
    !(v isa Value) && return string(v)
    Dict("type" => "Value", "constructor" => x.constructor, "args" => x.args)
end
