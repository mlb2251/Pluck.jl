export pluck_list, StateVars, Value, get_true_result, Thunk
using Printf



abstract type AbstractValue end
abstract type Thunk end

Base.:(==)(x::AbstractValue, y::Any) = error("Cannot compare Value with $(typeof(y))")
Base.:(==)(x::Any, y::AbstractValue) = error("Cannot compare $(typeof(x)) with Value")

mutable struct NativeValue{T} <: AbstractValue
    value::T
end
Base.:(==)(x::NativeValue{T}, y::NativeValue{T}) where T = x.value == y.value
Base.hash(x::NativeValue{T}, h::UInt) where T = hash(x.value, h)
Base.show(io::IO, x::NativeValue{T}) where T = print(io, x.value)

# mutable struct PExprValue{H <: Head} <: AbstractValue
#     head::H
#     args::Vector{Any} # thunks that produce other PExprValues
# end
# Base.show(io::IO, x::PExprValue{T}) where T = print(io, PExpr(x.head, x.args))
# Base.:(==)(x::PExprValue, y::PExprValue) = x.head === y.head && x.args == y.args
# Base.hash(x::PExprValue, h::UInt) = hash(x.head, hash(x.args, h))

mutable struct Value <: AbstractValue
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
        concrete ? 1 + converted_args[1] : x
    elseif x.constructor == :Nil
        Any[]
    elseif x.constructor == :Cons
        Any[converted_args[1]; converted_args[2]]
    else
        x
    end
    return base_val, concrete
end

function Base.show(io::IO, x::Value)
    v, concrete = from_value(x)
    show_value_inner(io, v)
end

show_value_inner(io::IO, x::Any) = print(io, x)
function show_value_inner(io::IO, x::Vector{Any})
    print(io, "[")
    for i in 1:length(x)
        print(io, x[i])
        i != length(x) && print(io, ", ")
    end
    print(io, "]")
end

function show_value_inner(io::IO, x::Value)
    if x.constructor === :Prob
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
            print(io, arg)
        end
        print(io, ")")
        return
    end

    print(io, "(", x.constructor)
    for arg in x.args
        print(io, " ")
        print(io, arg)
    end
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
