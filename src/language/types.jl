
abstract type PType end

struct BaseType <: PType
    name::Symbol
end
Base.:(==)(x::BaseType, y::BaseType) = x.name === y.name

struct Arrow <: PType
    arg_types::Vector{PType}
    return_type::PType

    Arrow(arg_types, return_type) = new(arg_types, return_type)
    # uncurry x -> (Y -> z) to (x,y) -> z
    Arrow(arg_types, return_type::Arrow) =
        new(vcat(arg_types, return_type.arg_types), return_type.return_type)
end
Base.:(==)(x::Arrow, y::Arrow) = x.return_type === y.return_type && all(x.arg_types .== y.arg_types)

mutable struct SumProductType
    name::Symbol
    constructors::Dict{Symbol,Vector{Symbol}}
end
Base.:(==)(x::SumProductType, y::SumProductType) = x.name === y.name

const spt_of_constructor = Dict{Symbol,SumProductType}()
const type_of_spt = Dict{Symbol,PType}()

function define_type!(name::Symbol, constructors::Dict{Symbol,Vector{Symbol}})
    spt = SumProductType(name, constructors)
    for constructor in keys(constructors)
        spt_of_constructor[constructor] = spt
    end
    # For backward compatibility, special-case nat to actually have name int
    if name === :nat
        type_of_spt[name] = BaseType(:int)
    else
        type_of_spt[name] = BaseType(name)
    end
    return spt
end

define_type!(:nat, Dict(:S => Symbol[:nat], :O => Symbol[]))
define_type!(:list, Dict(:Nil => Symbol[], :Cons => Symbol[:nat, :list]))
define_type!(:snoclist, Dict(:SNil => Symbol[], :Snoc => Symbol[:snoclist, :nat]))
define_type!(:bool, Dict(:True => Symbol[], :False => Symbol[]))
define_type!(:unit, Dict(:Unit => Symbol[]))

function args_of_constructor(name::Symbol)
    spt_of_constructor[name].constructors[name]
end



num_args(::BaseType) = 0
num_args(t::Arrow) = length(t.arg_types)

return_type(t::BaseType) = t
return_type(t::Arrow) = t.return_type

arg_types(::BaseType) = PType[]
arg_types(t::Arrow) = t.arg_types

Base.show(io::IO, t::BaseType) = print(io, t.name)
Base.show(io::IO, t::Arrow) = print(io, "(", join(t.arg_types, " -> "), " -> ", t.return_type, ")")

Base.parse(::Type{PType}, s::String) = parse_type(s)
parse_type(s::String) = parse_type(tokenize(s))
parse_type(s::SubString{String}) = parse_type(tokenize(s))
function parse_type(tokens)
    """
    Parse a type from a vector of tokens.
    int => BaseType(:int)
    ((int)) => BaseType(:int)
    foo => BaseType(:foo)
    x -> y -> z => Arrow([BaseType(:x), BaseType(:y)], BaseType(:z))
    # currying gets flattened away:
    x -> (Y -> z) => Arrow([BaseType(:x), BaseType(:y)], BaseType(:z))
    # however functions in an argument are of course preserved:
    (x -> y) -> z => Arrow([Arrow([BaseType(:x)], BaseType(:y))], BaseType(:z))
    """

    isempty(tokens) && error("unexpected end of input")
    types = PType[]
    connective = nothing
    while true
        token = tokens[1]
        if token == "("
            # parse the contents of these parens as a type
            end_idx = find_closeparn(tokens)
            push!(types, parse_type(tokens[2:end_idx-1]))
            tokens = tokens[end_idx+1:end]
        else
            # parse a base type
            @assert Meta.isidentifier(token) "expected a type name, got $(token)"
            push!(types, BaseType(Symbol(token)))
            tokens = tokens[2:end]
        end
        isempty(tokens) && break
        if tokens[1] == "->"
            @assert connective !== :constructor "unexpected mixture of arrows and type constructors - add more parentheses"
            connective = :arrow
            tokens = tokens[2:end]
        else
            @assert connective != :arrow "unexpected mixture of arrows and type constructors - add more parentheses"
            connective = :constructor
        end

    end

    # now we have a list of types, we can build the arrow type
    if connective === nothing
        @assert length(types) == 1
        return types[1]
    elseif connective === :arrow
        return Arrow(types[1:end-1], types[end])
    end
    error("unreachable")
end

function find_closeparn(tokens)::Int
    """
    Find the index of the matching ")" for the "(" at index 1.
    """
    @assert tokens[1] == "("
    depth = 0
    i = 1
    for (i, token) in enumerate(tokens)
        if token == "("
            depth += 1
        elseif token == ")"
            depth -= 1
            depth == 0 && return i
        end
    end
    error("unmatched parenthesis at start of $(join(tokens))")
end
