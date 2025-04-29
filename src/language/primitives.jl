export FlipOp, ConstructorEqOp, MkIntOp, IntDistEqOp, GetArgsOp, PBoolOp, GetConstructorOp

const primop_of_name::Dict{String, Type} = Dict()
const name_of_primop::Dict{Type, String} = Dict()
const arity_of_primop::Dict{Type, Int} = Dict()

function define_prim!(name::String, op::Type{T}, arity::Int) where T <: Primitive
    primop_of_name[name] = op
    name_of_primop[op] = name
    arity_of_primop[op] = arity
    nothing
end

function has_prim(name::AbstractString)
    haskey(primop_of_name, name)
end

function lookup_prim(name::AbstractString)
    primop_of_name[name]
end

function prim_str(::T) where T <: Primitive
    name_of_primop[T]
end

function prim_arity(::Type{T}) where T <: Primitive
    arity_of_primop[T]
end

Base.show(io::IO, e::T) where T <: Primitive = print(io, prim_str(e))
Base.:(==)(::Primitive, ::Primitive) = true


struct FlipOp <: Primitive end
define_prim!("flip", FlipOp, 1)

struct FlipOpDual <: Primitive end
define_prim!("flipd", FlipOpDual, 1)

struct ConstructorEqOp <: Primitive end
define_prim!("constructors_equal", ConstructorEqOp, 2)

struct GetArgsOp <: Primitive end
define_prim!("get_args", GetArgsOp, 1)

struct GetConstructorOp <: Primitive end
define_prim!("get_constructor", GetConstructorOp, 1)

struct PBoolOp <: Primitive end
define_prim!("pbool", PBoolOp, 1)

struct MkIntOp <: Primitive end
define_prim!("mk_int", MkIntOp, 2)

struct IntDistEqOp <: Primitive end
define_prim!("int_dist_eq", IntDistEqOp, 2)

