export FlipOp, ConstructorEqOp, MkIntOp, IntDistEqOp

struct FlipOp <: RandomPrimitive end
struct ConstructorEqOp <: Primitive end
struct MkIntOp <: Primitive end
struct IntDistEqOp <: Primitive end

const primop_of_name::Dict{String, Type} = Dict()
const name_of_primop::Dict{Type, String} = Dict()
const arity_of_primop::Dict{Type, Int} = Dict()

function define_prim!(name::String, op::Type{T}, arity::Int) where T <: Primitive
    primop_of_name[name] = op
    name_of_primop[op] = name
    arity_of_primop[op] = arity
    nothing
end

function has_prim(name::String)
    haskey(primop_of_name, name)
end

function lookup_prim(name::String)
    primop_of_name[name]
end

function prim_str(::T) where T <: Primitive
    name_of_primop[T]
end

function prim_arity(::T) where T <: Primitive
    arity_of_primop[T]
end

define_prim!("flip", FlipOp, 1)
define_prim!("constructors_equal", ConstructorEqOp, 2)
define_prim!("mk_int", MkIntOp, 2)
define_prim!("int_dist_eq", IntDistEqOp, 2)

Base.show(io::IO, e::T) where T <: Primitive = print(io, prim_str(e))
Base.:(==)(::Primitive, ::Primitive) = true

prim_type(::FlipOp) = Arrow(PType[BaseType(:bool)], BaseType(:bool))
prim_type(::MkIntOp) = BaseType(:int)
prim_type(::IntDistEqOp) = tbool