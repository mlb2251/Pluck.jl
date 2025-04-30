export FlipOp, ConstructorEqOp, MkIntOp, IntDistEqOp, GetArgsOp, PBoolOp, GetConstructorOp, GetConfig

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

struct GetConfig <: Primitive end
define_prim!("get_config", GetConfig, 0)

struct MkIntOp <: Primitive end
define_prim!("mk_int", MkIntOp, 2)

struct IntDistEqOp <: Primitive end
define_prim!("int_dist_eq", IntDistEqOp, 2)

struct QuoteOp <: Primitive end
define_prim!("quote", QuoteOp, 1)

struct EvalOp <: Primitive end
define_prim!("eval", EvalOp, 1)

# function application
struct App <: Primitive end
define_prim!("app", App, 2)
App(f, x) = PrimOp(App(), Any[f, x])

function Base.show(io::IO, e::PrimOp{App})
    print(io, "(", get_func(e))
    for i ∈ 1:num_apps(e)
        print(io, " ", getarg(e, i))
    end
    print(io, ")")
end

# (app f x y) -> (app (app f x) y)
num_apps(e::PrimOp{App}) = 1 + num_apps(e.args[1])
get_func(e::PrimOp{App}) = get_func(e.args[1])
function getarg(e::PrimOp{App}, i)
    # for an app chain (app (app f x) y) we want x to be the 1st arg and y to be
    # the second arg.
    which_app = num_apps(e) - i + 1
    for _ ∈ 1:which_app-1
        e = e.args[1]
    end
    e.args[2]
end

# functional abstraction
struct Abs <: Primitive end
Abs(body, name) = PrimOp(Abs(), Any[body, name])

var_is_free(e::PrimOp{Abs}, var) = var_is_free(e.args[1], var + 1)
shortname(e::PrimOp{Abs}) = "λ" * string(e.args[2])
function Base.show(io::IO, e::PrimOp{Abs})
    print(io, "(λ", e.args[2])
    while e.args[1] isa Abs
        e = e.args[1]
        print(io, " ", e.args[2])
    end
    print(io, " -> ", e.args[1], ")")
end



