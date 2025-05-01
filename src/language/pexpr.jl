export PExpr, Head, Var, App, Abs, Y, Defined, PExpr, CaseOf, Construct, FlipOp, NativeEqOp, MkIntOp, IntDistEqOp, GetArgsOp, PBoolOp, GetConstructorOp, GetConfig, ConstNative

import DataStructures: OrderedDict

abstract type Head end


Base.show(io::IO, e::T) where T <: Head = print(io, prim_str(e))
Base.:(==)(::T, ::T) where T <: Head = true

mutable struct PExpr{H <: Head}
    op::H
    args::Vector{Any}
end

(::Type{H})(args...) where H <: Head = PExpr{H}(H(), collect(Any, args))


# default PExpr methods
JSON.lower(e::PExpr) = string(e)
shortname(e::PExpr) = string(e.op)
function Base.show(io::IO, e::PExpr)
    print(io, "(", e.op)
    for arg in e.args
        print(io, " ", arg)
    end
    print(io, ")")
end
Base.copy(e::PExpr) = PExpr(e.op, [copy(arg) for arg in e.args])
Base.:(==)(a::PExpr, b::PExpr) = a.op == b.op && a.args == b.args
Base.hash(e::PExpr, h::UInt) = hash(e.op, hash(e.args, hash(:PExpr, h)))

##############
# Operations #
##############

# function application
struct App <: Head end

function Base.show(io::IO, e::PExpr{App})
    print(io, "(", get_func(e))
    for i ∈ 1:num_apps(e)
        print(io, " ", getarg(e, i))
    end
    print(io, ")")
end

# (app f x y) -> (app (app f x) y)
num_apps(e::PExpr) = 0
num_apps(e::PExpr{App}) = 1 + num_apps(e.args[1])
get_func(e::PExpr{App}) = get_func(e.args[1])
get_func(e::PExpr) = e
function getarg(e::PExpr{App}, i)
    # for an app chain (app (app f x) y) we want x to be the 1st arg and y to be
    # the second arg.
    which_app = num_apps(e) - i + 1
    for _ ∈ 1:which_app-1
        e = e.args[1]
    end
    e.args[2]
end

# functional abstraction
struct Abs <: Head end
# Abs(body, name) = PExpr(Abs(), Any[body, name])

shortname(e::PExpr{Abs}) = "λ" * string(e.args[2])
function Base.show(io::IO, e::PExpr{Abs})
    print(io, "(λ", e.args[2])
    while e.args[1] isa PExpr{Abs}
        e = e.args[1]
        print(io, " ", e.args[2])
    end
    print(io, " -> ", e.args[1], ")")
end


struct Var <: Head end
Var(idx::Int) = Var(idx, :noname)
Var(idx, name) = PExpr(Var(), Any[idx, name])
Base.show(io::IO, e::PExpr{Var}) =
    e.args[2] === :noname ? print(io, "#", e.args[1]) : print(io, e.args[2], "#", e.args[1])


struct Defined <: Head end
Defined(name) = PExpr(Defined(), Any[name])
shortname(e::PExpr{Defined}) = string(e.args[1])
Base.show(io::IO, e::PExpr{Defined}) = print(io, e.args[1])

struct ConstNative <: Head end
ConstNative(val) = PExpr(ConstNative(), Any[val])
shortname(e::PExpr{ConstNative}) = string(e.args[1])
function Base.show(io::IO, e::PExpr{ConstNative})
    if e.args[1] isa Int
        print(io, "@", e.args[1])
    else
        print(io, e.args[1])
    end
end


struct CaseOf <: Head end
CaseOf(scrutinee, cases) = PExpr(CaseOf(), Any[scrutinee, cases])
shortname(e::PExpr{CaseOf}) = "caseof"
function Base.show(io::IO, e::PExpr{CaseOf})
    print(io, "(case ", e.args[1], " of ")
    for (i, (constructor, case)) in enumerate(e.args[2])
        print(io, constructor, " => ", case)
        if i < length(e.args[2])
            print(io, " | ")
        end
    end
    print(io, ")")
end
Base.copy(e::PExpr{CaseOf}) = PExpr(CaseOf(), Any[copy(e.args[1]), OrderedDict(constructor => copy(e.args[2][constructor]) for constructor in keys(e.args[2]))])

struct Construct <: Head end
Construct(constructor, args) = PExpr(Construct(), Any[constructor, collect(args)])
Construct(constructor) = Construct(constructor, [])
shortname(e::PExpr{Construct}) = string(e.args[1])
function Base.show(io::IO, e::PExpr{Construct})
    as_const = maybe_const(e)
    if !isnothing(as_const)
        print(io, as_const)
        return
    end
    print(io, "(", e.args[1])
    for arg in e.args[2]
        print(io, " ", arg)
    end
    print(io, ")")
end
function maybe_const(e::PExpr{Construct})
    if e.args[1] === :O
        return 0
    elseif e.args[1] == :S
        inner = maybe_const(e.args[2][1])
        isnothing(inner) && return nothing
        return inner + 1
    end
    return nothing
end
maybe_const(e) = nothing
Base.copy(e::PExpr{Construct}) = PExpr(Construct(), Any[copy(e.args[1]), [copy(arg) for arg in e.args[2]]])


##############
# Simple Ops #
##############

const primop_of_name::Dict{String, Type} = Dict()
const name_of_primop::Dict{Type, String} = Dict()
const arity_of_primop::Dict{Type, Int} = Dict()

function define_parser!(name::String, op::Type{T}, arity::Int) where T <: Head
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

function prim_str(::T) where T <: Head
    name_of_primop[T]
end

function prim_arity(::Type{T}) where T <: Head
    arity_of_primop[T]
end

struct Y <: Head end
define_parser!("Y", Y, 1)


struct FlipOp <: Head end
define_parser!("flip", FlipOp, 1)

struct FlipOpDual <: Head end
define_parser!("flipd", FlipOpDual, 1)

struct NativeEqOp <: Head end
define_parser!("native_eq", NativeEqOp, 2)

struct GetArgsOp <: Head end
define_parser!("get_args", GetArgsOp, 1)

struct GetConstructorOp <: Head end
define_parser!("get_constructor", GetConstructorOp, 1)

struct PBoolOp <: Head end
define_parser!("pbool", PBoolOp, 1)

struct GetConfig <: Head end
define_parser!("get_config", GetConfig, 0)

struct MkIntOp <: Head end
define_parser!("mk_int", MkIntOp, 2)

struct IntDistEqOp <: Head end
define_parser!("int_dist_eq", IntDistEqOp, 2)

struct QuoteOp <: Head end
define_parser!("quote", QuoteOp, 1)

struct EvalOp <: Head end
define_parser!("eval", EvalOp, 1)





# by default we just look in subexpressions for free variables
var_is_free(e::PExpr, var) = any(var_is_free(arg, var) for arg in e.args if arg isa PExpr)
var_is_free(e::PExpr{Abs}, var) = var_is_free(e.args[1], var + 1)
var_is_free(e::PExpr{Var}, var) = e.args[1] == var
var_is_free(e::PExpr{CaseOf}, var) =
    var_is_free(e.args[1], var) || any(case -> var_is_free(case, var), values(e.args[2]))
var_is_free(e::PExpr{Construct}, var) = any(var_is_free(arg, var) for arg in e.args[2])