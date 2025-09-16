export PExpr, Head, Var, App, Abs, Y, Defined, PExpr, CaseOf, Construct, FlipOp, NativeEqOp, MkIntOp, IntDistEqOp, GetArgsOp, PBoolOp, GetConstructorOp, GetConfig, ConstNative, GSymbol, GVarSymbol, max_native_int_used

import DataStructures: OrderedDict

using AutoHashEquals

abstract type Head end

Base.show(io::IO, e::T) where T <: Head = print(io, prim_str(e))


"""
An expression in the Pluck language.
.args has all the subexpressions, and .head has any additional non-PExpr data.
"""
@auto_hash_equals mutable struct PExpr{H <: Head}
    head::H
    args::Vector{Any}
    PExpr(head::H, args) where H <: Head = new{H}(head, args)
    PExpr(head::H) where H <: Head = new{H}(head, [])
end
Base.copy(e::PExpr) = PExpr(e.head, Any[copy(arg) for arg in e.args])

(head::H where {H <: Head})(args...) = PExpr(head, collect(args))


function bottomup_descendants(e::PExpr)
    worklist = Vector{PExpr}(e)
    result = Vector{PExpr}(e)
    while !isempty(worklist)
        e = popfirst!(worklist)
        push!(result, e)
        for arg in e.args
            push!(worklist, arg)
        end
    end
    result
end

# default PExpr methods
JSON.lower(e::PExpr) = string(e)
shortname(e::PExpr) = string(e.head)
function Base.show(io::IO, e::PExpr)
    print(io, "(", e.head)
    for arg in e.args
        print(io, " ", arg)
    end
    print(io, ")")
end

##############
# Operations #
##############

# Function application
@auto_hash_equals struct App <: Head end
Base.show(io::IO, e::App) = print(io, "App")
function Base.show(io::IO, e::PExpr{App})
    # show (App (λ x -> e) arg) as (let [x e] arg)
    # and show (App (λ x -> (App (λ x -> e) ey)) ex) as (let [x ex y ey] e) 
    if e.args[1] isa PExpr{Abs}
        bindings = Tuple{Symbol, PExpr}[(e.args[1].head.var, e.args[2])]
        body = e.args[1].args[1]
        while body isa PExpr{App} && body.args[1] isa PExpr{Abs}
            push!(bindings, (body.args[1].head.var, body.args[2]))
            body = body.args[1].args[1]
        end

        print(io, "(let [")
        for (i, (var, expr)) in enumerate(bindings)
            print(io, "$var $expr")
            i < length(bindings) && print(io, " ")
        end
        print(io, "] ")
        print(io, body)
        print(io, ")")
        return
    end

    # show like (f x y)
    argc = num_apps(e)
    print(io, "(", getfunc(e))

    # show (f (Unit)) as (f)
    if argc == 1 && getarg(e, 1) isa PExpr{Construct} && getarg(e, 1).head.constructor === :Unit
        print(io, ")")
        return
    end

    for i ∈ 1:argc
        print(io, " ", getarg(e, i))
    end
    print(io, ")")
end

getf(e::PExpr{App}) = e.args[1]
getx(e::PExpr{App}) = e.args[2]

getfunc(e::PExpr{App}) = getfunc(getf(e))
getfunc(e) = e

num_apps(e) = 0
num_apps(e::PExpr{App}) = 1 + num_apps(getf(e))
function getarg(e::PExpr{App}, i)
    # for an app chain (app (app f x) y) we want x to be the 1st arg and y to be
    # the second arg.
    which_app = num_apps(e) - i + 1
    for _ in 1:which_app-1
        e = getf(e)
    end
    getx(e)
end

function argpath(e::PExpr{App}, i)
    which_app = num_apps(e) - i + 1
    path = ones(Int, which_app-1) # index into `f` that many times
    push!(path, 2) # index into `x`
    path
end

# Function abstraction
@auto_hash_equals struct Abs <: Head
    var::Symbol
end
Base.copy(h::Abs) = h
Base.show(io::IO, h::Abs) = print(io, "λ", h.var)
function Base.show(io::IO, e::PExpr{Abs})
    print(io, "(λ", e.head.var)
    while e.args[1] isa PExpr{Abs}
        e = e.args[1]
        print(io, " ", e.head.var)
    end
    print(io, " -> ", e.args[1], ")")
end

@auto_hash_equals struct Var <: Head
    name::Symbol
end
Base.show(io::IO, h::Var) = print(io, "\$", h.name)
Base.show(io::IO, e::PExpr{Var}) = print(io, e.head)

@auto_hash_equals struct Defined <: Head
    name::Symbol
end
Base.show(io::IO, h::Defined) = print(io, h.name)
Base.show(io::IO, e::PExpr{Defined}) = print(io, e.head)

@auto_hash_equals struct GSymbol <: Head
    name::Symbol
end
Base.show(io::IO, h::GSymbol) = print(io, "?", h.name)
Base.show(io::IO, e::PExpr{GSymbol}) = print(io, e.head)

@auto_hash_equals struct GVarSymbol <: Head
    name::Symbol
end
Base.show(io::IO, h::GVarSymbol) = print(io, "#", h.name)
Base.show(io::IO, e::PExpr{GVarSymbol}) = print(io, e.head)

@auto_hash_equals struct ConstNative <: Head
    val::Any
end
getval(e::PExpr{ConstNative}) = e.head.val
function Base.show(io::IO, e::ConstNative)
    if e.val isa Int
        print(io, "@")
    elseif e.val isa Symbol
        print(io, "'")
    elseif e.val isa PExpr
        print(io, "`")
    end
    print(io, e.val)
end
Base.show(io::IO, e::PExpr{ConstNative}) = show(io, e.head)
@auto_hash_equals struct CaseOfGuard
    constructor::Symbol
    args::Vector{Symbol}
end
function Base.show(io::IO, g::CaseOfGuard)
    print(io, g.constructor)
    for arg in g.args
        print(io, " ", arg)
    end
end

@auto_hash_equals struct CaseOf <: Head
    branches::Vector{CaseOfGuard}
end

numbranches(e::PExpr{CaseOf}) = length(e.head.branches)
getguard(e::PExpr{CaseOf}, i::Int) = e.head.branches[i]
getscrutinee(e::PExpr{CaseOf}) = e.args[1]
getbranch(e::PExpr{CaseOf}, i::Int) = e.args[i+1]
Base.show(io::IO, ::CaseOf) = print(io, "caseof")
function Base.show(io::IO, e::PExpr{CaseOf})
    if length(e.head.branches) == 2 && e.head.branches[1].constructor == :True && e.head.branches[2].constructor == :False
        print(io, "(if ", getscrutinee(e), " ", getbranch(e, 1), " ", getbranch(e, 2), ")")
        return
    end

    print(io, "(case ", getscrutinee(e), " of ")
    for i in eachindex(e.head.branches)
        print(io, getguard(e, i), " => ", getbranch(e, i))
        i < numbranches(e) && print(io, " | ")
    end
    print(io, ")")
end

@auto_hash_equals struct Construct <: Head
    constructor::Symbol
end
Base.show(io::IO, h::Construct) = print(io, h.constructor)
function Base.show(io::IO, e::PExpr{Construct})
    as_const = maybe_const(e)
    if !isnothing(as_const)
        print(io, as_const)
        return
    end
    print(io, "(", e.head.constructor)
    for arg in e.args
        print(io, " ", arg)
    end
    print(io, ")")
end
function maybe_const(e::PExpr{Construct})
    if e.head.constructor === :O
        return 0
    elseif e.head.constructor === :S
        inner = maybe_const(e.args[1])
        isnothing(inner) && return nothing
        return inner + 1
    end
    return nothing
end
maybe_const(e) = nothing

##############
# Simple Ops #
##############

const primop_of_name::Dict{String, Type} = Dict()
const primop_of_sym::Dict{Symbol, Type} = Dict()
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

struct PrintOp <: Head end
define_parser!("print", PrintOp, 1)

struct AbstractTypeOp <: Head end
define_parser!("abstract_type", AbstractTypeOp, 1)

struct FDivOp <: Head end
define_parser!("/.", FDivOp, 2)

struct FMulOp <: Head end
define_parser!("*.", FMulOp, 2)

struct FAddOp <: Head end
define_parser!("+.", FAddOp, 2)

struct FSubOp <: Head end
define_parser!("-.", FSubOp, 2)

struct IsApproxOp <: Head end
define_parser!("isapprox", IsApproxOp, 2)

struct ErrorOp <: Head end
define_parser!("error", ErrorOp, 1)

struct DefineOp <: Head end
define_parser!("define", DefineOp, 2)

struct PExprFromValueOp <: Head end
define_parser!("pexpr_from_value", PExprFromValueOp, 1)




# by default we just look in subexpressions for free variables
var_is_free(e::PExpr, var) = any(var_is_free(arg, var) for arg in e.args)
# abs binds a new variable
var_is_free(e::PExpr{Abs}, var) = var_is_free(e.args[1], var + 1)
# vars are free if they are the same as the variable we're checking for
var_is_free(e::PExpr{Var}, var) = e.head.name == var
# CaseOf branches also bind variables – one for each arg to the guard
var_is_free(e::PExpr{CaseOf}, var) = 
    var_is_free(getscrutinee(e), var) || any(case -> !any(arg -> arg == var, getguard(e, case).args) && var_is_free(getbranch(e, case), var), 1:numbranches(e))
