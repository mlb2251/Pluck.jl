export PExpr, Primitive, Var, App, Abs, Y, Defined, PrimOp, ConstReal, CaseOf, Construct, RawInt

abstract type PExpr end
abstract type Primitive end

# General PExpr methods
shortname(e::PExpr) = string(e)
Base.copy(e::PExpr) = error("not implemented")
num_apps(e::PExpr) = 0
get_func(e::PExpr) = e
getarg(e::PExpr, i) = error("arg doesnt exist")
JSON.lower(e::PExpr) = string(e)
maybe_const(e) = nothing

# deBruijn indexing
struct Var <: PExpr
    idx::Int
    name::Symbol
end
Var(idx::Int) = Var(idx, :noname)

var_is_free(e::Var, var) = e.idx == var
shortname(e::Var) = string(e)
Base.show(io::IO, e::Var) =
    e.name === :noname ? print(io, "#", e.idx) : print(io, e.name, "#", e.idx)
Base.copy(e::Var) = Var(e.idx, e.name)
Base.:(==)(a::Var, b::Var) = a.idx == b.idx
Base.hash(e::Var, h::UInt) = hash(e.idx, hash(:Var, h))

# function application
mutable struct App <: PExpr
    f::PExpr
    x::PExpr
end

var_is_free(e::App, var) = var_is_free(e.f, var) || var_is_free(e.x, var)
shortname(e::App) = "App"
function Base.show(io::IO, e::App)
    print(io, "(", get_func(e))
    for i ∈ 1:num_apps(e)
        print(io, " ", getarg(e, i))
    end
    print(io, ")")
end
Base.copy(e::App) = App(copy(e.f), copy(e.x))
Base.:(==)(a::App, b::App) = a.f == b.f && a.x == b.x
Base.hash(e::App, h::UInt) = hash(e.f, hash(e.x, hash(:App, h)))
# (app f x y) -> (app (app f x) y)
num_apps(e::App) = 1 + num_apps(e.f)
get_func(e::App) = get_func(e.f)
function getarg(e::App, i)
    # for an app chain (app (app f x) y) we want x to be the 1st arg and y to be
    # the second arg.
    which_app = num_apps(e) - i + 1
    for _ ∈ 1:which_app-1
        e = e.f
    end
    e.x
end

# functional abstraction
mutable struct Abs <: PExpr
    body::PExpr
    name::Symbol
end

var_is_free(e::Abs, var) = var_is_free(e.body, var + 1)
shortname(e::Abs) = "λ" * string(e.name)
function Base.show(io::IO, e::Abs)
    print(io, "(λ", e.name)
    while e.body isa Abs
        e = e.body
        print(io, " ", e.name)
    end
    print(io, " -> ", e.body, ")")
end
Base.copy(e::Abs) = Abs(copy(e.body), e.name)
Base.:(==)(a::Abs, b::Abs) = a.body == b.body
Base.hash(e::Abs, h::UInt) = hash(e.body, hash(:Abs, h))

mutable struct Y <: PExpr
    f::PExpr
    t0::Union{PType,Nothing}
    t1::Union{PType,Nothing}
end
Y(f) = Y(f, nothing, nothing)

var_is_free(e::Y, var) = var_is_free(e.f, var)
shortname(e::Y) = "Y"
function Base.show(io::IO, e::Y)
    annotation = isnothing(e.t0) ? "" : "{$(e.t0),$(e.t1)}"
    print(io, "(Y$annotation ", e.f, ")")
end
Base.copy(e::Y) = Y(copy(e.f), e.t0, e.t1)
Base.:(==)(a::Y, b::Y) = a.f == b.f
Base.hash(e::Y, h::UInt) = hash(e.f, hash(:Y, h))

struct Defined <: PExpr
    name::Symbol
end

var_is_free(e::Defined, var) = false
shortname(e::Defined) = string(e)
Base.show(io::IO, e::Defined) = print(io, e.name)
Base.copy(e::Defined) = Defined(e.name)
Base.:(==)(a::Defined, b::Defined) = a.name == b.name
Base.hash(e::Defined, h::UInt) = hash(e.name, hash(:Defined, h))

mutable struct PrimOp <: PExpr
    op::Primitive
    args::Vector{PExpr}
end

var_is_free(e::PrimOp, var) = any(var_is_free(arg, var) for arg in e.args)
shortname(e::PrimOp) = string(e.op)
function Base.show(io::IO, e::PrimOp)
    print(io, "(", e.op)
    for arg in e.args
        print(io, " ", arg)
    end
    print(io, ")")
end
Base.copy(e::PrimOp) = PrimOp(e.op, [copy(arg) for arg in e.args])
Base.:(==)(a::PrimOp, b::PrimOp) = a.op == b.op && a.args == b.args
Base.hash(e::PrimOp, h::UInt) = hash(e.op, hash(e.args, hash(:PrimOp, h)))
getarg(e::PrimOp, i) = e.args[i]

struct RawInt <: PExpr
    val::Int
end

var_is_free(e::RawInt, var) = false
shortname(e::RawInt) = "&"
Base.show(io::IO, e::RawInt) = print(io, "&", e.val)
Base.copy(e::RawInt) = RawInt(e.val)
Base.:(==)(a::RawInt, b::RawInt) = a.val == b.val
Base.hash(e::RawInt, h::UInt) = hash(e.val, hash(:RawInt, h))

struct ConstReal <: PExpr
    val::Float64
end

var_is_free(e::ConstReal, var) = false
shortname(e::ConstReal) = string(e.val)
Base.show(io::IO, e::ConstReal) = print(io, e.val)
Base.copy(e::ConstReal) = ConstReal(e.val)
Base.:(==)(a::ConstReal, b::ConstReal) = a.val == b.val
Base.hash(e::ConstReal, h::UInt) = hash(e.val, hash(:ConstReal, h))

mutable struct CaseOf <: PExpr
    scrutinee::PExpr
    cases::Dict{Symbol,PExpr}
    constructors::Vector{Symbol} # for deterministic enumeration of the cases
end

var_is_free(e::CaseOf, var) =
    var_is_free(e.scrutinee, var) || any(case -> var_is_free(case, var), values(e.cases))
shortname(e::CaseOf) = "CaseOf"
function Base.show(io::IO, e::CaseOf)
    print(io, "(case ", e.scrutinee, " of ")
    for (i, constructor) in enumerate(e.constructors)
        print(io, constructor, " => ", e.cases[constructor])
        if i < length(e.constructors)
            print(io, " | ")
        end
    end
    print(io, ")")
end
Base.copy(e::CaseOf) = CaseOf(
    copy(e.scrutinee),
    Dict(constructor => copy(e.cases[constructor]) for constructor in keys(e.cases)),
    copy(e.constructors),
)
Base.:(==)(a::CaseOf, b::CaseOf) =
    a.scrutinee == b.scrutinee &&
    a.constructors == b.constructors &&
    all(constructor -> a.cases[constructor] == b.cases[constructor], a.constructors)
Base.hash(e::CaseOf, h::UInt) =
    hash(e.scrutinee, hash(e.cases, hash(e.constructors, hash(:CaseOf, h))))

mutable struct Construct <: PExpr
    constructor::Symbol
    args::Vector{PExpr}
end

var_is_free(e::Construct, var) = any(arg -> var_is_free(arg, var), e.args)
shortname(e::Construct) = string(e.constructor)
function Base.show(io::IO, e::Construct)
    as_const = maybe_const(e)
    if !isnothing(as_const)
        print(io, as_const)
        return
    end
    print(io, "(", e.constructor)
    for arg in e.args
        print(io, " ", arg)
    end
    print(io, ")")
end
function maybe_const(e::Construct)
    if e.constructor == :O
        return 0
    elseif e.constructor == :S
        inner = maybe_const(e.args[1])
        isnothing(inner) && return nothing
        return inner + 1
    end
    return nothing
end
Base.copy(e::Construct) = Construct(e.constructor, [copy(arg) for arg in e.args])
Base.:(==)(a::Construct, b::Construct) =
    a.constructor === b.constructor && a.args == b.args
Base.hash(e::Construct, h::UInt) =
    hash(e.constructor, hash(e.args, hash(:Construct, h)))
