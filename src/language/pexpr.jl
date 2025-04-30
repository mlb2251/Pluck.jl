export PExpr, Primitive, Var, DiffVar, App, Abs, Y, Defined, PExpr, ConstReal, CaseOf, Construct, RawInt

import DataStructures: OrderedDict

abstract type Primitive end

mutable struct PExpr{P <: Primitive}
    op::P
    args::Vector{Any}
end


# General PExpr methods
get_func(e::PExpr) = e
JSON.lower(e::PExpr) = string(e)
maybe_const(e) = nothing

var_is_free(e::PExpr, var) = any(var_is_free(arg, var) for arg in e.args if var isa PExpr)
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
getarg(e::PExpr, i) = e.args[i]


struct Var <: Primitive end
Var(idx::Int) = Var(idx, :noname)
Var(idx, name) = PExpr(Var(), Any[idx, name])
var_is_free(e::PExpr{Var}, var) = e.args[1] == var
Base.show(io::IO, e::PExpr{Var}) =
    e.args[2] === :noname ? print(io, "#", e.args[1]) : print(io, e.args[2], "#", e.args[1])


struct DiffVar <: Primitive end
DiffVar(idx::Int) = DiffVar(idx, :noname)
DiffVar(idx, name) = PExpr(DiffVar(), Any[idx, name])
var_is_free(e::PExpr{DiffVar}, var) = e.args[1] == var
Base.show(io::IO, e::PExpr{DiffVar}) =
    e.args[2] === :noname ? print(io, "#", e.args[1]) : print(io, e.args[2], "#", e.args[1])

struct Y <: Primitive end
Y(f) = PExpr(Y(), Any[f])

struct Defined <: Primitive end
Defined(name) = PExpr(Defined(), Any[name])

shortname(e::PExpr{Defined}) = string(e.args[1])
Base.show(io::IO, e::PExpr{Defined}) = print(io, e.args[1])

struct RawInt <: Primitive end
RawInt(val) = PExpr(RawInt(), Any[val])

shortname(e::PExpr{RawInt}) = "&"
Base.show(io::IO, e::PExpr{RawInt}) = print(io, "&", e.args[1])

struct ConstReal <: Primitive end
ConstReal(val) = PExpr(ConstReal(), Any[val])

shortname(e::PExpr{ConstReal}) = string(e.args[1])
Base.show(io::IO, e::PExpr{ConstReal}) = print(io, e.args[1])


struct CaseOf <: Primitive end
CaseOf(scrutinee, cases) = PExpr(CaseOf(), Any[scrutinee, cases])

var_is_free(e::PExpr{CaseOf}, var) =
    var_is_free(e.args[1], var) || any(case -> var_is_free(case, var), values(e.args[2]))
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



struct Construct <: Primitive end
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
    if e.args[1] == :O
        return 0
    elseif e.args[1] == :S
        inner = maybe_const(e.args[1])
        isnothing(inner) && return nothing
        return inner + 1
    end
    return nothing
end
Base.copy(e::PExpr{Construct}) = PExpr(Construct(), Any[copy(e.args[1]), [copy(arg) for arg in e.args[2]]])

