"""
Lightweight Boolean formula DAG with SAT checking via DPLL + unit propagation.

Usage:
    x, y, z = Var(:x), Var(:y), Var(:z)
    f = (x & y) | ~z
    check(f)          # :sat or :unsat
    satisfying(f)     # Dict(:z => false) or nothing
"""
module BoolSAT

export BoolExpr, Var, TRUE, FALSE, check, satisfying, vars

# ── Types ──────────────────────────────────────────────────────────────

abstract type BoolExpr end

struct LitTrue  <: BoolExpr end
struct LitFalse <: BoolExpr end
struct Var      <: BoolExpr; id::Any end
struct Not      <: BoolExpr; x::BoolExpr end
struct And      <: BoolExpr; a::BoolExpr; b::BoolExpr end
struct Or       <: BoolExpr; a::BoolExpr; b::BoolExpr end

const TRUE  = LitTrue()
const FALSE = LitFalse()

# ── Smart constructors (simplify on build) ─────────────────────────────

not(::LitTrue)  = FALSE
not(::LitFalse) = TRUE
not(x::Not)     = x.x
not(x::BoolExpr) = Not(x)

and(::LitFalse, ::BoolExpr) = FALSE
and(::BoolExpr, ::LitFalse) = FALSE
and(::LitTrue,  b::BoolExpr) = b
and(a::BoolExpr, ::LitTrue)  = a
and(a::BoolExpr, b::BoolExpr) = And(a, b)

or(::LitTrue,  ::BoolExpr) = TRUE
or(::BoolExpr, ::LitTrue)  = TRUE
or(::LitFalse, b::BoolExpr) = b
or(a::BoolExpr, ::LitFalse) = a
or(a::BoolExpr, b::BoolExpr) = Or(a, b)

# ── Operators ──────────────────────────────────────────────────────────

Base.:~(x::BoolExpr) = not(x)
Base.:&(a::BoolExpr, b::BoolExpr) = and(a, b)
Base.:|(a::BoolExpr, b::BoolExpr) = or(a, b)

# ── Variable collection ───────────────────────────────────────────────

function vars(e::BoolExpr)
    s = Set{Any}()
    _vars!(s, e)
    return s
end
_vars!(s, ::LitTrue)  = nothing
_vars!(s, ::LitFalse) = nothing
_vars!(s, e::Var) = push!(s, e.id)
_vars!(s, e::Not) = _vars!(s, e.x)
_vars!(s, e::And) = (_vars!(s, e.a); _vars!(s, e.b))
_vars!(s, e::Or)  = (_vars!(s, e.a); _vars!(s, e.b))

# ── Substitute + simplify under partial assignment ────────────────────

subst(::LitTrue, _)  = TRUE
subst(::LitFalse, _) = FALSE
subst(e::Var, env) = haskey(env, e.id) ? (env[e.id] ? TRUE : FALSE) : e
subst(e::Not, env) = not(subst(e.x, env))
subst(e::And, env) = and(subst(e.a, env), subst(e.b, env))
subst(e::Or,  env) = or(subst(e.a, env), subst(e.b, env))

# ── Unit propagation ──────────────────────────────────────────────────
# Extract forced literals from the top-level conjunction spine.
# e.g. And(Var(:x), And(Not(Var(:y)), rest)) → {:x => true, :y => false}

function _extract_units!(units::Dict{Any,Bool}, e::And)
    _extract_units!(units, e.a)
    _extract_units!(units, e.b)
end
function _extract_units!(units::Dict{Any,Bool}, e::Var)
    if haskey(units, e.id) && units[e.id] == false
        units[e.id] = false  # conflict will be caught by subst → FALSE
    else
        units[e.id] = true
    end
end
function _extract_units!(units::Dict{Any,Bool}, e::Not)
    if e.x isa Var
        if haskey(units, e.x.id) && units[e.x.id] == true
            units[e.x.id] = true  # conflict will be caught by subst → FALSE
        else
            units[e.x.id] = false
        end
    end
end
_extract_units!(_, ::BoolExpr) = nothing

function _propagate(e::BoolExpr, env::Dict{Any,Bool})
    while true
        s = subst(e, env)
        (s isa LitTrue || s isa LitFalse) && return s

        units = Dict{Any,Bool}()
        _extract_units!(units, s)

        # Only keep new units (not already in env)
        new_units = Dict(k => v for (k, v) in units if !haskey(env, k))
        isempty(new_units) && return s

        merge!(env, new_units)
        e = s  # work on already-simplified formula
    end
end

# ── DPLL ──────────────────────────────────────────────────────────────

"""
    check(e::BoolExpr) → :sat or :unsat
"""
function check(e::BoolExpr)
    _dpll(e, Dict{Any,Bool}()) ? :sat : :unsat
end

"""
    satisfying(e::BoolExpr) → Dict{Any,Bool} or nothing

Returns a satisfying assignment, or nothing if unsat.
Unassigned variables are don't-cares.
"""
function satisfying(e::BoolExpr)
    env = Dict{Any,Bool}()
    _dpll(e, env) ? env : nothing
end

function _dpll(e::BoolExpr, env::Dict{Any,Bool})
    s = _propagate(e, env)
    s isa LitTrue  && return true
    s isa LitFalse && return false

    v = _pick_var(s)

    # Branch true
    env[v] = true
    if _dpll(e, env)
        return true
    end

    # Branch false
    env[v] = false
    if _dpll(e, env)
        return true
    end

    # Undo and fail
    delete!(env, v)
    return false
end

function _pick_var(e::BoolExpr)
    e isa Var && return e.id
    e isa Not && return _pick_var(e.x)
    e isa And && return _pick_var(e.a)
    e isa Or  && return _pick_var(e.a)
    error("_pick_var: no variables in expression")
end

# ── Display ───────────────────────────────────────────────────────────

Base.show(io::IO, ::LitTrue)  = print(io, "⊤")
Base.show(io::IO, ::LitFalse) = print(io, "⊥")
Base.show(io::IO, e::Var)     = print(io, e.id)
function Base.show(io::IO, e::Not)
    print(io, "¬")
    _needs_parens(e.x) ? (print(io, "("); show(io, e.x); print(io, ")")) : show(io, e.x)
end
function Base.show(io::IO, e::And)
    print(io, "("); show(io, e.a); print(io, " ∧ "); show(io, e.b); print(io, ")")
end
function Base.show(io::IO, e::Or)
    print(io, "("); show(io, e.a); print(io, " ∨ "); show(io, e.b); print(io, ")")
end

_needs_parens(::Union{And, Or}) = true
_needs_parens(::BoolExpr) = false

end # module
