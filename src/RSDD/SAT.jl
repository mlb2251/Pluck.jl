"""
Lightweight Boolean formula DAG with SAT checking via DPLL + unit propagation.
Properly hash-consed nodes: each unique node gets a unique `uid`, equality sat_and
hashing are O(1) via uid comparison. Per-type intern tables use structural keys
(child uids) to guarantee sharing.

Usage:
    x, y, z = SATVar(1), SATVar(2), SATVar(3)
    f = (x & y) | ~z
    sat_check(f)          # :sat or :unsat
    sat_assignment(f)     # Dict(3 => false) or nothing
"""
module SAT

export SATExpr, SATVar, SAT_TRUE, SAT_FALSE, sat_check, sat_assignment, sat_vars, clear_sat!, sat_not, sat_and, sat_or

# ── UID generation ────────────────────────────────────────────────────

const _NEXT_UID = Ref{UInt64}(2)  # 0 sat_and 1 reserved for LitTrue/LitFalse
_next_uid!() = (_NEXT_UID[] += 1; _NEXT_UID[])

# ── Types ─────────────────────────────────────────────────────────────

abstract type SATExpr end

struct LitTrue  <: SATExpr end
struct LitFalse <: SATExpr end

struct SATVar <: SATExpr
    id::Int
    uid::UInt64
end

struct Not <: SATExpr
    x::SATExpr
    uid::UInt64
end

struct And <: SATExpr
    a::SATExpr
    b::SATExpr
    uid::UInt64
end

struct Or <: SATExpr
    a::SATExpr
    b::SATExpr
    uid::UInt64
end

const SAT_TRUE  = LitTrue()
const SAT_FALSE = LitFalse()

# ── uid accessor ──────────────────────────────────────────────────────

_uid(::LitTrue)  = UInt64(0)   # reserved
_uid(::LitFalse) = UInt64(1)   # reserved
_uid(e::SATVar)  = e.uid
_uid(e::Not)     = e.uid
_uid(e::And)     = e.uid
_uid(e::Or)      = e.uid

# ── Per-type intern tables (structural keys → canonical node) ────────

const _VAR_INTERN = Dict{Int, SATVar}()
const _NOT_INTERN = Dict{UInt64, Not}()
const _AND_INTERN = Dict{Tuple{UInt64,UInt64}, And}()
const _OR_INTERN  = Dict{Tuple{UInt64,UInt64}, Or}()

# ── Interning constructors ───────────────────────────────────────────

function SATVar(id::Int)
    get!(_VAR_INTERN, id) do
        SATVar(id, _next_uid!())
    end
end

function Not(x::SATExpr)
    get!(_NOT_INTERN, _uid(x)) do
        Not(x, _next_uid!())
    end
end

function And(a::SATExpr, b::SATExpr)
    key = (_uid(a), _uid(b))
    get!(_AND_INTERN, key) do
        And(a, b, _next_uid!())
    end
end

function Or(a::SATExpr, b::SATExpr)
    key = (_uid(a), _uid(b))
    get!(_OR_INTERN, key) do
        Or(a, b, _next_uid!())
    end
end

# ── Equality & hashing (O(1) via uid) ────────────────────────────────

Base.:(==)(::LitTrue, ::LitTrue)   = true
Base.:(==)(::LitFalse, ::LitFalse) = true
Base.:(==)(a::SATVar, b::SATVar)   = a.uid == b.uid
Base.:(==)(a::Not, b::Not)         = a.uid == b.uid
Base.:(==)(a::And, b::And)         = a.uid == b.uid
Base.:(==)(a::Or, b::Or)           = a.uid == b.uid

Base.hash(::LitTrue, h::UInt)  = hash(UInt64(0), h)
Base.hash(::LitFalse, h::UInt) = hash(UInt64(1), h)
Base.hash(e::SATVar, h::UInt)  = hash(e.uid, h)
Base.hash(e::Not, h::UInt)     = hash(e.uid, h)
Base.hash(e::And, h::UInt)     = hash(e.uid, h)
Base.hash(e::Or, h::UInt)      = hash(e.uid, h)

# ── SAT result cache (keyed on uid) ──────────────────────────────────

const _SAT_RESULT = Dict{UInt64, Bool}()

_known_sat(::LitTrue)  = true
_known_sat(::LitFalse) = false
_known_sat(e::SATExpr) = get(_SAT_RESULT, _uid(e), nothing)

function clear_sat!()
    empty!(_VAR_INTERN)
    empty!(_NOT_INTERN)
    empty!(_AND_INTERN)
    empty!(_OR_INTERN)
    empty!(_SAT_RESULT)
    _NEXT_UID[] = 0
end

# ── Smart constructors (simplify on build) ─────────────────────────────

sat_not(::LitTrue)  = SAT_FALSE
sat_not(::LitFalse) = SAT_TRUE
sat_not(x::Not)     = x.x
function sat_not(x::SATExpr)
    k = _known_sat(x)
    # UNSAT → negation is tautology; tautology check: ¬x unsat means x is tautology
    k === false && return SAT_TRUE
    Not(x)
end

sat_and(::LitFalse, ::SATExpr) = SAT_FALSE
sat_and(::SATExpr, ::LitFalse) = SAT_FALSE
sat_and(::LitTrue,  b::SATExpr) = b
sat_and(a::SATExpr, ::LitTrue)  = a
sat_and(::LitTrue,  ::LitFalse) = SAT_FALSE
sat_and(::LitFalse, ::LitTrue)  = SAT_FALSE
sat_and(::LitTrue,  ::LitTrue)  = SAT_TRUE
sat_and(::LitFalse, ::LitFalse) = SAT_FALSE
function sat_and(a::SATExpr, b::SATExpr)
    # If either operand is known UNSAT, conjunction is UNSAT
    _known_sat(a) === false && return SAT_FALSE
    _known_sat(b) === false && return SAT_FALSE
    And(a, b)
end

sat_or(::LitTrue,  ::SATExpr) = SAT_TRUE
sat_or(::SATExpr, ::LitTrue)  = SAT_TRUE
sat_or(::LitFalse, b::SATExpr) = b
sat_or(a::SATExpr, ::LitFalse) = a
sat_or(::LitTrue,  ::LitFalse) = SAT_TRUE
sat_or(::LitFalse, ::LitTrue)  = SAT_TRUE
sat_or(::LitTrue,  ::LitTrue)  = SAT_TRUE
sat_or(::LitFalse, ::LitFalse) = SAT_FALSE
function sat_or(a::SATExpr, b::SATExpr)
    # If either operand is a known tautology (¬x is known UNSAT), disjunction is tautology
    # We check: if sat_not(a) was previously found UNSAT, then a is a tautology
    _known_sat(a) === false && return b   # a is UNSAT, so a|b = b
    _known_sat(b) === false && return a   # b is UNSAT, so a|b = a
    Or(a, b)
end

# ── Operators ──────────────────────────────────────────────────────────

# Base.:~(x::SATExpr) = sat_not(x)
# Base.:!(x::SATExpr) = sat_not(x)
# Base.:&(a::SATExpr, b::SATExpr) = sat_and(a, b)
# Base.:|(a::SATExpr, b::SATExpr) = sat_or(a, b)

# ── Variable collection ───────────────────────────────────────────────

function sat_vars(e::SATExpr)
    s = Set{Int}()
    _vars!(s, e)
    return s
end
_vars!(s, ::LitTrue)  = nothing
_vars!(s, ::LitFalse) = nothing
_vars!(s, e::SATVar) = push!(s, e.id)
_vars!(s, e::Not) = _vars!(s, e.x)
_vars!(s, e::And) = (_vars!(s, e.a); _vars!(s, e.b))
_vars!(s, e::Or)  = (_vars!(s, e.a); _vars!(s, e.b))

# ── Substitute + simplify under partial assignment (memoized) ────────
# Cache keyed on uid (safe because nodes are hash-consed:
# structurally equal ⟹ same uid ⟹ same canonical object).

function subst(e::SATExpr, env::Dict{Int,Bool})
    _subst(e, env, Dict{UInt64,SATExpr}())
end

_subst(e::LitTrue, _, _)  = SAT_TRUE
_subst(e::LitFalse, _, _) = SAT_FALSE
function _subst(e::SATVar, env, _)
    haskey(env, e.id) ? (env[e.id] ? SAT_TRUE : SAT_FALSE) : e
end
function _subst(e::Not, env, cache)
    uid = _uid(e)
    haskey(cache, uid) && return cache[uid]
    r = sat_not(_subst(e.x, env, cache))
    cache[uid] = r
end
function _subst(e::And, env, cache)
    uid = _uid(e)
    haskey(cache, uid) && return cache[uid]
    r = sat_and(_subst(e.a, env, cache), _subst(e.b, env, cache))
    cache[uid] = r
end
function _subst(e::Or, env, cache)
    uid = _uid(e)
    haskey(cache, uid) && return cache[uid]
    r = sat_or(_subst(e.a, env, cache), _subst(e.b, env, cache))
    cache[uid] = r
end

# ── Unit propagation ──────────────────────────────────────────────────
# Extract forced literals from the top-level conjunction spine.
# e.g. And(SATVar(1), And(Not(SATVar(2)), rest)) → {1 => true, 2 => false}

function _extract_units!(units::Dict{Int,Bool}, e::And)
    _extract_units!(units, e.a)
    _extract_units!(units, e.b)
end
function _extract_units!(units::Dict{Int,Bool}, e::SATVar)
    units[e.id] = get(units, e.id, true)
end
function _extract_units!(units::Dict{Int,Bool}, e::Not)
    if e.x isa SATVar
        units[e.x.id] = get(units, e.x.id, false)
    end
end
_extract_units!(_, ::SATExpr) = nothing

function _propagate(e::SATExpr, env::Dict{Int,Bool})
    cache = Dict{UInt64,SATExpr}()
    while true
        empty!(cache)  # env changed, invalidate
        s = _subst(e, env, cache)
        (s isa LitTrue || s isa LitFalse) && return s

        units = Dict{Int,Bool}()
        _extract_units!(units, s)

        # Only keep new units (sat_not already in env)
        new_units = Dict(k => v for (k, v) in units if !haskey(env, k))
        isempty(new_units) && return s

        merge!(env, new_units)
        e = s  # work on already-simplified formula
    end
end

# ── DPLL ──────────────────────────────────────────────────────────────

"""
    sat_check(e::SATExpr) → :sat sat_or :unsat
"""
function sat_check(e::SATExpr)
    uid = _uid(e)
    haskey(_SAT_RESULT, uid) && return _SAT_RESULT[uid] ? :sat : :unsat
    result = _dpll(e, Dict{Int,Bool}())
    _SAT_RESULT[uid] = result
    result ? :sat : :unsat
end

"""
    sat_assignment(e::SATExpr) → Dict{Int,Bool} sat_or nothing

Returns a satisfying assignment, sat_or nothing if unsat.
Unassigned variables are don't-cares.
"""
function sat_assignment(e::SATExpr)
    env = Dict{Int,Bool}()
    result = _dpll(e, env)
    _SAT_RESULT[_uid(e)] = result
    result ? env : nothing
end

function _dpll(e::SATExpr, env::Dict{Int,Bool})
    s = _propagate(e, env)
    s isa LitTrue  && return true
    s isa LitFalse && return false

    v = _pick_var(s)

    # Branch true
    env[v] = true
    if _dpll(s, env)
        return true
    end

    # Branch false
    env[v] = false
    if _dpll(s, env)
        return true
    end

    # Undo sat_and fail
    delete!(env, v)
    return false
end

function _pick_var(e::SATExpr)
    e isa SATVar && return e.id
    e isa Not && return _pick_var(e.x)
    e isa And && return _pick_var(e.a)
    e isa Or  && return _pick_var(e.a)
    error("_pick_var: no variables in expression")
end

# ── Display ───────────────────────────────────────────────────────────

Base.show(io::IO, ::LitTrue)  = print(io, "⊤")
Base.show(io::IO, ::LitFalse) = print(io, "⊥")
Base.show(io::IO, e::SATVar)     = print(io, e.id)
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
_needs_parens(::SATExpr) = false

end # module
