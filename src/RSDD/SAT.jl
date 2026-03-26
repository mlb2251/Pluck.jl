"""
Lightweight Boolean formula DAG with SAT checking via DPLL + unit propagation.
Single concrete type with a `head::Symbol` tag instead of multiple subtypes.
Hash-consed: each unique node gets a unique `uid`, equality and hashing are O(1).

Usage:
    x, y, z = sat_var(1), sat_var(2), sat_var(3)
    f = sat_or(sat_and(x, y), sat_not(z))
    sat_check(f)          # :sat or :unsat
    sat_assignment(f)     # Dict(3 => false) or nothing
"""
module SAT

export SATExpr, sat_var, SAT_TRUE, SAT_FALSE, sat_check, sat_assignment, sat_vars, clear_sat!, sat_not, sat_and, sat_or

# ── UID generation ────────────────────────────────────────────────────

const _NEXT_UID = Ref{UInt64}(2)  # 0 and 1 reserved for TRUE/FALSE
_next_uid!() = (_NEXT_UID[] += 1; _NEXT_UID[])

# ── Single concrete type ─────────────────────────────────────────────
# head: :T, :F, :var, :not, :and, :or

mutable struct SATExpr
    const head::Symbol
    const id::Int                          # only meaningful for :var
    const a::Union{SATExpr, Nothing}       # first child  (:not, :and, :or)
    const b::Union{SATExpr, Nothing}       # second child (:and, :or)
    const uid::UInt64
end

const SAT_TRUE  = SATExpr(:T,  0, nothing, nothing, UInt64(0))
const SAT_FALSE = SATExpr(:F, 0, nothing, nothing, UInt64(1))

# ── Intern/cache tables ──────────────────────────────────────────────
# uid-keyed tables use Dicts keyed on UInt64.
# (uid1,uid2)-keyed tables use Dicts keyed on Tuple.

const _VAR_INTERN = Dict{Int, SATExpr}()
const _NOT_INTERN = Dict{UInt64, SATExpr}()
const _AND_INTERN = Dict{Tuple{UInt64,UInt64}, SATExpr}()
const _OR_INTERN  = Dict{Tuple{UInt64,UInt64}, SATExpr}()

# SAT result: 0 = unknown, 1 = sat, -1 = unsat.
const _SAT_RESULT = Dict{UInt64, Int8}()

# ── Interning constructors ───────────────────────────────────────────

function sat_var(id::Int)
    get!(_VAR_INTERN, id) do
        SATExpr(:var, id, nothing, nothing, _next_uid!())
    end
end

function _make_not(x::SATExpr)
    get!(_NOT_INTERN, x.uid) do
        SATExpr(:not, 0, x, nothing, _next_uid!())
    end
end

function _make_and(a::SATExpr, b::SATExpr)
    key = (a.uid, b.uid)
    get!(_AND_INTERN, key) do
        SATExpr(:and, 0, a, b, _next_uid!())
    end
end

function _make_or(a::SATExpr, b::SATExpr)
    key = (a.uid, b.uid)
    get!(_OR_INTERN, key) do
        SATExpr(:or, 0, a, b, _next_uid!())
    end
end

# ── Equality & hashing (O(1) via uid) ────────────────────────────────

Base.:(==)(a::SATExpr, b::SATExpr) = a.uid == b.uid
Base.hash(e::SATExpr, h::UInt) = hash(e.uid, h)

# ── SAT result cache ─────────────────────────────────────────────────

function _known_sat(e::SATExpr)
    e.head === :T && return true
    e.head === :F && return false
    v = get(_SAT_RESULT, e.uid, Int8(0))
    v == Int8(0) ? nothing : v == Int8(1)
end

function _set_sat!(uid::UInt64, val::Bool)
    _SAT_RESULT[uid] = val ? Int8(1) : Int8(-1)
end

function clear_sat!()
    empty!(_VAR_INTERN)
    empty!(_NOT_INTERN)
    empty!(_AND_INTERN)
    empty!(_OR_INTERN)
    empty!(_SAT_RESULT)
    _NEXT_UID[] = 0
end

# ── Smart constructors (simplify on build) ───────────────────────────

function sat_not(x::SATExpr)
    x.head === :T  && return SAT_FALSE
    x.head === :F  && return SAT_TRUE
    x.head === :not && return x.a
    k = _known_sat(x)
    k === false && return SAT_TRUE
    _make_not(x)
end

function sat_and(a::SATExpr, b::SATExpr)
    a.head === :F && return SAT_FALSE
    b.head === :F && return SAT_FALSE
    a.head === :T && return b
    b.head === :T && return a
    _known_sat(a) === false && return SAT_FALSE
    _known_sat(b) === false && return SAT_FALSE
    _make_and(a, b)
end

function sat_or(a::SATExpr, b::SATExpr)
    a.head === :T && return SAT_TRUE
    b.head === :T && return SAT_TRUE
    a.head === :F && return b
    b.head === :F && return a
    _known_sat(a) === false && return b
    _known_sat(b) === false && return a
    _make_or(a, b)
end

# ── Variable collection ──────────────────────────────────────────────

function sat_vars(e::SATExpr)
    s = Set{Int}()
    _vars!(s, e)
    return s
end

function _vars!(s, e::SATExpr)
    h = e.head
    h === :T   && return nothing
    h === :F   && return nothing
    h === :var && (push!(s, e.id); return nothing)
    h === :not && (_vars!(s, e.a); return nothing)
    _vars!(s, e.a)
    _vars!(s, e.b)
    return nothing
end

# ── Substitute + simplify under partial assignment ───────────────────
# Cache is a uid-indexed Vector for speed.

function subst(e::SATExpr, env::Dict{Int,Bool})
    _subst(e, env, Dict{UInt64,SATExpr}())
end

function _subst(e::SATExpr, env::Dict{Int,Bool}, cache::Dict{UInt64,SATExpr})
    h = e.head
    h === :T && return SAT_TRUE
    h === :F && return SAT_FALSE
    if h === :var
        return haskey(env, e.id) ? (env[e.id] ? SAT_TRUE : SAT_FALSE) : e
    end
    haskey(cache, e.uid) && return cache[e.uid]
    r = if h === :not
        sat_not(_subst(e.a, env, cache))
    elseif h === :and
        sat_and(_subst(e.a, env, cache), _subst(e.b, env, cache))
    else # :or
        sat_or(_subst(e.a, env, cache), _subst(e.b, env, cache))
    end
    cache[e.uid] = r
end

# ── Unit propagation ─────────────────────────────────────────────────

function _extract_units!(units::Dict{Int,Bool}, e::SATExpr)
    h = e.head
    if h === :and
        _extract_units!(units, e.a)
        _extract_units!(units, e.b)
    elseif h === :var
        units[e.id] = get(units, e.id, true)
    elseif h === :not && e.a.head === :var
        units[e.a.id] = get(units, e.a.id, false)
    end
    nothing
end

function _propagate(e::SATExpr, env::Dict{Int,Bool})
    while true
        cache = Dict{UInt64,SATExpr}()
        s = _subst(e, env, cache)
        (s.head === :T || s.head === :F) && return s

        units = Dict{Int,Bool}()
        _extract_units!(units, s)

        new_units = Dict(k => v for (k, v) in units if !haskey(env, k))
        isempty(new_units) && return s

        merge!(env, new_units)
        e = s
    end
end

# ── DPLL ─────────────────────────────────────────────────────────────

"""
    sat_check(e::SATExpr) → :sat or :unsat
"""
function sat_check(e::SATExpr)
    k = _known_sat(e)
    k !== nothing && return k ? :sat : :unsat
    result = _dpll(e, Dict{Int,Bool}())
    _set_sat!(e.uid, result)
    result ? :sat : :unsat
end

"""
    sat_assignment(e::SATExpr) → Dict{Int,Bool} or nothing

Returns a satisfying assignment, or nothing if unsat.
Unassigned variables are don't-cares.
"""
function sat_assignment(e::SATExpr)
    env = Dict{Int,Bool}()
    result = _dpll(e, env)
    _set_sat!(e.uid, result)
    result ? env : nothing
end

function _dpll(e::SATExpr, env::Dict{Int,Bool})
    s = _propagate(e, env)
    s.head === :T && return true
    s.head === :F && return false

    v = _pick_var(s)

    env[v] = true
    _dpll(s, env) && return true

    env[v] = false
    _dpll(s, env) && return true

    delete!(env, v)
    return false
end

function _pick_var(e::SATExpr)
    h = e.head
    h === :var && return e.id
    h === :not && return _pick_var(e.a)
    (h === :and || h === :or) && return _pick_var(e.a)
    error("_pick_var: no variables in expression")
end

# ── Display ──────────────────────────────────────────────────────────

function Base.show(io::IO, e::SATExpr)
    h = e.head
    if h === :T
        print(io, "⊤")
    elseif h === :F
        print(io, "⊥")
    elseif h === :var
        print(io, e.id)
    elseif h === :not
        print(io, "¬")
        if e.a.head === :and || e.a.head === :or
            print(io, "("); show(io, e.a); print(io, ")")
        else
            show(io, e.a)
        end
    elseif h === :and
        print(io, "("); show(io, e.a); print(io, " ∧ "); show(io, e.b); print(io, ")")
    elseif h === :or
        print(io, "("); show(io, e.a); print(io, " ∨ "); show(io, e.b); print(io, ")")
    end
end

end # module
