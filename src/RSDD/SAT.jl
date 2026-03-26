"""
Lightweight Boolean formula DAG with SAT checking via DPLL + unit propagation.
Arena-based: all nodes live in a flat Vector, referenced by UInt32 index.
No heap allocation per node, no GC pressure.

Usage:
    x, y, z = sat_var(1), sat_var(2), sat_var(3)
    f = sat_or(sat_and(x, y), sat_not(z))
    sat_check(f)          # :sat or :unsat
    sat_assignment(f)     # Dict(3 => false) or nothing
"""
module SAT

export SATExpr, sat_var, SAT_TRUE, SAT_FALSE, sat_check, sat_assignment, sat_vars, clear_sat!, sat_not, sat_and, sat_or,
       CDCLSolver, cdcl_solver_from, cdcl_check_assuming!

# ── SATExpr is just an index into the arena ──────────────────────────

const SATExpr = UInt32

const _HEAD_T   = 0x01
const _HEAD_F   = 0x02
const _HEAD_VAR = 0x03
const _HEAD_NOT = 0x04
const _HEAD_AND = 0x05
const _HEAD_OR  = 0x06

struct SATNode
    head::UInt8
    id::Int32          # var id (only for _HEAD_VAR)
    a::UInt32          # first child uid  (not/and/or)
    b::UInt32          # second child uid (and/or)
end

# ── Arena ────────────────────────────────────────────────────────────

const _ARENA = SATNode[]

# Reserve index 1 = TRUE, 2 = FALSE
function _init_arena!()
    empty!(_ARENA)
    push!(_ARENA, SATNode(_HEAD_T, 0, 0, 0))   # uid 1
    push!(_ARENA, SATNode(_HEAD_F, 0, 0, 0))   # uid 2
end
_init_arena!()

const SAT_TRUE  = UInt32(1)
const SAT_FALSE = UInt32(2)

@inline _node(e::SATExpr) = @inbounds _ARENA[e]
@inline _head(e::SATExpr) = @inbounds _ARENA[e].head
@inline _id(e::SATExpr)   = @inbounds _ARENA[e].id
@inline _a(e::SATExpr)    = @inbounds _ARENA[e].a
@inline _b(e::SATExpr)    = @inbounds _ARENA[e].b

function _alloc!(head::UInt8, id::Int32, a::UInt32, b::UInt32)::SATExpr
    push!(_ARENA, SATNode(head, id, a, b))
    UInt32(length(_ARENA))
end

# ── Intern tables ────────────────────────────────────────────────────

const _VAR_INTERN = Dict{Int32, SATExpr}()
const _NOT_INTERN = Dict{UInt32, SATExpr}()
const _AND_INTERN = Dict{Tuple{UInt32,UInt32}, SATExpr}()
const _OR_INTERN  = Dict{Tuple{UInt32,UInt32}, SATExpr}()

# ── SAT result cache: 0 = unknown, 1 = sat, -1 = unsat ──────────────

const _SAT_RESULT = Int8[]

@inline function _known_sat(e::SATExpr)
    h = _head(e)
    h == _HEAD_T && return true
    h == _HEAD_F && return false
    e <= length(_SAT_RESULT) || return nothing
    v = @inbounds _SAT_RESULT[e]
    v == Int8(0) ? nothing : v == Int8(1)
end

function _set_sat!(e::SATExpr, val::Bool)
    if e > length(_SAT_RESULT)
        old_len = length(_SAT_RESULT)
        resize!(_SAT_RESULT, length(_ARENA))
        @inbounds for i in old_len+1:length(_ARENA)
            _SAT_RESULT[i] = Int8(0)
        end
    end
    @inbounds _SAT_RESULT[e] = val ? Int8(1) : Int8(-1)
end

# ── Interning constructors ───────────────────────────────────────────

function sat_var(id::Int)
    id32 = Int32(id)
    get!(_VAR_INTERN, id32) do
        _alloc!(_HEAD_VAR, id32, UInt32(0), UInt32(0))
    end
end

function _make_not(x::SATExpr)
    get!(_NOT_INTERN, x) do
        _alloc!(_HEAD_NOT, Int32(0), x, UInt32(0))
    end
end

function _make_and(a::SATExpr, b::SATExpr)
    get!(_AND_INTERN, (a, b)) do
        _alloc!(_HEAD_AND, Int32(0), a, b)
    end
end

function _make_or(a::SATExpr, b::SATExpr)
    get!(_OR_INTERN, (a, b)) do
        _alloc!(_HEAD_OR, Int32(0), a, b)
    end
end

# ── Smart constructors ───────────────────────────────────────────────

function sat_not(x::SATExpr)
    h = _head(x)
    h == _HEAD_T   && return SAT_FALSE
    h == _HEAD_F   && return SAT_TRUE
    h == _HEAD_NOT && return _a(x)
    k = _known_sat(x)
    k === false && return SAT_TRUE
    _make_not(x)
end

function sat_and(a::SATExpr, b::SATExpr)
    _head(a) == _HEAD_F && return SAT_FALSE
    _head(b) == _HEAD_F && return SAT_FALSE
    _head(a) == _HEAD_T && return b
    _head(b) == _HEAD_T && return a
    _known_sat(a) === false && return SAT_FALSE
    _known_sat(b) === false && return SAT_FALSE
    _make_and(a, b)
end

function sat_or(a::SATExpr, b::SATExpr)
    _head(a) == _HEAD_T && return SAT_TRUE
    _head(b) == _HEAD_T && return SAT_TRUE
    _head(a) == _HEAD_F && return b
    _head(b) == _HEAD_F && return a
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
    h = _head(e)
    h == _HEAD_T   && return nothing
    h == _HEAD_F   && return nothing
    h == _HEAD_VAR && (push!(s, Int(_id(e))); return nothing)
    h == _HEAD_NOT && (_vars!(s, _a(e)); return nothing)
    _vars!(s, _a(e))
    _vars!(s, _b(e))
    return nothing
end

# ── Substitute + simplify under partial assignment ───────────────────

function subst(e::SATExpr, env::Dict{Int,Bool})
    _subst(e, env, Dict{UInt32,SATExpr}())
end

function _subst(e::SATExpr, env::Dict{Int,Bool}, cache::Dict{UInt32,SATExpr})
    h = _head(e)
    h == _HEAD_T && return SAT_TRUE
    h == _HEAD_F && return SAT_FALSE
    if h == _HEAD_VAR
        id = Int(_id(e))
        return haskey(env, id) ? (env[id] ? SAT_TRUE : SAT_FALSE) : e
    end
    haskey(cache, e) && return cache[e]
    r = if h == _HEAD_NOT
        sat_not(_subst(_a(e), env, cache))
    elseif h == _HEAD_AND
        sat_and(_subst(_a(e), env, cache), _subst(_b(e), env, cache))
    else # _HEAD_OR
        sat_or(_subst(_a(e), env, cache), _subst(_b(e), env, cache))
    end
    cache[e] = r
end

# ── Unit propagation ─────────────────────────────────────────────────

function _extract_units!(units::Dict{Int,Bool}, e::SATExpr)
    h = _head(e)
    if h == _HEAD_AND
        _extract_units!(units, _a(e))
        _extract_units!(units, _b(e))
    elseif h == _HEAD_VAR
        id = Int(_id(e))
        units[id] = get(units, id, true)
    elseif h == _HEAD_NOT && _head(_a(e)) == _HEAD_VAR
        id = Int(_id(_a(e)))
        units[id] = get(units, id, false)
    end
    nothing
end

function _propagate(e::SATExpr, env::Dict{Int,Bool})
    while true
        cache = Dict{UInt32,SATExpr}()
        s = _subst(e, env, cache)
        h = _head(s)
        (h == _HEAD_T || h == _HEAD_F) && return s

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
    _set_sat!(e, result)
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
    _set_sat!(e, result)
    result ? env : nothing
end

function _dpll(e::SATExpr, env::Dict{Int,Bool})
    s = _propagate(e, env)
    _head(s) == _HEAD_T && return true
    _head(s) == _HEAD_F && return false

    v = _pick_var(s)
    saved = copy(env)

    env[v] = true
    _dpll(s, env) && return true

    empty!(env); merge!(env, saved)
    env[v] = false
    _dpll(s, env) && return true

    empty!(env); merge!(env, saved)
    return false
end

function _pick_var(e::SATExpr)
    h = _head(e)
    h == _HEAD_VAR && return Int(_id(e))
    h == _HEAD_NOT && return _pick_var(_a(e))
    (h == _HEAD_AND || h == _HEAD_OR) && return _pick_var(_a(e))
    error("_pick_var: no variables in expression")
end

# ── CDCL incremental solver ───────────────────────────────────────────

include("cdcl.jl")

# ── Clear ────────────────────────────────────────────────────────────

function clear_sat!()
    empty!(_VAR_INTERN)
    empty!(_NOT_INTERN)
    empty!(_AND_INTERN)
    empty!(_OR_INTERN)
    empty!(_SAT_RESULT)
    _init_arena!()
end

# ── Display ──────────────────────────────────────────────────────────

function Base.show(io::IO, e::SATExpr)
    h = _head(e)
    if h == _HEAD_T
        print(io, "⊤")
    elseif h == _HEAD_F
        print(io, "⊥")
    elseif h == _HEAD_VAR
        print(io, Int(_id(e)))
    elseif h == _HEAD_NOT
        print(io, "¬")
        ah = _head(_a(e))
        if ah == _HEAD_AND || ah == _HEAD_OR
            print(io, "("); show(io, _a(e)); print(io, ")")
        else
            show(io, _a(e))
        end
    elseif h == _HEAD_AND
        print(io, "("); show(io, _a(e)); print(io, " ∧ "); show(io, _b(e)); print(io, ")")
    elseif h == _HEAD_OR
        print(io, "("); show(io, _a(e)); print(io, " ∨ "); show(io, _b(e)); print(io, ")")
    end
end

end # module
