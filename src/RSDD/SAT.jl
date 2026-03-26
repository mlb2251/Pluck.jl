"""
Lightweight Boolean formula DAG with SAT checking via DPLL + unit propagation.
Hash-consed nodes ensure structural sharing; memoized substitution avoids
re-traversing shared subDAGs.

Usage:
    x, y, z = SATVar(1), SATVar(2), SATVar(3)
    f = (x & y) | ~z
    sat_check(f)          # :sat or :unsat
    sat_assignment(f)     # Dict(3 => false) or nothing
"""
module SAT

export SATExpr, SATVar, SAT_TRUE, SAT_FALSE, sat_check, sat_assignment, sat_vars, clear_sat!

# ── Types (hash-consed) ──────────────────────────────────────────────

abstract type SATExpr end

struct LitTrue  <: SATExpr end
struct LitFalse <: SATExpr end

struct SATVar <: SATExpr
    id::Int
    function SATVar(id::Int)
        e = new(id)
        get!(_INTERN, e, e)
    end
end

struct Not <: SATExpr
    x::SATExpr
    function Not(x::SATExpr)
        e = new(x)
        get!(_INTERN, e, e)
    end
end

struct And <: SATExpr
    a::SATExpr
    b::SATExpr
    function And(a::SATExpr, b::SATExpr)
        e = new(a, b)
        get!(_INTERN, e, e)
    end
end

struct Or <: SATExpr
    a::SATExpr
    b::SATExpr
    function Or(a::SATExpr, b::SATExpr)
        e = new(a, b)
        get!(_INTERN, e, e)
    end
end

const SAT_TRUE  = LitTrue()
const SAT_FALSE = LitFalse()

# ── Equality, hashing & intern table ────────────────────────────────

Base.:(==)(::LitTrue, ::LitTrue)   = true
Base.:(==)(::LitFalse, ::LitFalse) = true
Base.:(==)(a::SATVar, b::SATVar)   = a.id == b.id
Base.:(==)(a::Not, b::Not)         = a.x === b.x
Base.:(==)(a::And, b::And)         = a.a === b.a && a.b === b.b
Base.:(==)(a::Or, b::Or)           = a.a === b.a && a.b === b.b

Base.hash(::LitTrue, h::UInt)    = hash(:LitTrue, h)
Base.hash(::LitFalse, h::UInt)   = hash(:LitFalse, h)
Base.hash(e::SATVar, h::UInt)    = hash(e.id, hash(:SATVar, h))
Base.hash(e::Not, h::UInt)       = hash(e.x, hash(:Not, h))
Base.hash(e::And, h::UInt)       = hash(e.b, hash(e.a, hash(:And, h)))
Base.hash(e::Or, h::UInt)        = hash(e.b, hash(e.a, hash(:Or, h)))

const _INTERN = Dict{SATExpr, SATExpr}()

# Per-node SAT result cache. Keyed on objectid (safe because hash-consed).
# true = satisfiable, false = unsatisfiable.
const _SAT_RESULT = Dict{UInt, Bool}()

# Query cached results (returns nothing if unknown)
_known_sat(e::LitTrue)  = true
_known_sat(e::LitFalse) = false
_known_sat(e::SATExpr)  = get(_SAT_RESULT, objectid(e), nothing)

function clear_sat!()
    empty!(_INTERN)
    empty!(_SAT_RESULT)
end

# ── Smart constructors (simplify on build) ─────────────────────────────

not(::LitTrue)  = SAT_FALSE
not(::LitFalse) = SAT_TRUE
not(x::Not)     = x.x
function not(x::SATExpr)
    k = _known_sat(x)
    # UNSAT → negation is tautology; tautology check: ¬x unsat means x is tautology
    k === false && return SAT_TRUE
    Not(x)
end

and(::LitFalse, ::SATExpr) = SAT_FALSE
and(::SATExpr, ::LitFalse) = SAT_FALSE
and(::LitTrue,  b::SATExpr) = b
and(a::SATExpr, ::LitTrue)  = a
and(::LitTrue,  ::LitFalse) = SAT_FALSE
and(::LitFalse, ::LitTrue)  = SAT_FALSE
and(::LitTrue,  ::LitTrue)  = SAT_TRUE
and(::LitFalse, ::LitFalse) = SAT_FALSE
function and(a::SATExpr, b::SATExpr)
    # If either operand is known UNSAT, conjunction is UNSAT
    _known_sat(a) === false && return SAT_FALSE
    _known_sat(b) === false && return SAT_FALSE
    And(a, b)
end

or(::LitTrue,  ::SATExpr) = SAT_TRUE
or(::SATExpr, ::LitTrue)  = SAT_TRUE
or(::LitFalse, b::SATExpr) = b
or(a::SATExpr, ::LitFalse) = a
or(::LitTrue,  ::LitFalse) = SAT_TRUE
or(::LitFalse, ::LitTrue)  = SAT_TRUE
or(::LitTrue,  ::LitTrue)  = SAT_TRUE
or(::LitFalse, ::LitFalse) = SAT_FALSE
function or(a::SATExpr, b::SATExpr)
    # If either operand is a known tautology (¬x is known UNSAT), disjunction is tautology
    # We check: if not(a) was previously found UNSAT, then a is a tautology
    _known_sat(a) === false && return b   # a is UNSAT, so a|b = b
    _known_sat(b) === false && return a   # b is UNSAT, so a|b = a
    Or(a, b)
end

# ── Operators ──────────────────────────────────────────────────────────

Base.:~(x::SATExpr) = not(x)
Base.:!(x::SATExpr) = not(x)
Base.:&(a::SATExpr, b::SATExpr) = and(a, b)
Base.:|(a::SATExpr, b::SATExpr) = or(a, b)

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
# The cache is keyed on objectid, which is safe because nodes are hash-consed
# (structurally equal ⟹ identical object).

function subst(e::SATExpr, env::Dict{Int,Bool})
    _subst(e, env, Dict{UInt,SATExpr}())
end

_subst(e::LitTrue, _, _)  = SAT_TRUE
_subst(e::LitFalse, _, _) = SAT_FALSE
function _subst(e::SATVar, env, _)
    haskey(env, e.id) ? (env[e.id] ? SAT_TRUE : SAT_FALSE) : e
end
function _subst(e::Not, env, cache)
    oid = objectid(e)
    haskey(cache, oid) && return cache[oid]
    r = not(_subst(e.x, env, cache))
    cache[oid] = r
end
function _subst(e::And, env, cache)
    oid = objectid(e)
    haskey(cache, oid) && return cache[oid]
    r = and(_subst(e.a, env, cache), _subst(e.b, env, cache))
    cache[oid] = r
end
function _subst(e::Or, env, cache)
    oid = objectid(e)
    haskey(cache, oid) && return cache[oid]
    r = or(_subst(e.a, env, cache), _subst(e.b, env, cache))
    cache[oid] = r
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
    cache = Dict{UInt,SATExpr}()
    while true
        empty!(cache)  # env changed, invalidate
        s = _subst(e, env, cache)
        (s isa LitTrue || s isa LitFalse) && return s

        units = Dict{Int,Bool}()
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
    sat_check(e::SATExpr) → :sat or :unsat
"""
function sat_check(e::SATExpr)
    oid = objectid(e)
    haskey(_SAT_RESULT, oid) && return _SAT_RESULT[oid] ? :sat : :unsat
    result = _dpll(e, Dict{Int,Bool}())
    _SAT_RESULT[oid] = result
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
    _SAT_RESULT[objectid(e)] = result
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

    # Undo and fail
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

# ── Tests ────────────────────────────────────────────────────────────

function test()
    pass = 0
    fail = 0
    function t(name, cond)
        if cond
            pass += 1
        else
            fail += 1
            println("FAIL: $name")
        end
    end

    x, y, z = SATVar(1), SATVar(2), SATVar(3)

    # Hash-consing
    t("SATVar hash-cons", SATVar(1) === SATVar(1))
    t("And hash-cons", And(x, y) === And(x, y))
    t("Or hash-cons", Or(x, y) === Or(x, y))
    t("Not hash-cons", Not(x) === Not(x))

    # Smart constructors
    t("and(SAT_FALSE, x) == SAT_FALSE", and(SAT_FALSE, x) === SAT_FALSE)
    t("and(x, SAT_FALSE) == SAT_FALSE", and(x, SAT_FALSE) === SAT_FALSE)
    t("and(SAT_TRUE, x) == x",     and(SAT_TRUE, x) === x)
    t("and(x, SAT_TRUE) == x",     and(x, SAT_TRUE) === x)
    t("or(SAT_TRUE, x) == SAT_TRUE",   or(SAT_TRUE, x) === SAT_TRUE)
    t("or(x, SAT_TRUE) == SAT_TRUE",   or(x, SAT_TRUE) === SAT_TRUE)
    t("or(SAT_FALSE, x) == x",     or(SAT_FALSE, x) === x)
    t("or(x, SAT_FALSE) == x",     or(x, SAT_FALSE) === x)
    t("not(SAT_TRUE) == SAT_FALSE",    not(SAT_TRUE) === SAT_FALSE)
    t("not(SAT_FALSE) == SAT_TRUE",    not(SAT_FALSE) === SAT_TRUE)
    t("not(not(x)) == x",     not(not(x)) === x)

    # Operators
    t("~SAT_TRUE == SAT_FALSE", (~SAT_TRUE) === SAT_FALSE)
    t("x & SAT_FALSE == SAT_FALSE", (x & SAT_FALSE) === SAT_FALSE)
    t("x | SAT_TRUE == SAT_TRUE",  (x | SAT_TRUE) === SAT_TRUE)

    # sat_vars
    t("sat_vars(x & y | z)", sat_vars(x & y | z) == Set([1, 2, 3]))
    t("sat_vars(SAT_TRUE)", sat_vars(SAT_TRUE) == Set{Int}())
    t("sat_vars(~x)", sat_vars(~x) == Set([1]))

    # Trivial sat/unsat
    t("SAT_TRUE is sat",  sat_check(SAT_TRUE) == :sat)
    t("SAT_FALSE is unsat", sat_check(SAT_FALSE) == :unsat)

    # Single var
    t("x is sat", sat_check(x) == :sat)
    t("~x is sat", sat_check(~x) == :sat)

    # x & ~x is unsat
    t("x & ~x unsat", sat_check(x & ~x) == :unsat)

    # x | ~x is tautology
    t("x | ~x sat", sat_check(x | ~x) == :sat)

    # (x | y) & (~x | y) & (x | ~y) & (~x | ~y) is unsat
    t("all 2-clauses unsat", sat_check((x | y) & (~x | y) & (x | ~y) & (~x | ~y)) == :unsat)

    # (x | y) & (~x | y) is sat (y=true)
    f = (x | y) & (~x | y)
    t("(x|y)&(~x|y) sat", sat_check(f) == :sat)
    env = sat_assignment(f)
    t("sat_assignment assigns y=true", env !== nothing && env[2] == true)

    # 3-var sat
    f3 = (x | y | z) & (~x | ~y) & (~y | ~z) & (~x | ~z)
    t("3-var sat", sat_check(f3) == :sat)
    env3 = sat_assignment(f3)
    t("3-var assignment valid", env3 !== nothing)

    # Verify sat_assignment assignment by substitution
    if env3 !== nothing
        # Fill in don't-cares with false
        for v in [1, 2, 3]
            haskey(env3, v) || (env3[v] = false)
        end
        t("3-var subst to SAT_TRUE", subst(f3, env3) === SAT_TRUE)
    end

    # sat_assignment returns nothing for unsat
    t("sat_assignment unsat -> nothing", sat_assignment(x & ~x) === nothing)

    # SAT result propagation into constructors
    unsat_expr = (x & ~x)  # known unsat after check above
    t("and(unsat, y) == SAT_FALSE", and(unsat_expr, y) === SAT_FALSE)
    t("and(y, unsat) == SAT_FALSE", and(y, unsat_expr) === SAT_FALSE)
    t("or(unsat, y) == y",  or(unsat_expr, y) === y)
    t("not(unsat) == SAT_TRUE", not(unsat_expr) === SAT_TRUE)

    # Display
    t("show SATVar",  sprint(show, x) == "1")
    t("show And",  sprint(show, x & y) == "(1 ∧ 2)")
    t("show Or",   sprint(show, x | y) == "(1 ∨ 2)")
    t("show Not",  sprint(show, ~x) == "¬1")
    t("show Not(And)", sprint(show, ~(x & y)) == "¬((1 ∧ 2))")
    t("show SAT_TRUE",  sprint(show, SAT_TRUE) == "⊤")
    t("show SAT_FALSE", sprint(show, SAT_FALSE) == "⊥")

    println("BoolSAT tests: $pass passed, $fail failed")
    fail == 0
end

end # module
