"""
Lightweight Boolean formula DAG with SAT checking via DPLL + unit propagation.

Usage:
    x, y, z = SATVar(1), SATVar(2), SATVar(3)
    f = (x & y) | ~z
    sat_check(f)          # :sat or :unsat
    sat_assignment(f)     # Dict(:z => false) or nothing
"""
module SAT

export SATExpr, SATVar, SAT_TRUE, SAT_FALSE, sat_check, sat_assignment, sat_vars

# ── Types ──────────────────────────────────────────────────────────────

abstract type SATExpr end

struct LitTrue  <: SATExpr end
struct LitFalse <: SATExpr end
struct SATVar      <: SATExpr; id::Int end
struct Not      <: SATExpr; x::SATExpr end
struct And      <: SATExpr; a::SATExpr; b::SATExpr end
struct Or       <: SATExpr; a::SATExpr; b::SATExpr end

const SAT_TRUE  = LitTrue()
const SAT_FALSE = LitFalse()

# ── Smart constructors (simplify on build) ─────────────────────────────

not(::LitTrue)  = SAT_FALSE
not(::LitFalse) = SAT_TRUE
not(x::Not)     = x.x
not(x::SATExpr) = Not(x)

and(::LitFalse, ::SATExpr) = SAT_FALSE
and(::SATExpr, ::LitFalse) = SAT_FALSE
and(::LitTrue,  b::SATExpr) = b
and(a::SATExpr, ::LitTrue)  = a
and(::LitTrue,  ::LitFalse) = SAT_FALSE
and(::LitFalse, ::LitTrue)  = SAT_FALSE
and(::LitTrue,  ::LitTrue)  = SAT_TRUE
and(::LitFalse, ::LitFalse) = SAT_FALSE
and(a::SATExpr, b::SATExpr) = And(a, b)

or(::LitTrue,  ::SATExpr) = SAT_TRUE
or(::SATExpr, ::LitTrue)  = SAT_TRUE
or(::LitFalse, b::SATExpr) = b
or(a::SATExpr, ::LitFalse) = a
or(::LitTrue,  ::LitFalse) = SAT_TRUE
or(::LitFalse, ::LitTrue)  = SAT_TRUE
or(::LitTrue,  ::LitTrue)  = SAT_TRUE
or(::LitFalse, ::LitFalse) = SAT_FALSE
or(a::SATExpr, b::SATExpr) = Or(a, b)

# ── Operators ──────────────────────────────────────────────────────────

Base.:~(x::SATExpr) = not(x)
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

# ── Substitute + simplify under partial assignment ────────────────────

subst(::LitTrue, _)  = SAT_TRUE
subst(::LitFalse, _) = SAT_FALSE
subst(e::SATVar, env) = haskey(env, e.id) ? (env[e.id] ? SAT_TRUE : SAT_FALSE) : e
subst(e::Not, env) = not(subst(e.x, env))
subst(e::And, env) = and(subst(e.a, env), subst(e.b, env))
subst(e::Or,  env) = or(subst(e.a, env), subst(e.b, env))

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
    while true
        s = subst(e, env)
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
    _dpll(e, Dict{Int,Bool}()) ? :sat : :unsat
end

"""
    sat_assignment(e::SATExpr) → Dict{Int,Bool} or nothing

Returns a sat_assignment assignment, or nothing if unsat.
Unassigned variables are don't-cares.
"""
function sat_assignment(e::SATExpr)
    env = Dict{Int,Bool}()
    _dpll(e, env) ? env : nothing
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
