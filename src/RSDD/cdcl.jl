# ── Literal encoding ──────────────────────────────────────────────────
# Variable v (1-indexed) → positive literal = 2v, negative = 2v+1

@inline mklit(v::Int, pos::Bool)::Int32 = Int32(pos ? 2v : 2v + 1)
@inline litvar(l::Int32)::Int = Int(l >> 1)
@inline litpos(l::Int32)::Bool = (l & 1) == 0
@inline litneg(l::Int32)::Int32 = xor(l, Int32(1))

@inline function litval(assigns::Vector{Int8}, l::Int32)::Int8
    @inbounds v = assigns[litvar(l)]
    v == Int8(0) && return Int8(0)
    litpos(l) ? v : -v
end

const CDCL_LIT_TRUE  = mklit(1, true)   # var 1 is constant true
const CDCL_LIT_FALSE = mklit(1, false)

# ── CDCLSolver ────────────────────────────────────────────────────────

mutable struct CDCLSolver
    n_vars::Int
    clauses::Vector{Vector{Int32}}
    watches::Vector{Vector{Int32}}   # watches[lit - 1]
    assigns::Vector{Int8}            # per variable: 0=undef, 1=true, -1=false
    trail::Vector{Int32}
    trail_lim::Vector{Int}           # trail length at start of each decision level
    reason::Vector{Int32}            # clause index that propagated, 0 = decision
    level::Vector{Int32}             # decision level of assignment
    qhead::Int
    seen::BitVector
    expr_to_lit::Dict{UInt32, Int32} # SATExpr → literal (Tseitin cache)
end

@inline _dlevel(s::CDCLSolver) = length(s.trail_lim)

function CDCLSolver()
    s = CDCLSolver(
        0, Vector{Int32}[], Vector{Int32}[], Int8[], Int32[], Int[], Int32[], Int32[],
        1, BitVector(), Dict{UInt32, Int32}()
    )
    # Var 1 = constant TRUE
    _cdcl_new_var!(s)
    s.assigns[1] = Int8(1)
    s.level[1] = Int32(0)
    push!(s.trail, CDCL_LIT_TRUE)
    return s
end

function _cdcl_new_var!(s::CDCLSolver)::Int
    s.n_vars += 1
    push!(s.assigns, Int8(0))
    push!(s.reason, Int32(0))
    push!(s.level, Int32(-1))
    push!(s.watches, Int32[])  # positive literal watch list
    push!(s.watches, Int32[])  # negative literal watch list
    return s.n_vars
end

function _cdcl_add_clause!(s::CDCLSolver, lits::Vector{Int32})::Int32
    push!(s.clauses, lits)
    ci = Int32(length(s.clauses))
    if length(lits) >= 2
        push!(s.watches[Int(lits[1]) - 1], ci)
        push!(s.watches[Int(lits[2]) - 1], ci)
    end
    return ci
end

function _cdcl_enqueue!(s::CDCLSolver, lit::Int32, reason::Int32 = Int32(0))::Bool
    v = litvar(lit)
    val = litpos(lit) ? Int8(1) : Int8(-1)
    @inbounds cur = s.assigns[v]
    cur != Int8(0) && return cur == val
    @inbounds s.assigns[v] = val
    @inbounds s.level[v] = Int32(_dlevel(s))
    @inbounds s.reason[v] = reason
    push!(s.trail, lit)
    return true
end

function _cdcl_backtrack!(s::CDCLSolver, target_level::Int)
    while _dlevel(s) > target_level
        prev_len = s.trail_lim[end]
        for i in length(s.trail):-1:(prev_len + 1)
            @inbounds s.assigns[litvar(s.trail[i])] = Int8(0)
        end
        resize!(s.trail, prev_len)
        pop!(s.trail_lim)
    end
    s.qhead = min(s.qhead, length(s.trail) + 1)
end

# ── BCP with watched literals ────────────────────────────────────────

function _cdcl_propagate!(s::CDCLSolver)::Int32
    while s.qhead <= length(s.trail)
        @inbounds p = s.trail[s.qhead]
        s.qhead += 1

        falsified = litneg(p)
        wl = s.watches[Int(falsified) - 1]
        j = 0; i = 1

        while i <= length(wl)
            @inbounds ci = wl[i]
            @inbounds clause = s.clauses[ci]

            # Ensure falsified literal is at position 2
            if clause[1] == falsified
                clause[1], clause[2] = clause[2], clause[1]
            end

            @inbounds other = clause[1]
            if litval(s.assigns, other) == Int8(1)
                j += 1; @inbounds wl[j] = ci; i += 1; continue
            end

            # Find replacement watched literal
            found = false
            for k in 3:length(clause)
                @inbounds lk = clause[k]
                if litval(s.assigns, lk) != Int8(-1)
                    clause[2], clause[k] = clause[k], clause[2]
                    push!(s.watches[Int(clause[2]) - 1], ci)
                    found = true; break
                end
            end
            if found; i += 1; continue; end

            # No replacement — clause is unit or conflicting
            j += 1; @inbounds wl[j] = ci

            if litval(s.assigns, other) == Int8(-1)
                # Conflict — copy remaining watches, return
                for ii in (i+1):length(wl)
                    j += 1; @inbounds wl[j] = wl[ii]
                end
                resize!(wl, j)
                return ci
            end

            # Unit propagation
            _cdcl_enqueue!(s, other, ci)
            i += 1
        end
        resize!(wl, j)
    end
    return Int32(0)
end

# ── Conflict analysis (1UIP) ─────────────────────────────────────────

function _cdcl_analyze!(s::CDCLSolver, conflict::Int32)::Tuple{Vector{Int32}, Int}
    if length(s.seen) < s.n_vars
        resize!(s.seen, s.n_vars)
    end
    fill!(s.seen, false)

    counter = 0; btlevel = 0
    learned = Int32[]
    p = Int32(0)
    clause_idx = conflict
    idx = length(s.trail)

    while true
        @inbounds for l in s.clauses[clause_idx]
            l == p && continue
            v = litvar(l)
            @inbounds s.seen[v] && continue
            @inbounds s.seen[v] = true
            @inbounds lv = s.level[v]
            if lv == _dlevel(s)
                counter += 1
            elseif lv > 0
                push!(learned, l)
                btlevel = max(btlevel, Int(lv))
            end
            # level 0 literals are always assigned — omit from learned clause
        end

        counter -= 1
        while true
            @inbounds p = s.trail[idx]
            idx -= 1
            @inbounds s.seen[litvar(p)] && break
        end
        @inbounds s.seen[litvar(p)] = false
        counter == 0 && break
        @inbounds clause_idx = s.reason[litvar(p)]
    end

    pushfirst!(learned, litneg(p))
    return learned, btlevel
end

# ── Variable selection ────────────────────────────────────────────────

function _cdcl_pick_var(s::CDCLSolver)::Int
    for v in 2:s.n_vars  # skip var 1 (constant true)
        @inbounds s.assigns[v] == Int8(0) && return v
    end
    return 0
end

# ── Tseitin encoding ─────────────────────────────────────────────────

function _tseitin!(s::CDCLSolver, e::SATExpr)::Int32
    haskey(s.expr_to_lit, e) && return s.expr_to_lit[e]

    h = _head(e)

    lit = if h == _HEAD_T
        CDCL_LIT_TRUE
    elseif h == _HEAD_F
        CDCL_LIT_FALSE
    elseif h == _HEAD_VAR
        mklit(_cdcl_new_var!(s), true)
    elseif h == _HEAD_NOT
        litneg(_tseitin!(s, _a(e)))
    elseif h == _HEAD_AND
        al = _tseitin!(s, _a(e)); bl = _tseitin!(s, _b(e))
        if al == CDCL_LIT_TRUE;     bl
        elseif bl == CDCL_LIT_TRUE; al
        elseif al == CDCL_LIT_FALSE || bl == CDCL_LIT_FALSE; CDCL_LIT_FALSE
        elseif al == bl;            al
        elseif al == litneg(bl);    CDCL_LIT_FALSE
        else
            g = _cdcl_new_var!(s); gl = mklit(g, true)
            _cdcl_add_clause!(s, Int32[litneg(gl), al])
            _cdcl_add_clause!(s, Int32[litneg(gl), bl])
            _cdcl_add_clause!(s, Int32[gl, litneg(al), litneg(bl)])
            gl
        end
    elseif h == _HEAD_OR
        al = _tseitin!(s, _a(e)); bl = _tseitin!(s, _b(e))
        if al == CDCL_LIT_TRUE || bl == CDCL_LIT_TRUE; CDCL_LIT_TRUE
        elseif al == CDCL_LIT_FALSE; bl
        elseif bl == CDCL_LIT_FALSE; al
        elseif al == bl;             al
        elseif al == litneg(bl);     CDCL_LIT_TRUE
        else
            g = _cdcl_new_var!(s); gl = mklit(g, true)
            _cdcl_add_clause!(s, Int32[litneg(gl), al, bl])
            _cdcl_add_clause!(s, Int32[gl, litneg(al)])
            _cdcl_add_clause!(s, Int32[gl, litneg(bl)])
            gl
        end
    else
        error("_tseitin!: unknown head $h")
    end

    s.expr_to_lit[e] = lit
    return lit
end

# ── High-level interface ──────────────────────────────────────────────

"""
    cdcl_solver_from(base::SATExpr) → CDCLSolver or :sat or :unsat

Build a CDCL solver with `base` as permanent clauses. Returns the solver
for use with `cdcl_check_assuming!`, or a symbol if the base is trivially
sat/unsat.
"""
function cdcl_solver_from(base::SATExpr)::Union{CDCLSolver, Symbol}
    _head(base) == _HEAD_T && return :sat
    _head(base) == _HEAD_F && return :unsat
    k = _known_sat(base)
    k === false && return :unsat

    s = CDCLSolver()
    root = _tseitin!(s, base)

    root == CDCL_LIT_TRUE  && return :sat
    root == CDCL_LIT_FALSE && (_set_sat!(base, false); return :unsat)

    # Assert root and propagate (qhead=1 ensures var 1 + root are processed)
    _cdcl_add_clause!(s, Int32[root])
    _cdcl_enqueue!(s, root)

    if _cdcl_propagate!(s) != Int32(0)
        _set_sat!(base, false)
        return :unsat
    end

    return s
end

"""
    cdcl_check_assuming!(s::CDCLSolver, additional::SATExpr) → :sat or :unsat

Check satisfiability of `base ∧ additional`. Learned clauses from this
call persist in the solver and benefit future calls.
"""
function cdcl_check_assuming!(s::CDCLSolver, additional::SATExpr)::Symbol
    _head(additional) == _HEAD_F && return :unsat
    _head(additional) == _HEAD_T && return :sat
    k = _known_sat(additional)
    k === false && return :unsat

    @assert _dlevel(s) == 0

    add_lit = _tseitin!(s, additional)
    add_lit == CDCL_LIT_FALSE && return :unsat
    add_lit == CDCL_LIT_TRUE  && return :sat

    # Reprocess level-0 trail so BCP picks up newly added Tseitin clauses
    s.qhead = 1
    if _cdcl_propagate!(s) != Int32(0)
        return :unsat
    end

    # Assumption variable may already be forced at level 0
    v = litvar(add_lit)
    if s.assigns[v] != Int8(0)
        return litval(s.assigns, add_lit) == Int8(1) ? :sat : :unsat
    end

    # Assert assumption at level 1
    push!(s.trail_lim, length(s.trail))
    _cdcl_enqueue!(s, add_lit)

    result = _cdcl_solve_with_assumption!(s, add_lit)
    _cdcl_backtrack!(s, 0)
    return result
end

"""
    cdcl_fork(parent::CDCLSolver, additional::SATExpr) → CDCLSolver

Create a child solver that inherits all of `parent`'s clauses and learned
clauses, with `additional` permanently asserted at level 0.
Call only after `cdcl_check_assuming!` confirmed the combination is SAT.
"""
function cdcl_fork(parent::CDCLSolver, additional::SATExpr)::CDCLSolver
    child = CDCLSolver(
        parent.n_vars,
        [copy(c) for c in parent.clauses],
        [copy(w) for w in parent.watches],
        copy(parent.assigns),
        copy(parent.trail),
        copy(parent.trail_lim),
        copy(parent.reason),
        copy(parent.level),
        parent.qhead,
        copy(parent.seen),
        copy(parent.expr_to_lit),
    )

    add_lit = _tseitin!(child, additional)
    (add_lit == CDCL_LIT_TRUE || add_lit == CDCL_LIT_FALSE) && return child

    v = litvar(add_lit)
    child.assigns[v] != Int8(0) && return child  # already forced at level 0

    child.qhead = 1  # reprocess trail to pick up any new Tseitin clauses
    _cdcl_enqueue!(child, add_lit)
    _cdcl_propagate!(child)
    return child
end

function _cdcl_solve_with_assumption!(s::CDCLSolver, assumption::Int32)::Symbol
    while true
        conflict = _cdcl_propagate!(s)

        if conflict != Int32(0)
            if _dlevel(s) == 0
                return :unsat
            end

            learned, btlevel = _cdcl_analyze!(s, conflict)
            _cdcl_backtrack!(s, btlevel)

            ci = _cdcl_add_clause!(s, learned)
            if length(learned) == 1
                _cdcl_enqueue!(s, learned[1])
            else
                _cdcl_enqueue!(s, learned[1], ci)
            end

            # If backjumped to level 0, propagate new facts, then re-assert assumption
            if _dlevel(s) == 0
                if _cdcl_propagate!(s) != Int32(0)
                    return :unsat
                end
                v = litvar(assumption)
                if s.assigns[v] != Int8(0)
                    return litval(s.assigns, assumption) == Int8(1) ? :sat : :unsat
                end
                push!(s.trail_lim, length(s.trail))
                _cdcl_enqueue!(s, assumption)
            end
        else
            v = _cdcl_pick_var(s)
            v == 0 && return :sat
            push!(s.trail_lim, length(s.trail))
            _cdcl_enqueue!(s, mklit(v, true))
        end
    end
end
