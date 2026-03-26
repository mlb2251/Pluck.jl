"""
Lightweight Boolean formula DAG with SAT checking via CDCL.
Arena-based: all nodes live in a flat Vector, referenced by UInt32 index.
No heap allocation per node, no GC pressure.
"""
module SAT

using Printf

export SATExpr, sat_var, SAT_TRUE, SAT_FALSE, clear_sat!, sat_not, sat_and, sat_or,
       CDCLSolver, cdcl_solver_from, cdcl_check_assuming!, cdcl_new_selector!,
       CDCLStats, get_cdcl_stats, clear_cdcl_stats!, show_cdcl_stats

# ── Stats ────────────────────────────────────────────────────────────

mutable struct CDCLStats
    check_calls::Int        # cdcl_check_assuming! calls
    check_time::Float64     # total time in cdcl_check_assuming!
    propagate_calls::Int    # _cdcl_propagate! calls
    propagate_time::Float64
    conflicts::Int          # number of conflicts
    decisions::Int          # number of decisions (pick_var)
    selector_calls::Int     # cdcl_new_selector! calls
    selector_time::Float64  # total time in cdcl_new_selector!
    solver_from_calls::Int  # cdcl_solver_from calls
    solver_from_time::Float64 # total time in cdcl_solver_from
    reprocess_time::Float64 # time in qhead=1 level-0 reprocessing
    n_vars_at_check::Int    # sum of n_vars at each check (for avg)
    n_clauses_at_check::Int # sum of n_clauses at each check (for avg)
    assumption_depth::Int   # sum of assumption stack length at each check (for avg)
end

const _cdcl_stats = CDCLStats(0, 0.0, 0, 0.0, 0, 0, 0, 0.0, 0, 0.0, 0.0, 0, 0, 0)

function get_cdcl_stats()
    return _cdcl_stats
end

function clear_cdcl_stats!()
    _cdcl_stats.check_calls = 0
    _cdcl_stats.check_time = 0.0
    _cdcl_stats.propagate_calls = 0
    _cdcl_stats.propagate_time = 0.0
    _cdcl_stats.conflicts = 0
    _cdcl_stats.decisions = 0
    _cdcl_stats.selector_calls = 0
    _cdcl_stats.selector_time = 0.0
    _cdcl_stats.solver_from_calls = 0
    _cdcl_stats.solver_from_time = 0.0
    _cdcl_stats.reprocess_time = 0.0
    _cdcl_stats.n_vars_at_check = 0
    _cdcl_stats.n_clauses_at_check = 0
    _cdcl_stats.assumption_depth = 0
end

function Base.show(io::IO, s::CDCLStats)
    show_cdcl_stats(io, s)
end

function show_cdcl_stats(io::IO=stdout, s::CDCLStats=_cdcl_stats)
    n = s.check_calls
    avg_vars = n > 0 ? s.n_vars_at_check / n : 0.0
    avg_clauses = n > 0 ? s.n_clauses_at_check / n : 0.0
    avg_depth = n > 0 ? s.assumption_depth / n : 0.0
    other_time = s.check_time - s.propagate_time - s.reprocess_time
    props_per_check = n > 0 ? s.propagate_calls / n : 0.0

    _fmt(t) = @sprintf("%.3fs", t)
    _pct(t) = s.check_time > 0 ? @sprintf("%.0f%%", 100 * t / s.check_time) : "-"

    println(io, "CDCL Stats")
    println(io, "──────────────────────────────────────")
    println(io, "  Calls")
    println(io, "    check_assuming!     $(n)")
    println(io, "    new_selector!       $(s.selector_calls)")
    println(io, "    solver_from         $(s.solver_from_calls)")
    println(io, "  Search")
    println(io, "    propagations        $(s.propagate_calls)  ($(@sprintf("%.1f", props_per_check))/check)")
    println(io, "    conflicts           $(s.conflicts)")
    println(io, "    decisions           $(s.decisions)")
    total_time = s.check_time + s.selector_time + s.solver_from_time
    _pct_total(t) = total_time > 0 ? @sprintf("%.0f%%", 100 * t / total_time) : "-"

    println(io, "  Time breakdown (total $(_fmt(total_time)))")
    println(io, "    check_assuming!     $(_fmt(s.check_time))  $(_pct_total(s.check_time))")
    println(io, "      propagation       $(_fmt(s.propagate_time))")
    println(io, "      L0 reprocessing   $(_fmt(s.reprocess_time))")
    println(io, "      other (decide+bt) $(_fmt(other_time))")
    println(io, "    new_selector!       $(_fmt(s.selector_time))  $(_pct_total(s.selector_time))")
    println(io, "    solver_from         $(_fmt(s.solver_from_time))  $(_pct_total(s.solver_from_time))")
    println(io, "  Solver size (avg per check)")
    println(io, "    variables           $(@sprintf("%.1f", avg_vars))")
    println(io, "    clauses             $(@sprintf("%.1f", avg_clauses))")
    println(io, "    assumption depth    $(@sprintf("%.1f", avg_depth))")
    println(io, "──────────────────────────────────────")
end

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

# ── CDCL incremental solver ─────────────────────────────────────────

# Literal encoding: variable v (1-indexed) → positive literal = 2v, negative = 2v+1

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
    active_buf::Vector{Int32}        # reusable buffer for filtering assumptions
    # VSIDS
    activity::Vector{Float64}
    var_heap::Vector{Int}            # binary max-heap of variable indices
    heap_pos::Vector{Int}            # position of each variable in heap (0 = not in heap)
    var_inc::Float64                 # current activity bump amount
end

const VSIDS_DECAY = 0.95

@inline _dlevel(s::CDCLSolver) = length(s.trail_lim)

function CDCLSolver()
    s = CDCLSolver(
        0, Vector{Int32}[], Vector{Int32}[], Int8[], Int32[], Int[], Int32[], Int32[],
        1, BitVector(), Dict{UInt32, Int32}(), Int32[],
        Float64[], Int[], Int[], 1.0
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
    push!(s.activity, 0.0)
    push!(s.heap_pos, 0)
    _vsids_insert!(s, s.n_vars)
    return s.n_vars
end

# ── VSIDS heap ───────────────────────────────────────────────────────

@inline _heap_gt(s::CDCLSolver, a::Int, b::Int) = @inbounds s.activity[a] > s.activity[b]

function _vsids_insert!(s::CDCLSolver, v::Int)
    @inbounds s.heap_pos[v] != 0 && return
    push!(s.var_heap, v)
    pos = length(s.var_heap)
    @inbounds s.heap_pos[v] = pos
    _heap_up!(s, pos)
end

function _heap_up!(s::CDCLSolver, pos::Int)
    @inbounds v = s.var_heap[pos]
    while pos > 1
        parent_pos = pos >> 1
        @inbounds pv = s.var_heap[parent_pos]
        !_heap_gt(s, v, pv) && break
        @inbounds s.var_heap[pos] = pv
        @inbounds s.heap_pos[pv] = pos
        pos = parent_pos
    end
    @inbounds s.var_heap[pos] = v
    @inbounds s.heap_pos[v] = pos
end

function _heap_down!(s::CDCLSolver, pos::Int)
    n = length(s.var_heap)
    @inbounds v = s.var_heap[pos]
    while true
        child = pos << 1
        child > n && break
        if child + 1 <= n && _heap_gt(s, s.var_heap[child + 1], s.var_heap[child])
            child += 1
        end
        @inbounds !_heap_gt(s, s.var_heap[child], v) && break
        @inbounds s.var_heap[pos] = s.var_heap[child]
        @inbounds s.heap_pos[s.var_heap[child]] = pos
        pos = child
    end
    @inbounds s.var_heap[pos] = v
    @inbounds s.heap_pos[v] = pos
end

function _vsids_pop!(s::CDCLSolver)::Int
    while !isempty(s.var_heap)
        v = s.var_heap[1]
        n = length(s.var_heap)
        if n == 1
            pop!(s.var_heap)
            @inbounds s.heap_pos[v] = 0
        else
            @inbounds last = s.var_heap[n]
            pop!(s.var_heap)
            @inbounds s.var_heap[1] = last
            @inbounds s.heap_pos[last] = 1
            @inbounds s.heap_pos[v] = 0
            _heap_down!(s, 1)
        end
        @inbounds s.assigns[v] == Int8(0) && return v
    end
    return 0
end

function _vsids_bump!(s::CDCLSolver, v::Int)
    @inbounds s.activity[v] += s.var_inc
    if @inbounds s.activity[v] > 1e100
        for i in 1:s.n_vars
            @inbounds s.activity[i] *= 1e-100
        end
        s.var_inc *= 1e-100
    end
    @inbounds if s.heap_pos[v] != 0
        _heap_up!(s, s.heap_pos[v])
    end
end

@inline function _vsids_decay!(s::CDCLSolver)
    s.var_inc /= VSIDS_DECAY
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
            @inbounds v = litvar(s.trail[i])
            @inbounds s.assigns[v] = Int8(0)
            _vsids_insert!(s, v)
        end
        resize!(s.trail, prev_len)
        pop!(s.trail_lim)
    end
    s.qhead = min(s.qhead, length(s.trail) + 1)
end

# ── BCP with watched literals ────────────────────────────────────────

function _cdcl_propagate!(s::CDCLSolver)::Int32
    _cdcl_stats.propagate_calls += 1
    t_start = time_ns()
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
                _cdcl_stats.propagate_time += (time_ns() - t_start) / 1e9
                return ci
            end

            # Unit propagation
            _cdcl_enqueue!(s, other, ci)
            i += 1
        end
        resize!(wl, j)
    end
    _cdcl_stats.propagate_time += (time_ns() - t_start) / 1e9
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
            _vsids_bump!(s, v)
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

@inline _cdcl_pick_var(s::CDCLSolver)::Int = _vsids_pop!(s)

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
    t_start = time_ns()
    _cdcl_stats.solver_from_calls += 1
    _head(base) == _HEAD_T && return :sat
    _head(base) == _HEAD_F && return :unsat
    k = _known_sat(base)
    k === false && return :unsat

    s = CDCLSolver()
    root = _tseitin!(s, base)

    root == CDCL_LIT_TRUE  && (_cdcl_stats.solver_from_time += (time_ns() - t_start) / 1e9; return :sat)
    root == CDCL_LIT_FALSE && (_set_sat!(base, false); _cdcl_stats.solver_from_time += (time_ns() - t_start) / 1e9; return :unsat)

    # Assert root and propagate (qhead=1 ensures var 1 + root are processed)
    _cdcl_add_clause!(s, Int32[root])
    _cdcl_enqueue!(s, root)

    if _cdcl_propagate!(s) != Int32(0)
        _set_sat!(base, false)
        _cdcl_stats.solver_from_time += (time_ns() - t_start) / 1e9
        return :unsat
    end

    _cdcl_stats.solver_from_time += (time_ns() - t_start) / 1e9
    return s
end

"""
    cdcl_new_selector!(s::CDCLSolver, guard_expr::SATExpr) → Int32

Create a selector variable `sel` and add the clause `(¬sel ∨ tseitin(guard))`.
When `sel` is assumed true it forces the guard; when unassumed the guard is
unconstrained. Returns the selector literal (positive), or 0 if the guard
is trivially true (no assumption needed), or -1 if trivially false.
"""
function cdcl_new_selector!(s::CDCLSolver, guard_expr::SATExpr)::Int32
    t_start = time_ns()
    _cdcl_stats.selector_calls += 1
    guard_lit = _tseitin!(s, guard_expr)
    guard_lit == CDCL_LIT_TRUE  && (_cdcl_stats.selector_time += (time_ns() - t_start) / 1e9; return Int32(0))   # trivially true
    guard_lit == CDCL_LIT_FALSE && (_cdcl_stats.selector_time += (time_ns() - t_start) / 1e9; return Int32(-1))   # trivially false
    sel_var = _cdcl_new_var!(s)
    sel_lit = mklit(sel_var, true)
    _cdcl_add_clause!(s, Int32[litneg(sel_lit), guard_lit])  # sel => guard
    _cdcl_stats.selector_time += (time_ns() - t_start) / 1e9
    return sel_lit
end

"""
    cdcl_check_assuming!(s::CDCLSolver, assumptions::Vector{Int32}) → :sat or :unsat

Check satisfiability of the base formula under all assumption literals.
Learned clauses persist in the solver and benefit future calls.
"""
function cdcl_check_assuming!(s::CDCLSolver, assumptions::Vector{Int32})::Symbol
    t_start = time_ns()
    @assert _dlevel(s) == 0

    _cdcl_stats.check_calls += 1
    _cdcl_stats.n_vars_at_check += s.n_vars
    _cdcl_stats.n_clauses_at_check += length(s.clauses)
    _cdcl_stats.assumption_depth += length(assumptions)

    # Reprocess level-0 trail so BCP picks up any newly added Tseitin clauses
    t_repro = time_ns()
    s.qhead = 1
    if _cdcl_propagate!(s) != Int32(0)
        _cdcl_stats.check_time += (time_ns() - t_start) / 1e9
        return :unsat
    end
    _cdcl_stats.reprocess_time += (time_ns() - t_repro) / 1e9

    # Filter assumptions into reusable buffer (no allocation)
    empty!(s.active_buf)
    for lit in assumptions
        lit == CDCL_LIT_TRUE && continue
        if lit == CDCL_LIT_FALSE
            _cdcl_stats.check_time += (time_ns() - t_start) / 1e9
            return :unsat
        end
        v = litvar(lit)
        if s.assigns[v] != Int8(0)
            if litval(s.assigns, lit) == Int8(-1)
                _cdcl_stats.check_time += (time_ns() - t_start) / 1e9
                return :unsat
            end
            continue  # already true at level 0
        end
        push!(s.active_buf, lit)
    end

    if isempty(s.active_buf)
        _cdcl_stats.check_time += (time_ns() - t_start) / 1e9
        return :sat
    end

    # Assert all assumptions at level 1
    push!(s.trail_lim, length(s.trail))
    for lit in s.active_buf
        if !_cdcl_enqueue!(s, lit)
            # Conflict between assumptions
            _cdcl_backtrack!(s, 0)
            _cdcl_stats.check_time += (time_ns() - t_start) / 1e9
            return :unsat
        end
    end

    # Initial propagation after asserting assumptions
    if _cdcl_propagate!(s) != Int32(0)
        # Conflict — need full solve loop for analysis
        _cdcl_backtrack!(s, 0)

        # Re-assert assumptions for the solve loop
        push!(s.trail_lim, length(s.trail))
        for lit in s.active_buf
            if !_cdcl_enqueue!(s, lit)
                _cdcl_backtrack!(s, 0)
                _cdcl_stats.check_time += (time_ns() - t_start) / 1e9
                return :unsat
            end
        end
    elseif _all_clauses_satisfied(s)
        # All clauses satisfied after BCP — no decisions needed
        _cdcl_backtrack!(s, 0)
        _cdcl_stats.check_time += (time_ns() - t_start) / 1e9
        return :sat
    end

    result = _cdcl_solve_with_assumptions!(s, s.active_buf)
    _cdcl_backtrack!(s, 0)
    _cdcl_stats.check_time += (time_ns() - t_start) / 1e9
    return result
end

function _all_clauses_satisfied(s::CDCLSolver)::Bool
    @inbounds for clause in s.clauses
        satisfied = false
        for lit in clause
            if litval(s.assigns, lit) == Int8(1)
                satisfied = true
                break
            end
        end
        satisfied || return false
    end
    return true
end

function _cdcl_solve_with_assumptions!(s::CDCLSolver, assumptions::Vector{Int32})::Symbol
    while true
        conflict = _cdcl_propagate!(s)

        if conflict != Int32(0)
            _cdcl_stats.conflicts += 1
            if _dlevel(s) == 0
                return :unsat
            end

            learned, btlevel = _cdcl_analyze!(s, conflict)
            _vsids_decay!(s)
            _cdcl_backtrack!(s, btlevel)

            ci = _cdcl_add_clause!(s, learned)
            if length(learned) == 1
                _cdcl_enqueue!(s, learned[1])
            else
                _cdcl_enqueue!(s, learned[1], ci)
            end

            # If backjumped to level 0, propagate new facts, then re-assert assumptions
            if _dlevel(s) == 0
                if _cdcl_propagate!(s) != Int32(0)
                    return :unsat
                end
                push!(s.trail_lim, length(s.trail))
                for lit in assumptions
                    v = litvar(lit)
                    if s.assigns[v] != Int8(0)
                        if litval(s.assigns, lit) == Int8(-1)
                            _cdcl_backtrack!(s, 0)
                            return :unsat
                        end
                        continue  # already true at level 0
                    end
                    _cdcl_enqueue!(s, lit)
                end
            end
        else
            _cdcl_stats.decisions += 1
            # Periodically check if all clauses are already satisfied.
            # This catches don't-care variables without scanning clauses every iteration.
            if _cdcl_stats.decisions & Int(63) == 0 && _all_clauses_satisfied(s)
                return :sat
            end
            v = _cdcl_pick_var(s)
            v == 0 && return :sat
            push!(s.trail_lim, length(s.trail))
            _cdcl_enqueue!(s, mklit(v, true))
        end
    end
end

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
