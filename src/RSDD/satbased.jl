export var_bdd, true_bdd, false_bdd
const DEBUG_CHECKS = false

mutable struct DeferredBDD
    op::Symbol
    left::Union{DeferredBDD, Nothing}
    right::Union{DeferredBDD, Nothing}
    strict_bdd::Union{InnerBDD, Nothing}
end

mutable struct BDD
    bdd::DeferredBDD
    sat_expr::SATExpr
    solver::Union{CDCLSolver, Nothing}
end


function bdd_is_false(a::BDD)
    # Fast path: solver already determined satisfiability
    if a.solver !== nothing
        return false  # solver exists → known SAT
    end
    result = cdcl_solver_from(a.sat_expr)
    is_unsat = result === :unsat
    if result isa CDCLSolver
        a.solver = result  # cache for future incremental checks
        is_unsat = false
    end
    if DEBUG_CHECKS
        @assert bdd_is_false(force(a.bdd)) == is_unsat "SAT/BDD disagreement: CDCL says $(is_unsat ? :unsat : :sat) but BDD says $(bdd_is_false(force(a.bdd)) ? :unsat : :sat)"
    end
    return is_unsat
end

function bdd_is_true(a::BDD)
    return bdd_is_false(bdd_negate(a))
end


function force(deferred::DeferredBDD)::InnerBDD
    if deferred.strict_bdd !== nothing
        return deferred.strict_bdd
    end
    a = force(deferred.left)

    if deferred.op === :and
        if bdd_is_false(a)
            deferred.strict_bdd = a # F & _ = F
        elseif bdd_is_true(a)
            deferred.strict_bdd = force(deferred.right)
        else
            b = force(deferred.right)
            deferred.strict_bdd = bdd_and(a, b)
        end
    elseif deferred.op === :or
        if bdd_is_true(a)
            deferred.strict_bdd = a # T | _ = T
        elseif bdd_is_false(a)
            deferred.strict_bdd = force(deferred.right)
        else
            b = force(deferred.right)
            deferred.strict_bdd = bdd_or(a, b)
        end
    elseif deferred.op === :not
        deferred.strict_bdd = bdd_negate(a)
    end
    return deferred.strict_bdd
end

function var_bdd(bdd::InnerBDD, label::Int)::BDD
    deferred = DeferredBDD(:var, nothing, nothing, bdd)
    return BDD(deferred, sat_var(label), nothing)
end

function true_bdd(bdd::InnerBDD)::BDD
    deferred = DeferredBDD(:T, nothing, nothing, bdd)
    return BDD(deferred, SAT_TRUE, nothing)
end

function false_bdd(bdd::InnerBDD)::BDD
    deferred = DeferredBDD(:F, nothing, nothing, bdd)
    return BDD(deferred, SAT_FALSE, nothing)
end

function bdd_and(a::BDD, b::BDD)
    deferred = DeferredBDD(:and, a.bdd, b.bdd, nothing)
    return BDD(deferred, sat_and(a.sat_expr, b.sat_expr), nothing)
end

function bdd_or(a::BDD, b::BDD)
    deferred = DeferredBDD(:or, a.bdd, b.bdd, nothing)
    return BDD(deferred, sat_or(a.sat_expr, b.sat_expr), nothing)
end

function bdd_negate(a::BDD)
    deferred = DeferredBDD(:not, a.bdd, nothing, nothing)
    return BDD(deferred, sat_not(a.sat_expr), nothing)
end

"""
Get or create a CDCL solver for this BDD. Returns CDCLSolver, :sat, or :unsat.
"""
function ensure_cdcl_solver!(bdd::BDD)::Union{CDCLSolver, Symbol}
    bdd.solver !== nothing && return bdd.solver
    result = cdcl_solver_from(bdd.sat_expr)
    if result isa CDCLSolver
        bdd.solver = result
    end
    return result
end

bdd_implies(a::BDD, b::BDD) = b | !a
Base.:!(a::BDD) = bdd_negate(a)
Base.:&(a::BDD, b::BDD) = bdd_and(a, b)
Base.:|(a::BDD, b::BDD) = bdd_or(a, b)
bdd_topvar(a::BDD) = bdd_topvar(force(a.bdd))
bdd_size(a::BDD) = bdd_size(force(a.bdd))
bdd_wmc(a::BDD) = bdd_wmc(force(a.bdd))
