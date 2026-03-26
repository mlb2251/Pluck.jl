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
end


function bdd_is_false(a::BDD)
    # return bdd_is_false(force(a.bdd))
    if DEBUG_CHECKS
        @assert bdd_is_false(force(a.bdd)) == (sat_check(a.sat_expr) === :unsat)
    end
    return sat_check(a.sat_expr) === :unsat
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
    return BDD(deferred, sat_var(label))
end

function true_bdd(bdd::InnerBDD)::BDD
    deferred = DeferredBDD(:T, nothing, nothing, bdd)
    return BDD(deferred, SAT_TRUE)
end

function false_bdd(bdd::InnerBDD)::BDD
    deferred = DeferredBDD(:F, nothing, nothing, bdd)
    return BDD(deferred, SAT_FALSE)
end

function bdd_and(a::BDD, b::BDD)
    deferred = DeferredBDD(:and, a.bdd, b.bdd, nothing)
    return BDD(deferred, sat_and(a.sat_expr, b.sat_expr))
end

function bdd_or(a::BDD, b::BDD)
    deferred = DeferredBDD(:or, a.bdd, b.bdd, nothing)
    return BDD(deferred, sat_or(a.sat_expr, b.sat_expr))
end

function bdd_negate(a::BDD)
    deferred = DeferredBDD(:not, a.bdd, nothing, nothing)
    return BDD(deferred, sat_not(a.sat_expr))
end

bdd_implies(a::BDD, b::BDD) = b | !a
Base.:!(a::BDD) = bdd_negate(a)
Base.:&(a::BDD, b::BDD) = bdd_and(a, b)
Base.:|(a::BDD, b::BDD) = bdd_or(a, b)
bdd_topvar(a::BDD) = bdd_topvar(force(a.bdd))
bdd_size(a::BDD) = bdd_size(force(a.bdd))
bdd_wmc(a::BDD) = bdd_wmc(force(a.bdd))


