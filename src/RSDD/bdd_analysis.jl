

abstract type DeferredHead end

struct DeferredAnd <: DeferredHead end
struct DeferredOr <: DeferredHead end
struct DeferredNot <: DeferredHead end
struct Forced <: DeferredHead
    bdd::InnerBDD
end

mutable struct BDD
    head::DeferredHead
    op::Symbol
    possible_vars::Set{Label}
    possible_overlap::Set{Label}
    maybe_const_true::Bool
    maybe_const_false::Bool
    args::Vector{BDD}
end

function bdd_is_false(bdd::BDD)
    # if it could be false, we need to force it
    if bdd_maybe_const_false(bdd)
        return bdd_is_false(force(bdd))
    end
    return false
end

function bdd_maybe_const_false(bdd::BDD)
    head = bdd.head

    # if forced, we just look at the inner bdd
    head isa Forced && return bdd_is_false(head.bdd)

    if head isa DeferredNot
        return bdd_maybe_const_true(bdd.args[1])
    end

    if head isa DeferredAnd
        a = bdd.args[1]
        b = bdd.args[2]
        # the bdd is false if either child is false
        bdd_maybe_const_false(a) && return true
        bdd_maybe_const_false(b) && return true
        # if neither is false and they have no overlap, then the bdd cant be false
        isempty(bdd.possible_overlap) && return false
        # if there is overlap, we need to force ourselves
        return bdd_is_false(force(bdd))
    end

    if head isa DeferredOr
        a = bdd.args[1]
        b = bdd.args[2]
        # the bdd is false if either child is false
        bdd_is_false(a) && return true
        bdd_is_false(b) && return true
        # if neither is false and they have no overlap, then the bdd cant be false
        isempty(bdd.possible_overlap) && return false
        # if there is overlap, we need to force ourselves
        return bdd_is_false(force(bdd))
    end
end





function bdd_is_true(a::BDD)
    if !a.maybe_const_true
        return false
    end
    return bdd_is_true(force(a))
end

function force(dbdd::BDD)::InnerBDD
    if dbdd.head isa DeferredAnd
        a = force(dbdd.args[1])
        if bdd_is_false(a) # perhaps unnecessary optimization but yeah
            set_forced(dbdd, a)
        else
            b = force(dbdd.args[2])
            set_forced(dbdd, a & b)
        end
    elseif dbdd.head isa DeferredOr
        a = force(dbdd.args[1])
        if bdd_is_true(a)
            set_forced(dbdd, a)
        else
            b = force(dbdd.args[2])
            set_forced(dbdd, a | b)
        end
    elseif dbdd.head isa DeferredNot
        a = force(dbdd.args[1])
        set_forced(dbdd, !a)
    end
    @assert dbdd.head isa Forced
    dbdd.head.bdd
end

function set_forced(dbdd::BDD, bdd::InnerBDD)
    dbdd.head = Forced(bdd)
    dbdd.possible_vars = bdd_get_vars(bdd)
    dbdd.maybe_const_true = bdd_is_true(bdd)
    dbdd.maybe_const_false = bdd_is_false(bdd)
    empty!(dbdd.args)
end

function embed_bdd(bdd::InnerBDD)::BDD
    return BDD(Forced(bdd), bdd_get_vars(bdd), Set{Label}(), bdd_is_true(bdd), bdd_is_false(bdd), BDD[])
end


function bdd_and(a::BDD, b::BDD)
    possible_vars = a.possible_vars ∪ b.possible_vars
    possible_overlap = a.possible_overlap ∩ b.possible_overlap
    maybe_const_true = a.maybe_const_true && b.maybe_const_true
    maybe_const_false = a.maybe_const_false || b.maybe_const_false || !isempty(possible_overlap)
    return BDD(DeferredAnd(), possible_vars, maybe_const_true, maybe_const_false, [a, b])
end

# note you could also write Or just as !(!a & !b) which if you had complement pointers wouldnt be bad
# but none of this matters for proof of concept
function bdd_or(a::BDD, b::BDD)
    possible_vars = a.possible_vars ∪ b.possible_vars
    maybe_const_true = a.maybe_const_true || b.maybe_const_true || !isempty(a.possible_vars ∩ b.possible_vars)
    maybe_const_false = a.maybe_const_false && b.maybe_const_false
    return BDD(DeferredOr(), possible_vars, maybe_const_true, maybe_const_false, [a, b])
end

function bdd_negate(a::BDD)
    # maybe true and maybe false swap
    return BDD(DeferredNot(), a.possible_vars, a.maybe_const_false, a.maybe_const_true, [a])
end

bdd_implies(a::BDD, b::BDD) = b | !a

Base.:!(a::BDD) = bdd_negate(a)
Base.:&(a::BDD, b::BDD) = bdd_and(a, b)
Base.:|(a::BDD, b::BDD) = bdd_or(a, b)

function bdd_wmc(bdd::BDD)
    return bdd_wmc(force(bdd))
end

function bdd_topvar(bdd::BDD)
    return bdd_topvar(force(bdd))
end

function bdd_size(bdd::BDD)
    return bdd_size(force(bdd))
end

