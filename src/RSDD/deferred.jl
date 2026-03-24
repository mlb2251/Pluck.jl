
const DEBUG_CHECKS = false

mutable struct BDD
    op::Symbol
    possible_vars::Set{Label}
    possible_overlap::Set{Label}
    maybe_const_true::Bool
    maybe_const_false::Bool
    left::Union{BDD, Nothing}
    right::Union{BDD, Nothing}
    strict_bdd::Union{InnerBDD, Nothing}
end

# function bdd_is_false(bdd::BDD)
#     # if it could be false, we need to force it
#     if bdd_maybe_const_false(bdd)
#         return bdd_is_false(force(bdd))
#     end
#     return false
# end

# function bdd_maybe_const_false(bdd::BDD)
#     head = bdd.head

#     # if forced, we just look at the inner bdd
#     head isa Forced && return bdd_is_false(head.bdd)

#     if head isa DeferredNot
#         return bdd_maybe_const_true(bdd.args[1])
#     end

#     if head isa DeferredAnd
#         a = bdd.args[1]
#         b = bdd.args[2]
#         # the bdd is false if either child is false
#         bdd_maybe_const_false(a) && return true
#         bdd_maybe_const_false(b) && return true
#         # if neither is false and they have no overlap, then the bdd cant be false
#         isempty(bdd.possible_overlap) && return false
#         # if there is overlap, we need to force ourselves
#         return bdd_is_false(force(bdd))
#     end

#     if head isa DeferredOr
#         a = bdd.args[1]
#         b = bdd.args[2]
#         # the bdd is false if either child is false
#         bdd_is_false(a) && return true
#         bdd_is_false(b) && return true
#         # if neither is false and they have no overlap, then the bdd cant be false
#         isempty(bdd.possible_overlap) && return false
#         # if there is overlap, we need to force ourselves
#         return bdd_is_false(force(bdd))
#     end
# end


function bdd_is_false(a::BDD)
    # strict_false = bdd_is_false(a.strict_bdd)
    # if !isnothing(a.strict_bdd)
    #     return bdd_is_false(a.strict_bdd)
    # end
    if !a.maybe_const_false
        return false
    end
    # is_false = bdd_is_false(a.strict_bdd)

    # is_false = bdd_is_false(force(a))
    # is_false = bdd_is_false(a.strict_bdd)
    # if is_false
    #     @assert a.maybe_const_false
    # end

    # return bdd_is_false(a.strict_bdd)
    return bdd_is_false(force(a))
end


function bdd_is_true(a::BDD)
    # if !isnothing(a.strict_bdd)
    #     return bdd_is_true(a.strict_bdd)
    # end
    if !a.maybe_const_true
        return false
    end
    # bdd_is_true(force(a))
    # return bdd_is_true(a.strict_bdd)

    # is_true = bdd_is_true(force(a))
    # is_true = bdd_is_true(a.strict_bdd)
    # if is_true
    #     @assert a.maybe_const_true
    # end

    return bdd_is_true(force(a))
end

function force(dbdd::BDD)::InnerBDD
    if dbdd.strict_bdd !== nothing
        return dbdd.strict_bdd
    end
    if dbdd.op === :and
        a = force(dbdd.left)
        if bdd_is_false(a) # perhaps unnecessary optimization but yeah
            set_forced(dbdd, a)
        else
            b = force(dbdd.right)
            set_forced(dbdd, a & b)
        end
    elseif dbdd.op === :not
        a = force(dbdd.left)
        set_forced(dbdd, !a)
    end
    return dbdd.strict_bdd
end

function set_forced(dbdd::BDD, bdd::InnerBDD)
    dbdd.strict_bdd = bdd
    dbdd.possible_vars = bdd_get_vars(bdd)
    dbdd.maybe_const_true = bdd_is_true(bdd)
    dbdd.maybe_const_false = bdd_is_false(bdd)
    dbdd.left = nothing
    dbdd.right = nothing
end

function embed_bdd(bdd::InnerBDD)::BDD
    return BDD(:embedded, bdd_get_vars(bdd), Set{Label}(),bdd_is_true(bdd), bdd_is_false(bdd), nothing, nothing, bdd)
end


function bdd_and(a::BDD, b::BDD)
    possible_vars = a.possible_vars ∪ b.possible_vars
    possible_overlap = a.possible_vars ∩ b.possible_vars
    maybe_const_true = a.maybe_const_true && b.maybe_const_true
    maybe_const_false = a.maybe_const_false || b.maybe_const_false || !isempty(possible_overlap)
    # strict_bdd = bdd_and(a.strict_bdd, b.strict_bdd)
    return BDD(:and, possible_vars, possible_overlap, maybe_const_true, maybe_const_false, a, b, nothing)
end

function bdd_or(a::BDD, b::BDD)
    return !(!a & !b)
end

function bdd_negate(a::BDD)
    # strict_bdd = bdd_negate(a.strict_bdd)
    # maybe true and maybe false swap
    return BDD(:not, a.possible_vars, Set{Label}(), a.maybe_const_false, a.maybe_const_true, a, nothing, nothing)
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

