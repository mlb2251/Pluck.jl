
const DEBUG_CHECKS = false

mutable struct BDD
    node
    negated::Bool
end

mutable struct DeferredNode
    op::Symbol
    possible_vars::Set{Label}
    possible_overlap::Set{Label}
    maybe_const_true::Bool
    maybe_const_false::Bool
    left::Union{BDD, Nothing}
    right::Union{BDD, Nothing}
    strict_bdd::Union{InnerBDD, Nothing}
end


function maybe_const_true(bdd::BDD)
    node = bdd.node :: DeferredNode
    bdd.negated ? node.maybe_const_false : node.maybe_const_true
end

function maybe_const_false(bdd::BDD)
    node = bdd.node :: DeferredNode
    bdd.negated ? node.maybe_const_true : node.maybe_const_false
end

function bdd_is_false(a::BDD)
    # strict_false = bdd_is_false(a.strict_bdd)
    # if !isnothing(a.strict_bdd)
    #     return bdd_is_false(a.strict_bdd)
    # end
    if !maybe_const_false(a)
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
    if !maybe_const_true(a)
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
    a = force(dbdd.left)
    if bdd_is_false(a) # perhaps unnecessary optimization but yeah
        set_strict(dbdd, a)
    else
        b = force(dbdd.right)
        set_strict(dbdd, a & b)
    end
    return dbdd.strict_bdd
end

function set_strict(node::DeferredNode, bdd::InnerBDD)
    node.strict_bdd = bdd
    node.possible_vars = bdd_get_vars(bdd)
    node.maybe_const_true = bdd_is_true(bdd)
    node.maybe_const_false = bdd_is_false(bdd)
    node.left = nothing
    node.right = nothing
end

function embed_bdd(bdd::InnerBDD)::BDD
    node = DeferredNode(:embedded, bdd_get_vars(bdd), Set{Label}(),bdd_is_true(bdd), bdd_is_false(bdd), nothing, nothing, bdd)
    return BDD(node, false)
end


function bdd_and(a::BDD, b::BDD)
    a_node = a.node :: DeferredNode
    b_node = b.node :: DeferredNode
    possible_vars = a_node.possible_vars ∪ b_node.possible_vars
    possible_overlap = a_node.possible_vars ∩ b_node.possible_vars
    maybe_const_true_val = maybe_const_true(a) && maybe_const_true(b)
    maybe_const_false_val = maybe_const_false(a) || maybe_const_false(b) || !isempty(possible_overlap)
    node = DeferredNode(:and, possible_vars, possible_overlap, maybe_const_true_val, maybe_const_false_val, a, b, nothing)
    return BDD(node, false)
end

function bdd_or(a::BDD, b::BDD)
    return !(!a & !b)
end

function bdd_negate(a::BDD)
    # strict_bdd = bdd_negate(a.strict_bdd)
    # maybe true and maybe false swap
    return BDD(a.node, !a.negated)
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

