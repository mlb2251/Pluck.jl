export var_bdd, true_bdd, false_bdd
const DEBUG_CHECKS = false

mutable struct BDD
    node
    negated::Bool
end

node(bdd::BDD) :: DeferredNode = bdd.node

mutable struct DeferredNode
    op::Symbol
    possible_vars::Set{Int}
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
    if DEBUG_CHECKS
        if bdd_is_false(force(a))
            @assert maybe_const_false(a)
        end
    end
    if !maybe_const_false(a)
        return false
    end
    return bdd_is_false(force(a))
end

bdd_is_true(a::BDD) = bdd_is_false(!a)

function force(bdd::BDD)::InnerBDD
    node = bdd.node :: DeferredNode
    if node.strict_bdd !== nothing
        return bdd.negated ? bdd_negate(node.strict_bdd) : node.strict_bdd
    end
    a = force(node.left)
    if bdd_is_false(a) # perhaps unnecessary optimization but yeah
        set_strict(node, a) # F & _ = F
    else
        b = force(node.right)
        set_strict(node, a & b)
    end
    return bdd.negated ? bdd_negate(node.strict_bdd) : node.strict_bdd
end

function set_strict(node::DeferredNode, bdd::InnerBDD)
    node.strict_bdd = bdd
    # node.possible_vars = bdd_get_vars(bdd)
    node.maybe_const_true = bdd_is_true(bdd)
    node.maybe_const_false = bdd_is_false(bdd)
    node.left = nothing
    node.right = nothing
end

function embed_bdd(bdd::InnerBDD)::BDD
    node = DeferredNode(:embedded, varset_of_bdd(bdd), bdd_is_true(bdd), bdd_is_false(bdd), nothing, nothing, bdd)
    return BDD(node, false)
end

function var_bdd(bdd::InnerBDD, label::Int)::BDD
    node = DeferredNode(:var, varset_of_label(label), false, false, nothing, nothing, bdd)
    return BDD(node, false)
end

function true_bdd(bdd::InnerBDD)::BDD
    node = DeferredNode(:T, empty_varset(), true, false, nothing, nothing, bdd)
    return BDD(node, false)
end

function false_bdd(bdd::InnerBDD)::BDD
    node = DeferredNode(:F, empty_varset(), false, true, nothing, nothing, bdd)
    return BDD(node, false)
end


function bdd_and(a::BDD, b::BDD)
    a_node = a.node :: DeferredNode
    b_node = b.node :: DeferredNode
    possible_vars = varset_union(a_node.possible_vars, b_node.possible_vars)
    empty_intersect = varset_empty_intersection(a_node.possible_vars, b_node.possible_vars)
    maybe_const_true_val = maybe_const_true(a) && maybe_const_true(b) || !empty_intersect
    maybe_const_false_val = maybe_const_false(a) || maybe_const_false(b) || !empty_intersect
    node = DeferredNode(:and, possible_vars, maybe_const_true_val, maybe_const_false_val, a, b, nothing)
    return BDD(node, false)
end

bdd_or(a::BDD, b::BDD) = !(!a & !b)
bdd_negate(a::BDD) = BDD(a.node, !a.negated)
bdd_implies(a::BDD, b::BDD) = b | !a
Base.:!(a::BDD) = bdd_negate(a)
Base.:&(a::BDD, b::BDD) = bdd_and(a, b)
Base.:|(a::BDD, b::BDD) = bdd_or(a, b)
bdd_topvar(a::BDD) = bdd_topvar(force(a))
bdd_size(a::BDD) = bdd_size(force(a))
bdd_wmc(a::BDD) = bdd_wmc(force(a))



function varset_union(a, b)
    isempty(a) && return b
    isempty(b) && return a
    return union(a, b)
end

function varset_empty_intersection(a, b)
    isempty(a) && return true
    isempty(b) && return true
    for x in a
        if x in b
            return false
        end
    end
    return true
end

function varset_of_bdd(bdd::InnerBDD)
    return bdd_get_vars(bdd)
end

function varset_of_label(label::Int)
    return Set{Int}([label])
end

function empty_varset()
    return Set{Int}()
end

