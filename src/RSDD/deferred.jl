export var_bdd, true_bdd, false_bdd
const DEBUG_CHECKS = false

mutable struct BDD
    node
    negated::Bool
end

node(bdd::BDD) :: DeferredNode = bdd.node

mutable struct DeferredNode
    op::Symbol
    min_var::Int
    max_var::Int
    maybe_const_true::Bool
    maybe_const_false::Bool
    left::Union{BDD, Nothing}
    right::Union{BDD, Nothing}
    strict_bdd::Union{InnerBDD, Nothing}
    sat_expr::SATExpr
end

function is_const_true(bdd::BDD)
    node = bdd.node :: DeferredNode
    return bdd.negated ? node.op === :F : node.op === :T
end

function is_const_false(bdd::BDD)
    node = bdd.node :: DeferredNode
    return bdd.negated ? node.op === :T : node.op === :F
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
    if is_const_false(a)
        return true
    end
    if !maybe_const_false(a)
        return false
    end

    if sat_check(get_sat_expr(a)) === :sat
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
    elseif bdd_is_true(a)
        set_strict(node, force(node.right))
    else
        b = force(node.right)
        set_strict(node, a & b)
    end
    return bdd.negated ? bdd_negate(node.strict_bdd) : node.strict_bdd
end

function set_strict(node::DeferredNode, bdd::InnerBDD)
    node.strict_bdd = bdd
    is_true = bdd_is_true(bdd)
    is_false = bdd_is_false(bdd)
    node.op = is_true ? :T : is_false ? :F : node.op
    node.min_var = is_true || is_false ? typemax(Int) : bdd_topvar(bdd)
    node.max_var = is_true || is_false ? typemin(Int) : node.max_var # we dont know the max var
    node.maybe_const_true = is_true
    node.maybe_const_false = is_false
    node.left = nothing
    node.right = nothing
end

function var_bdd(bdd::InnerBDD, label::Int)::BDD
    node = DeferredNode(:var, label, label, false, false, nothing, nothing, bdd, SATVar(label))
    return BDD(node, false)
end

function true_bdd(bdd::InnerBDD)::BDD
    node = DeferredNode(:T, typemax(Int), typemin(Int), true, false, nothing, nothing, bdd, SAT_TRUE)
    return BDD(node, false)
end

function false_bdd(bdd::InnerBDD)::BDD
    node = DeferredNode(:F, typemax(Int), typemin(Int), false, true, nothing, nothing, bdd, SAT_FALSE)
    return BDD(node, false)
end

function get_sat_expr(a::BDD)::SATExpr
    node = a.node :: DeferredNode
    return a.negated ? sat_not(node.sat_expr) : node.sat_expr
end

function bdd_and(a::BDD, b::BDD)
    is_const_true(a) && return b
    is_const_true(b) && return a
    is_const_false(a) && return a
    is_const_false(b) && return b

    a_node = a.node :: DeferredNode
    b_node = b.node :: DeferredNode
    interval_overlap = a_node.min_var != typemax(Int) && b_node.min_var != typemax(Int) && (a_node.min_var <= b_node.max_var && b_node.min_var <= a_node.max_var)

    min_var = min(a_node.min_var, b_node.min_var)
    max_var = max(a_node.max_var, b_node.max_var)
    maybe_const_true_val = maybe_const_true(a) && maybe_const_true(b)
    maybe_const_false_val = maybe_const_false(a) || maybe_const_false(b) || interval_overlap

    sat_expr = sat_and(get_sat_expr(a), get_sat_expr(b))
    node = DeferredNode(:and, min_var, max_var, maybe_const_true_val, maybe_const_false_val, a, b, nothing, sat_expr)
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



# function embed_bdd(bdd::InnerBDD)::BDD
#     node = DeferredNode(:embedded, varset_of_bdd(bdd), bdd_is_true(bdd), bdd_is_false(bdd), nothing, nothing, bdd)
#     return BDD(node, false)
# end


# VECTOR VERSION


# function varset_union(a, b)
#     isempty(a) && return b
#     isempty(b) && return a

#     c = empty!(Vector{Int}(undef, length(a) + length(b)))


#     ai = 1
#     bi = 1
#     while true
#         if a[ai] < b[bi]
#             push!(c, a[ai])
#             ai += 1
#         elseif a[ai] > b[bi]
#             push!(c, b[bi])
#             bi += 1
#         else
#             # both must be equal in this case
#             push!(c, a[ai])
#             ai += 1
#             bi += 1
#         end
#         if ai > length(a) || bi > length(b)
#             break
#         end
#     end

#     while ai <= length(a)
#         push!(c, a[ai])
#         ai += 1
#     end
#     while bi <= length(b)
#         push!(c, b[bi])
#         bi += 1
#     end

#     return c
# end

# function varset_empty_intersection(a, b)
#     isempty(a) && return true
#     isempty(b) && return true

#     ai = 1
#     bi = 1
#     while true
#         if a[ai] < b[bi]
#             ai += 1
#         elseif a[ai] > b[bi]
#             bi += 1
#         else
#             return false
#         end
#         if ai > length(a) || bi > length(b)
#             break
#         end
#     end

#     return true
# end

# function varset_of_label(label::Int)
#     return Int[label]
# end

# function empty_varset()
#     return Int[]
# end

# SET VERSION

# function varset_union(a, b)
#     isempty(a) && return b
#     isempty(b) && return a
#     return union(a, b)
# end

# function varset_empty_intersection(a, b)
#     isempty(a) && return true
#     isempty(b) && return true
#     for x in a
#         if x in b
#             return false
#         end
#     end
#     return true
# end

# function varset_of_bdd(bdd::InnerBDD)
#     return bdd_get_vars(bdd)
# end

# function varset_of_label(label::Int)
#     return Set{Int}([label])
# end

# function empty_varset()
#     return Set{Int}()
# end

