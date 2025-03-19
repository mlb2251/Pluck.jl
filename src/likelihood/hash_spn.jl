export num_traces

# An SPNNode represents a *region* of trace space.
# It also measures the *volume* of that region under the program's distribution.
# For memory optimization, some dimensions of the region are not explicitly represented
# (corresponding to non-memoized choices).
# Unlike an ordinary sum-product network, sum nodes are not always over
# the same set of variables; some branches may have instantiated more 
# variables than others.

abstract type SPNNode end
const Scope = BitSet
const Address = Int
const EMPTY_SCOPE::Scope = Scope()

const EMPTY_ENV::Vector{Any} = Any[] # envs are treated immutably so its ok
const args_syms::Vector{Symbol} = [Symbol("arg$i") for i = 1:100]


const SPN = Int

struct Leaf <: SPNNode
    value::Any
    total::Float64
    scope::Scope # Name of this variable
end

struct Product <: SPNNode
    children::Vector{SPN}
    total::Float64 # Product of weights of children, times extra
    scope::Scope
    extra::Float64 # An extra weight multiplied into the product
end

struct Sum <: SPNNode
    children::Vector{SPN}
    total::Float64
    scope::Scope
end

const SPN_FALSE::SPN = 1
const SPN_TRUE::SPN = 2

struct SPNHash
    node_of_spn::Vector{SPNNode}
    spn_of_leaf::Dict{Tuple{Address, Any, Float64}, SPN}
    spn_of_product::Dict{Tuple{Vector{SPN}, Float64}, SPN}
    spn_of_sum::Dict{Vector{SPN}, SPN}
end

impossible(x::SPNNode) = weight(x) == -Inf
impossible(x::SPN) = x == SPN_FALSE # we guarantee this thru canonicalizing

@inline function weight(spn_hash::SPNHash, spn::SPN)
    spn == SPN_FALSE ? -Inf : spn == SPN_TRUE ? 0.0 : weight(spn_hash.node_of_spn[spn])
end

function canonicalize_leaf!(spn_hash::SPNHash, value, total, name::Address)::SPN
    total == -Inf && return SPN_FALSE
    get!(spn_hash.spn_of_leaf, (name, value, total)) do
        push!(spn_hash.node_of_spn, Leaf(value, total, Scope(name)))
        length(spn_hash.node_of_spn)
    end
end
function canonicalize_product!(spn_hash::SPNHash, children, extra::Float64)::SPN
    sort!(children)
    length(children) == 0 && extra == 0.0 && return SPN_TRUE
    length(children) == 1 && extra == 0.0 && return children[1]
    get!(spn_hash.spn_of_product, (children, extra)) do
        new_scope = Scope()
        total = extra
        for child in children
            node = spn_hash.node_of_spn[child]
            add_scope!(new_scope, node)
            total += weight(node)
        end
        total == -Inf && return SPN_FALSE # unclear if we want this added to hash like this or have it on outside
        push!(spn_hash.node_of_spn, Product(children, total, new_scope, extra))
        length(spn_hash.node_of_spn)
    end
end
function canonicalize_sum!(spn_hash::SPNHash, children)::SPN
    isempty(children) && SPN_FALSE # we guarantee anything with -Inf weight will get canonicalized to SPN_FALSE
    length(children) == 1 && return children[1]
    sort!(children)
    get!(spn_hash.spn_of_sum, children) do
        new_scope = Scope()
        total = -Inf
        for child in children
            node = spn_hash.node_of_spn[child]
            add_scope!(new_scope, node)
            total = logaddexp(total, weight(node))
        end
        total == -Inf && return SPN_FALSE # unclear if we want this added to hash like this or have it on outside
        push!(spn_hash.node_of_spn, Sum(children, total, new_scope))
        length(spn_hash.node_of_spn)
    end
end

const NODE_FALSE = Sum([], -Inf, Scope())
const NODE_TRUE = Product([], 0.0, Scope(), 0.0)


function SPNHash()
    spn_of_id = SPNNode[]
    leaf_of_spn = Dict{Leaf, SPN}()
    product_of_spn = Dict{Product, SPN}()
    sum_of_spn = Dict{Sum, SPN}()
    spn_hash = SPNHash(spn_of_id, leaf_of_spn, product_of_spn, sum_of_spn)
    empty!(spn_hash) # sets initial values for SPN_TRUE and SPN_FALSE
    spn_hash
end

function Base.empty!(spn_hash::SPNHash)
    empty!(spn_hash.node_of_spn)
    empty!(spn_hash.spn_of_leaf)
    empty!(spn_hash.spn_of_product)
    empty!(spn_hash.spn_of_sum)
    push!(spn_hash.node_of_spn, NODE_FALSE)
    push!(spn_hash.node_of_spn, NODE_TRUE)
    spn_hash.spn_of_sum[NODE_FALSE.children] = SPN_FALSE
    spn_hash.spn_of_product[(NODE_TRUE.children, NODE_TRUE.extra)] = SPN_TRUE
    spn_hash
end

@inline Base.getindex(spn_hash::SPNHash, id::SPN) = spn_hash.node_of_spn[id]

Base.:(==)(a::Leaf, b::Leaf) = a.scope == b.scope && a.value == b.value
# fails if children are in different order. No need to check scope since that's fully dependent on our children
Base.:(==)(a::Product, b::Product) = a.children == b.children && a.extra ≈ b.extra
# fails if children are in different order. No need to check scope since that's fully dependent on our children
Base.:(==)(a::Sum, b::Sum) = a.children == b.children

Base.hash(spn::Leaf, h::UInt) = hash(spn.scope, hash(spn.value, h))
# we dont include .extra in the hash because we dont need to for a valid hash – and it would make our approx equality invalid
# also no need to hash scope since tahts full dependent on our children
Base.hash(spn::Product, h::UInt) = hash(spn.children, h)
Base.hash(spn::Sum, h::UInt) = hash(spn.children, h)

# num_traces(spn::Leaf) = 1
# num_traces(spn::Product) = prod(num_traces(child) for child in spn.children; init=1)
# num_traces(spn::Sum) = sum(num_traces(child) for child in spn.children; init=0)

# depth(spn::Leaf) = 1
# depth(spn::Product) = 1 + maximum(depth.(spn.children); init=0)
# depth(spn::Sum) = 1 + maximum(depth.(spn.children); init=0)

# num_nodes(spn::Leaf) = 1
# num_nodes(spn::Product) = 1 + sum(num_nodes.(spn.children); init=0)
# num_nodes(spn::Sum) = 1 + sum(num_nodes.(spn.children); init=0)

in_scope(spn::Leaf, var::Address) = var in spn.scope
in_scope(spn::Product, var::Address) = var in spn.scope
in_scope(spn::Sum, var::Address) = var in spn.scope

add_scope!(scope::Scope, spn::Leaf) = union!(scope, spn.scope)
add_scope!(scope::Scope, spn::Product) = union!(scope, spn.scope)
add_scope!(scope::Scope, spn::Sum) = union!(scope, spn.scope)

weight(spn::Leaf) = spn.total
weight(spn::Product) = spn.total
weight(spn::Sum) = spn.total

mul_weight(spn_hash, spn::SPN, w::Float64) = mul_weight(spn_hash, spn, spn_hash[spn], w)
mul_weight(spn_hash, spn, node::Leaf, w::Float64) =
    canonicalize_leaf!(spn_hash, node.value, node.total + w, first(node.scope)) # TODO: should this create a product?
mul_weight(spn_hash, spn, node::Product, w::Float64) =
    canonicalize_product!(spn_hash, node.children, node.extra + w)
mul_weight(spn_hash, spn, node::Sum, w::Float64) = canonicalize_product!(spn_hash, [spn], w)

scope(spn::Leaf) = spn.scope
scope(spn::Product) = spn.scope
scope(spn::Sum) = spn.scope

function Base.show(io::IO, spn::Leaf)
    indent = Base.get(io, :indent, 0)
    print(
        io,
        " "^indent,
        first(spn.scope),
        " ~ ",
        spn.value,
        " [",
        round(exp(spn.total), sigdigits = 4),
        "]",
    )
end
function Base.show(io::IO, spn::Sum)
    indent = Base.get(io, :indent, 0)
    print(io, " "^indent, "Sum [total=", round(exp(spn.total), sigdigits = 2), "]")
    for (i, child) in enumerate(spn.children)
        inner_io = IOContext(io, :indent => indent + 2)
        print(inner_io, "\n", child)
    end
end
function Base.show(io::IO, spn::Product)
    indent = Base.get(io, :indent, 0)
    print(
        io,
        " "^indent,
        "Product [total=",
        round(exp(spn.total), sigdigits = 2),
        ", extra=",
        round(exp(spn.extra), sigdigits = 2),
        "]",
    )
    for (i, child) in enumerate(spn.children)
        inner_io = IOContext(io, :indent => indent + 2)
        print(inner_io, "\n", child)
    end
end

json_spn(spn::SPN, spn_hash) = json_spn(spn_hash.node_of_spn[spn], spn_hash)
json_spn(spn::Leaf, spn_hash) = Dict(
    "type" => "leaf",
    "value" => string(spn.value),
    "weight" => exp(weight(spn)),
    "scope" => spn.scope,
)
json_spn(spn::Sum, spn_hash) = Dict(
    "type" => "sum",
    "children" => [json_spn(c, spn_hash) for c in spn.children],
    "weight" => exp(weight(spn)),
    "scope" => spn.scope,
)
json_spn(spn::Product, spn_hash) = Dict(
    "type" => "product",
    "children" => [json_spn(c, spn_hash) for c in spn.children],
    "extra" => exp(spn.extra),
    "weight" => exp(weight(spn)),
    "scope" => spn.scope,
)

function add_products(
    a_children::Vector{SPN},
    a_extra,
    b_children::Vector{SPN},
    b_extra,
    eval_state,
)::Tuple{Vector{SPN}, Float64}
    """
    compute A + B. Pulls out any shared factors to get C * (A/C + B/C). These factors must be `===` indistinguishable
    direct children of A and B.
    """

    # @assert false "for initial spn_hash impl we shd disable this for simplicity"

    # pull out shared factors if any
    has_shared = any(a === b for a in a_children for b in b_children)
    shared_children = SPN[]
    if has_shared
        dup_a = Set{Int}()
        dup_b = Set{Int}()
        for (i, a) in enumerate(a_children)
            for (j, b) in enumerate(b_children)
                if a === b
                    push!(dup_a, i)
                    push!(dup_b, j)
                    push!(shared_children, a)
                end
            end
        end
        new_a = SPN[a_children[i] for i = 1:length(a_children) if !(i in dup_a)]
        new_b = SPN[b_children[i] for i = 1:length(b_children) if !(i in dup_b)]
    else
        new_a = a_children
        new_b = b_children
    end

    a_product = new_product(new_a, a_extra, eval_state)
    b_product = new_product(new_b, b_extra, eval_state)
    total_weight = logaddexp(weight((a_product, eval_state)), weight((b_product, eval_state)))
    new_scope = Scope()
    add_scope!(new_scope, eval_state.spn_hash[a_product])
    add_scope!(new_scope, eval_state.spn_hash[b_product])

    unshared_factors = SPN[]

    if a_product isa Sum
        append!(unshared_factors, a_product.children)
    else
        push!(unshared_factors, a_product)
    end
    if b_product isa Sum
        append!(unshared_factors, b_product.children)
    else
        push!(unshared_factors, b_product)
    end
    # sort!(unshared_factors, by=spn -> hash(spn))
    pushfirst!(shared_children, canonicalize_sum!(eval_state.spn_hash, unshared_factors))
    return shared_children, 0.0
end

function merge_worlds(worlds, eval_state)
    filter!(world -> !impossible(world[2]), worlds)
    # return worlds -- TODO: put merge worlds behind a flag?
    # From Maddy:     # Note this 2 line version which doesnt do the Dict / world merging is just as fast on our current examples, because
    # merging doesnt seem to happen much. Leaving it commented out tho because it'd be nice to find where the merging is helpful!
    # From Alex:     There is an example we were looking at (from Dice) where it does help, so adding back in, but maybe should be behind a flag

    # length(worlds) <= 1 && return worlds
    # return [(val, spn) for (val, spn) in worlds if !impossible(spn)] 

    length(worlds) <= 1 && return worlds
    val_to_spns = Dict{Any, Vector{SPN}}()

    for (val, spn) in worlds
        if haskey(val_to_spns, val)
            push!(val_to_spns[val], spn)
        else
            val_to_spns[val] = [spn]
        end
    end

    return [
        (val, new_sum(spns, eval_state)) for
        (val, spns) in val_to_spns if any(!impossible(spn) for spn in spns)
    ]
end

# Create a new sum node with the given children
function new_sum(children::Vector{SPN}, eval_state)::SPN
    """
    Takes a list of children and builds a Sum by merging scopes and totals of children. Skips -Inf children. Flattens Sum children.
    The order in which children get added like (A + B) + C vs A + (B + C) is not specified (in practice leaves
    get filtered out of the child list and handled separately)
    """
    children_processed = eval_state.reused.children_processed
    empty!(children_processed) # honestly shd be part of eval_state, this would be esp needed if we had threads
    while !isempty(children)
        child = popfirst!(children)
        node = eval_state.spn_hash[child]
        impossible(child) && continue
        if node isa Sum
            # Flatten children of sum nodes
            append!(children, node.children)
        else
            push!(children_processed, child)
        end
    end

    isempty(children_processed) && return SPN_FALSE
    length(children_processed) == 1 && return children_processed[1]
    if !eval_state.config.dedup_and_factor
        return canonicalize_sum!(eval_state.spn_hash, copy(children_processed))
    end

    # - Combine weights of duplicate children.
    product_weights = eval_state.reused.product_weights
    leaf_weights = eval_state.reused.leaf_weights
    children_as_products = eval_state.reused.children_as_products

    empty!(product_weights) # honestly shd be part of eval_state, this would be esp needed if we had threads
    empty!(leaf_weights) # honestly shd be part of eval_state, this would be esp needed if we had threads
    empty!(children_as_products) # honestly shd be part of eval_state, this would be esp needed if we had threads
    for child in children_processed
        child_node = eval_state.spn_hash[child]
        if child_node isa Product
            product_weights[child_node.children] =
                logaddexp(Base.get(product_weights, child_node.children, -Inf), child_node.extra)
        elseif child_node isa Leaf
            leaf_weights[(child_node.scope, child_node.value)] =
                logaddexp(Base.get(leaf_weights, (child_node.scope, child_node.value), -Inf), child_node.total)
        else
            error("children of sum node must be products or leaves, but got $child_node")
        end
    end

    # now put everything in (a_children, a_extra) form by wrapping Leaf in SPNNode[]
    for (a_children, extra) in product_weights
        push!(children_as_products, (a_children, extra))
    end
    for ((scope, val), wt) in leaf_weights
        push!(children_as_products, (SPN[canonicalize_leaf!(eval_state.spn_hash, val, wt, first(scope))], 0.0))
    end

    # now add them all together
    (a_children, a_extra) = pop!(children_as_products)
    while length(children_as_products) >= 1
        (b_children, b_extra) = pop!(children_as_products)
        (a_children, a_extra) =
            add_products(a_children, a_extra, b_children, b_extra, eval_state)
    end
    return canonicalize_product!(eval_state.spn_hash, a_children, a_extra)
end


# function new_sum(children)
#     total = reduce(logaddexp, (weight(child) for child in children), init=-Inf)
#     new_scope = Set{Symbol}()
#     for child in children
#         new_scope = union(new_scope, scope(child))
#     end
#     Sum(children, total, new_scope)
# end

# function new_product(children, extra)
#     total = sum(weight(child) for child in children; init=0.0)
#     new_scope = Dict{Symbol,Int}()
#     for (i, child) in enumerate(children)
#         for var in scope(child)
#             # @assert !haskey(new_scope, var) "Supports of product node children must be distinct, but $var is in both children $i and $(scope[var])"
#             new_scope[var] = i
#         end
#     end
#     Product(
#         children,
#         total + extra,
#         extra,
#         new_scope
#     )
# end

# Create a new product node with the given children
function new_product(children::Vector{SPN}, extra, eval_state)::SPN
    """
    Takes (children,extra) and builds a Product by merging scopes and totals and extras of children,
    and flattening out nested products. Returns -Inf if any child is -Inf. If there is only one child, that child is returned.
    """

    extra == -Inf && return SPN_FALSE
    isempty(children) && return Product(children, extra, extra, EMPTY_SCOPE)
    length(children) == 1 && impossible(children[1]) == -Inf && return SPN_FALSE
    length(children) == 1 && return extra == 0.0 ? children[1] :
                                    mul_weight(eval_state.spn_hash, children[1], extra)
    any(impossible(child) for child in children) && return SPN_FALSE

    # if eval_state.flat_spn
    #     # distribute the product completely so you end up with just a big sum over products
    #     sum_res = SPNNode[]
    #     push!(sum_res, pop!(children))
    #     while !isempty(children)
    #         next = pop!(children)
    #         if next isa Leaf
    #             append!(children, next.children)
    #         else
    #             res = new_product([res, next], 0.0, eval_state)
    #         end
    #     end
    #     # return new_sum(sum_res)
    # end

    processed_children = empty!(Vector{SPN}(undef, length(children)))

    for child in children
        node = eval_state.spn_hash[child]
        if node isa Product
            # Flatten children of product nodes
            append!(processed_children, node.children)
            extra += node.extra
            # @assert !any(in_scope(child, var) for var in new_scope)
        else
            push!(processed_children, child)
            # @assert !any(in_scope(child, var) for var in new_scope)
        end
    end
    # sort!(processed_children, by=spn -> hash(spn))
    return canonicalize_product!(eval_state.spn_hash, processed_children, extra)
end

function traced_condition_spn(spn::SPN, name, output, new_weight, eval_state)
    if eval_state.config.record_json
        new_record, old_children = new_json_record(
            :condition,
            Dict(
                :spn => json_spn(spn, eval_state.spn_hash),
                :name => name,
                :output => string(output),
                :weight => new_weight,
            ),
            eval_state,
        )
    end

    result =
        (eval_state.memoizing && !eval_state.config.disable_memoize) ?
        condition_spn(eval_state.spn_hash[spn], spn, name, output, new_weight, eval_state) :
        mul_weight(eval_state.spn_hash, spn, new_weight)

    limit_hit = check_time_limit(spn, name, output, new_weight, eval_state) ? :none : :time
    if eval_state.config.record_json
        json_record_result(new_record, result, limit_hit, false, eval_state, old_children)
    end
    result
end

function condition_spn(node::Leaf, spn::SPN, name, output, new_weight, eval_state)::SPN
    !check_time_limit(spn, name, output, new_weight, eval_state) && return SPN_FALSE

    name in scope(node) && return node.value == output ? spn : SPN_FALSE

    # Create a new product node.
    new_leaf = canonicalize_leaf!(eval_state.spn_hash, output, new_weight, name)
    new_children = SPN[spn, new_leaf]
    return new_product(new_children, 0.0, eval_state)
end

function condition_spn(node::Product, spn::SPN, name, output, new_weight, eval_state)::SPN
    !check_time_limit(spn, name, output, new_weight, eval_state) && return SPN_FALSE

    if name in scope(node)
        index =
            findfirst(child -> in_scope(eval_state.spn_hash[child], name), node.children)
        child = node.children[index]
        conditioned_child = condition_spn(
            eval_state.spn_hash[child],
            child,
            name,
            output,
            new_weight,
            eval_state,
        )
        impossible(conditioned_child) && return SPN_FALSE
        children = copy(node.children)
        children[index] = conditioned_child
        return new_product(children, node.extra, eval_state)
    else
        new_scope = copy(node.scope)
        push!(new_scope, name)
        new_children = copy(node.children)
        new_leaf = canonicalize_leaf!(eval_state.spn_hash, output, new_weight, name)
        push!(new_children, new_leaf)
        return new_product(new_children, node.extra, eval_state)
    end
end

function condition_spn(node::Sum, spn::SPN, name, output, new_weight, eval_state)::SPN
    !check_time_limit(spn, name, output, new_weight, eval_state) && return SPN_FALSE

    if name in scope(node)
        conditioned_children = SPN[
            condition_spn(
                eval_state.spn_hash[child],
                child,
                name,
                output,
                new_weight,
                eval_state,
            ) for child in node.children
        ]
        filter!(child -> !impossible(child), conditioned_children)
        return new_sum(conditioned_children, eval_state)
    else
        new_leaf = canonicalize_leaf!(eval_state.spn_hash, output, new_weight, name)
        new_children = SPN[spn, new_leaf]
        return new_product(new_children, 0.0, eval_state)
    end
end

@inline function check_time_limit(spn, name, output, new_weight, eval_state)
    eval_state.stats.condition_spn += 1
    if time() > eval_state.timeout_stack[end]
        # eval_state.config.verbose &&
        # printstyled("  "^eval_state.depth * "hit time limit", color = :yellow)
        eval_state.stats.time_limit_hit = 1
        return false
    end
    return true
end