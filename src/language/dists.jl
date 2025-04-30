struct Geometric
    p::Float64
end
function random(dist::Geometric)
    n = 0
    while rand() < dist.p
        n += 1
    end
    return n
end
logprob(dist::Geometric, n::Int) = n * log(dist.p) + log1p(-dist.p)

const geom_05 = Geometric(.5)

struct Uniform
    lo::Int
    hi::Int
end
random(dist::Uniform) = rand(dist.lo:dist.hi)
logprob(dist::Uniform, n::Int) = n < dist.lo || n > dist.hi ? -Inf : -log(dist.hi - dist.lo + 1)


struct FixedSize end
const fixed_size_dist = FixedSize()

function logprob(::FixedSize, pcfg::Grammar, size::Int, e::GExpr)::Float64
    @assert e.rhs_idx != 0 "parse_gexpr! must be called before logprob_gexpr"
    size != num_internal_nodes(e) && return -Inf

    # logprob of the production rule choice
    probs = size == 0 ? rhs_probs_leaf(pcfg, e) : rhs_probs_nonleaf(pcfg, e)
    logprob_ = log(probs[e.rhs_idx])

    # logprob of the variable choice (uniform)
    if is_var(e.rhs)
        var_choices = size == 0 ? valid_vars_leaf(pcfg, e) : valid_vars_nonleaf(pcfg, e)
        var_idx = get_var_idx(e.expr.child)
        logprob_ += var_idx in var_choices ? -log(length(var_choices)) : -Inf
    end

    # logprob of the allocation of the remaining size among children
    remaining_size = size - 1
    if remaining_size > 0
        num_children = length(e.rhs.symbol_paths)
        e.size_allocation_logprob = remaining_size * -log(num_children) # logspace of (1 / num_children) ^ remaining_num_internal_nodes    
        logprob_ += e.size_allocation_logprob
    else
        e.size_allocation_logprob = 0.
    end

    # recursive logprob call on children
    for (i, (sym, path)) in enumerate(e.rhs.symbol_paths)
        @assert e.children[i].lhs == getchild(e.rhs.expr, path).name == sym
        logprob_ += logprob(fixed_size_dist, pcfg, num_internal_nodes(e.children[i]), e.children[i])
    end

    e.logprob = logprob_
    logprob_
end

function random(::FixedSize, pcfg::Grammar, size::Int, e::GExpr)::GExpr
    @assert e.rhs_idx == 0 "sample_gexpr on an empty GExpr"

    # sample the production rule
    prods = pcfg.prod_of_sym[e.lhs].rhs_all
    probs = size == 0 ? rhs_probs_leaf(pcfg, e) : rhs_probs_nonleaf(pcfg, e)
    idx = sample(probs)
    rhs = prods[idx]

    # if it's a variable, sample which one and build any App structure if the variable is a function type
    if is_var(rhs)
        var_choices = size == 0 ? valid_vars_leaf(pcfg, e) : valid_vars_nonleaf(pcfg, e)
        # sample var (uniform)
        var_idx = var_choices[rand(1:length(var_choices))]
        rhs = build_var_rhs(e, var_idx, pcfg)
    end

    e.rhs = rhs
    e.rhs_idx = idx

    # mutate underlying Expr object
    set_underlying_expr!(e, copy(rhs.expr))

    # Decide out how to allocate our remaining size among the children.
    # Randomly populate the child sizes via repeated draws from a uniform categorical
    remaining_size = size - 1
    num_children = length(rhs.symbol_paths)
    child_sizes = fill(0, num_children)
    for _ in 1:remaining_size
        child_sizes[rand(1:num_children)] += 1
    end

    # recursively sample children
    for (i, (sym, path)) in enumerate(rhs.symbol_paths)
        child = make_child!(e, path, sym)
        random(fixed_size_dist, pcfg, child_sizes[i], child)
    end

    e
end

struct PCFGDist end
const pcfg_dist = PCFGDist()


function logprob(::PCFGDist, pcfg::Grammar, e::GExpr)::Float64
    @assert e.rhs_idx != 0 "parse_gexpr! must be called before logprob"

    # logprob of the production rule choice (PCFGDist considers all productions, combining leaf and nonleaf)
    probs = rhs_probs_all(pcfg, e)
    logprob_ = log(probs[e.rhs_idx])

    # logprob of the variable choice (uniform)
    if is_var(e.rhs)
        var_choices = valid_vars_all(pcfg, e)
        var_idx = get_var_idx(e.expr.child)
        logprob_ += var_idx in var_choices ? -log(length(var_choices)) : -Inf
    end

    # recursive logprob call on children
    for (i, (sym, path)) in enumerate(e.rhs.symbol_paths)
        @assert e.children[i].lhs == getchild(e.rhs.expr, path).name == sym
        logprob_ += logprob(pcfg_dist, pcfg, e.children[i])
    end

    e.logprob = logprob_
    logprob_
end

function random(::PCFGDist, pcfg::Grammar, e::GExpr)::GExpr
    @assert e.rhs_idx == 0 "random() must be called on an empty GExpr"

    # sample the production rule
    prods = pcfg.prod_of_sym[e.lhs].rhs_all
    probs = rhs_probs_all(pcfg, e)
    idx = sample(probs)
    rhs = prods[idx]

    # if it's a variable, sample which one and build any App structure if the variable is a function type
    if is_var(rhs)
        var_choices = valid_vars_all(pcfg, e)
        # sample var (uniform)
        var_idx = var_choices[rand(1:length(var_choices))]
        rhs = build_var_rhs(e, var_idx, pcfg)
    end

    e.rhs = rhs
    e.rhs_idx = idx

    # mutate underlying Expr object
    set_underlying_expr!(e, copy(rhs.expr))

    # recursively sample children
    for (sym, path) in rhs.symbol_paths
        child = make_child!(e, path, sym)
        random(pcfg_dist, pcfg, child)
    end

    e
end
