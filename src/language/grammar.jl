export Grammar, propose, SMCProposalResult, ExpandLeafProposal, ExpandLeafMultistepProposal, Geometric, show_size_dist, parsed_expr, pcfg_dist

"""
A path describing how to traverse a PExpr or GExpr to reach a particular subexpression.
The entries in the path are the indices of the children to follow.
"""
const Path = Vector{Int}

"""
The right hand side (RHS) of a PCFG production, along with paths to the subexprs that are cfg symbols,
like (index ?int ?list) has paths to ?int and ?list. 
is_random is true if PExpr itself contains a RandomPrimitive
"""
struct GrammarProdRHS
    expr::PExpr
    symbol_paths::Vector{Tuple{Symbol,Path}}
    is_var::Bool
    is_random::Bool
end
GrammarProdRHS(e::PExpr) = GrammarProdRHS(e, e isa VarCFGSymbol ? [] : [(c.name, path) for (c, path) in cfg_symbol_paths(e)], e isa VarCFGSymbol, is_random(e))
function is_leaf(rhs::GrammarProdRHS)
    @assert !is_var(rhs) "can't call is_leaf on a var because whether it's a leaf depends on the context"
    isempty(rhs.symbol_paths)
end
@inline is_var(rhs::GrammarProdRHS) = rhs.is_var
@inline is_random(rhs::GrammarProdRHS) = rhs.is_random


"""
A full PCFG production - nonterminal symbol on left like `?int` and a list of possible right hand sides.
We have 3 different lists of right hand sides: "leaf" ones where the RHS doesnt contain futher nonterminals
to expand. "nonterm" ones where they do, and "all" which is the union of the two. For each of these lists,
there are actually two distributions: one where there is one or more variables to be added to the list of productions,
and one where there are no such variables. For example if theres an int-typed var in context then to take that into account
we have to renormalize the probabilities of the other productions to include this - which is what we've precomputed
here with probs_leaf_yesvar. Note that function typed variable are essentially new nonterminals eg (#1 ?int ?bool).

Also note all RHS lists have a Var production
"""
mutable struct GrammarProd
    lhs::Symbol

    rhs_all::Vector{GrammarProdRHS}
    probs_all_yesvar::Vector{Float64}
    probs_all_novar::Vector{Float64}

    probs_leaf_yesvar::Vector{Float64}
    probs_leaf_novar::Vector{Float64}
    probs_leaf_novar_random::Vector{Float64}

    probs_nonterm_yesvar::Vector{Float64}
    probs_nonterm_novar::Vector{Float64}
end
GrammarProd(lhs, rhs_all, probs_all_yesvar, probs_all_novar) = GrammarProd(lhs, rhs_all, probs_all_yesvar, probs_all_novar, [], [], [], [], [])

mutable struct Grammar
    prods::Vector{GrammarProd}
    prod_of_sym::Dict{Symbol,GrammarProd}
    sym_of_type::Dict{PType,Symbol}
    start_sym_of_type::Dict{PType,Symbol}
    start_expr_of_type::Dict{PType,PExpr}
    size_dist::Any
end


export size_dist

const SizeCache = Dict{Tuple{Symbol, Union{Int,Nothing}, Int}, Float64}
"""
Probability that sampling from the PCFG distribution starting from `sym` will result in a tree of size `size`
For now, we assume variables of all types are available (though it's not hard to relax this). We also assume
no function typed vars are available (ie vars are terminals).

P(size | sym) = Σ_rhs P(size | sym, rhs) P(rhs | sym)
"""
function size_dist(pcfg::Grammar, sym::Symbol, size::Int; cache=SizeCache())::Float64
    haskey(cache, (sym, nothing, size)) && return cache[(sym, nothing, size)]
    prods = pcfg.prod_of_sym[sym]::GrammarProd
    res = sum(prods.probs_all_yesvar[i] * size_dist(pcfg, sym, i, size; cache=cache) for i in eachindex(prods.rhs_all))
    cache[(sym, nothing, size)] = res
    res
end

"""
Probability that sampling from the PCFG distribution starting from `sym` at the `idx`th production will result in a tree of size `size`
For now, we assume variables of all types are available (though it's not hard to relax this).  We also assume
no function typed vars are available (ie vars are terminals).


"""
function size_dist(pcfg::Grammar, sym::Symbol, idx::Int, size::Int; cache=SizeCache())::Float64
    haskey(cache, (sym, idx, size)) && return cache[(sym, idx, size)]
    prods = pcfg.prod_of_sym[sym]::GrammarProd
    rhs = prods.rhs_all[idx]::GrammarProdRHS
    if size == 0
        return is_var(rhs) || is_leaf(rhs) ? 1.0 : 0.0
    elseif is_var(rhs) || is_leaf(rhs)
        return 0.0
    end
    res = sum_to_k(pcfg, rhs.symbol_paths, size - 1; cache=cache)
    cache[(sym, idx, size)] = res
    res
end


function show_size_dist(g::Grammar, max_size)
    cache = SizeCache()
    pad_sym = maximum(length(string(prod.lhs)) for prod in g.prods)
    for prod in g.prods
        sym = prod.lhs
        println(rpad(sym,pad_sym), " ", collect(round3(size_dist(g, sym, k; cache=cache)) for k in 0:max_size))
        pad_rhs = maximum(length(string(prod.rhs_all[i])) for i in eachindex(prod.rhs_all))
        for i in eachindex(g.prod_of_sym[sym].rhs_all)
            println("  ", rpad(g.prod_of_sym[sym].rhs_all[i], pad_rhs), " ", collect(round3(size_dist(g, sym, i, k; cache=cache)) for k in 0:max_size))
        end
        println()
    end
end



function sum_to_k(pcfg::Grammar, symbol_paths::Vector{Tuple{Symbol,Path}}, remaining::Int; cache=SizeCache())::Float64
    @assert !isempty(symbol_paths)
    first_sym = symbol_paths[1][1]
    length(symbol_paths) == 1 && return size_dist(pcfg, first_sym, remaining; cache=cache)
    symbol_paths = symbol_paths[2:end]
    sum(size_dist(pcfg, first_sym, first_size; cache=cache) * sum_to_k(pcfg, symbol_paths, remaining - first_size; cache=cache) for first_size in 0:remaining)
end


"""
Construct a PCFG from a list of productions. Any CFG symbols that are not
in sym_of_type or start_sym_of_type will be unrolled away.
"""
function Grammar(prods, sym_of_type::Vector{Pair{String,String}}, start_expr_of_type::Vector{Pair{String,String}}; size_dist=Geometric(0.5), start_sym_of_type::Vector{Pair{String,String}}=sym_of_type)
    sym_of_type = Dict{PType,Symbol}(parse_type(k) => parse_expr(v).name for (k, v) in sym_of_type)
    start_sym_of_type = Dict{PType,Symbol}(parse_type(k) => parse_expr(v).name for (k, v) in start_sym_of_type)
    start_expr_of_type = Dict{PType,PExpr}(parse_type(k) => parse_expr(v) for (k, v) in start_expr_of_type)
    # "original" refers to the productions as given, before unrolling
    original_prod_of_sym = Dict{Symbol,GrammarProd}()
    original_prods = Vector{GrammarProd}()

    # build the initial hierchical pcfg pre-unrolling
    for (lhs_str, rhs_options_vec) in prods
        # parse LHS and assert right format
        @assert rhs_options_vec isa Vector "rhs_options should be a list not a $(typeof(rhs_options_vec)) on the RHS of $lhs_str"
        parsed_lhs = parse_expr(lhs_str)
        @assert parsed_lhs isa AuxCFGSymbol "invalid left hand side: $lhs_str"
        lhs = parsed_lhs.name # eg `int_nonterm`
        @assert !haskey(original_prod_of_sym, lhs) "duplicate production for $lhs"

        # set default of 1.0 for weight
        rhs_entries = Pair{PExpr,Float64}[]
        for rhs in rhs_options_vec
            @assert rhs isa String || rhs isa Pair "unexpected type for rhs: $(typeof(rhs))"
            push!(rhs_entries, rhs isa String ? (parse_expr(rhs) => 1.0) : parse_expr(rhs[1]) => rhs[2])
        end

        # build up initial set of productions
        total_weight_yesvar = sum(wt for (_, wt) in rhs_entries)
        total_weight_novar = sum(wt for (e, wt) in rhs_entries if !(e isa VarCFGSymbol); init=0.)
        probs_all_yesvar = [wt / total_weight_yesvar for (_, wt) in rhs_entries]
        probs_all_novar = [e isa VarCFGSymbol ? 0.0 : wt / total_weight_novar for (e, wt) in rhs_entries]
        @assert sum(probs_all_yesvar) ≈ 1.0
        @assert sum(probs_all_novar) ≈ 1.0

        rhs_all = map(entry -> GrammarProdRHS(entry[1]), rhs_entries)
        @assert length(probs_all_novar) == length(probs_all_yesvar) == length(rhs_all)
        prod = GrammarProd(lhs, rhs_all, probs_all_yesvar, probs_all_novar)

        push!(original_prods, prod)
        original_prod_of_sym[lhs] = prod
    end

    # these will be the final productions we return – we will mutate them to unroll away
    # any intermediate productions used
    unrolled_prods = filter(prod -> prod.lhs in values(sym_of_type) || prod.lhs in values(start_sym_of_type), original_prods)
    unrolled_prod_of_sym = Dict{Symbol,GrammarProd}(prod.lhs => prod for prod in unrolled_prods)

    for prod in unrolled_prods
        i = 1 # while loop since we're extending the length of this list as we go
        while i <= length(prod.rhs_all)
            rhs = prod.rhs_all[i]::GrammarProdRHS
            prob_yesvar = prod.probs_all_yesvar[i]
            prob_novar = prod.probs_all_novar[i]
            if all(sym_path -> sym_path[1] in values(sym_of_type), rhs.symbol_paths)
                i += 1
                continue # this production is done! Any nonterminals in it are our target nonterminals
            end
            # we need to unroll this production. Lets unroll the first nonterminal in it.
            deleteat!(prod.rhs_all, i) # delete the old one since we're expanding it
            deleteat!(prod.probs_all_yesvar, i)
            deleteat!(prod.probs_all_novar, i)
            j = findfirst(sym_path -> sym_path[1] ∉ values(sym_of_type), rhs.symbol_paths)
            (sym, path) = rhs.symbol_paths[j]
            expand_to_prod = original_prod_of_sym[sym]
            # println("?$(prod.lhs) => $(rhs.expr) expanding $sym with $expand_to_prod")
            # create a new rhs for each way of expanding the nonterminal. Reversing just
            # gives a more intuitive ordering because of how we'll later repeatedly call insert!() at index i
            for (rhs_inner, prob_yesvar_inner, prob_novar_inner) in reverse(collect(zip(expand_to_prod.rhs_all, expand_to_prod.probs_all_yesvar, expand_to_prod.probs_all_novar)))
                new_rhs_expr = if isempty(path)
                    copy(rhs_inner.expr)
                else
                    new_rhs_expr = copy(rhs.expr)
                    setchild!(new_rhs_expr, path, copy(rhs_inner.expr))
                    new_rhs_expr
                end
                new_rhs = GrammarProdRHS(new_rhs_expr)
                # insert them all at index i and dont increment i, so when the loop continues we
                # will process these things that we just inserted!
                insert!(prod.rhs_all, i, new_rhs)
                insert!(prod.probs_all_yesvar, i, prob_yesvar * prob_yesvar_inner)
                insert!(prod.probs_all_novar, i, prob_novar * prob_novar_inner)
            end
        end
    end

    # populate _leaf and _nonterm fields
    for prod in unrolled_prods
        if !any(is_var(rhs) for rhs in prod.rhs_all) && prod.lhs in values(sym_of_type)
            # @warn "no #type variable production in $(prod.lhs)"
        end

        # condition on whether its a leaf and renormalize
        leaves = [is_var(rhs) || is_leaf(rhs) for rhs in prod.rhs_all]
        prod.probs_leaf_yesvar = prod.probs_all_yesvar .* leaves
        prod.probs_leaf_yesvar ./= sum(prod.probs_leaf_yesvar)
        prod.probs_leaf_novar = prod.probs_all_novar .* leaves
        prod.probs_leaf_novar ./= sum(prod.probs_leaf_novar)

        nonterms = [is_var(rhs) || !is_leaf(rhs) for rhs in prod.rhs_all]
        prod.probs_nonterm_yesvar = prod.probs_all_yesvar .* nonterms
        prod.probs_nonterm_yesvar ./= sum(prod.probs_nonterm_yesvar)
        prod.probs_nonterm_novar = prod.probs_all_novar .* nonterms
        prod.probs_nonterm_novar ./= sum(prod.probs_nonterm_novar)

        random_novar_leaves = [!is_var(rhs) && is_leaf(rhs) && is_random(rhs) for rhs in prod.rhs_all]
        prod.probs_leaf_novar_random = prod.probs_all_novar .* random_novar_leaves
        prod.probs_leaf_novar_random ./= sum(prod.probs_leaf_novar_random)

        @assert isempty(prod.probs_all_yesvar) || sum(prod.probs_all_yesvar) ≈ 1.0
        @assert isempty(prod.probs_all_novar) || sum(prod.probs_all_novar) ≈ 1.0
        @assert sum(leaves) == 0. || sum(prod.probs_leaf_yesvar) ≈ 1.0
        @assert sum(leaves) == 0. || sum(prod.probs_leaf_novar) ≈ 1.0
        @assert sum(nonterms) == 0. || sum(prod.probs_nonterm_yesvar) ≈ 1.0
        @assert sum(nonterms) == 0. || sum(prod.probs_nonterm_novar) ≈ 1.0
        @assert sum(random_novar_leaves) == 0. || sum(prod.probs_leaf_novar_random) ≈ 1.0
    end

    return Grammar(unrolled_prods, unrolled_prod_of_sym, sym_of_type, start_sym_of_type, start_expr_of_type, size_dist)
end

function Base.show(io::IO, p::Grammar)
    println(io, "PCFG:")
    for prod in p.prods
        println(io, "  ", prod)
    end
end

function Base.show(io::IO, p::GrammarProd)
    print(io, "?", p.lhs, " -> ")
    for (i, rhs) in enumerate(p.rhs_all)
        no = round1(p.probs_all_novar[i])
        yes = round1(p.probs_all_yesvar[i])
        yes == no ? print(io, rhs, " [", yes, "]") : print(io, rhs, " [", yes, "-", no, "]")
        i < length(p.rhs_all) && print(io, " | ")
    end
end

function Base.show(io::IO, p::GrammarProdRHS)
    print(io, p.expr)
end


"""

`children`: these all have separate SubExpr objects for the same underlying Expr ie mutation on that Expr will affect all of them
`expr`: note that the `.path` of this tells you the path through the Expr tree to get here
`lhs`: the nonterminal symbol that this subexpression came from
`path`: the path through the GExpr tree to get here
"""
mutable struct GExpr
    lhs::Symbol
    rhs::Union{Nothing,GrammarProdRHS}
    rhs_idx::Int
    logprob::Float64 # logprob under whatever the last distribution this was logprob'd against was
    size_allocation_logprob::Float64
    expr::SubExpr
    children::Vector{GExpr}
    parent::Union{Nothing,Tuple{GExpr,Int}}
end

GExpr(lhs, expr) = GExpr(lhs, nothing, 0, -Inf, 0., expr, GExpr[], nothing)

JSON.lower(e::GExpr) = string(e.expr.child)
Base.show(io::IO, e::GExpr) = print(io, e.expr.child)
function show_detailed(e::GExpr, depth=0)
    res = ""
    depth == 0 && (res *= "$(e.expr.child)\n")
    alloc_str = e.size_allocation_logprob == 0. ? "" : " <- $(round3(exp(e.size_allocation_logprob)))"
    res *= "[$(round3(exp(e.logprob)))$alloc_str] $(e.rhs)"
    for child in e.children
        res *= "\n" * "  "^(depth+1) * show_detailed(child, depth+1)
    end
    res
end

"""
end

"""

function parsed_expr_root(lhs, type, env; env_names=Symbol[Symbol("input$i") for i in eachindex(env)])
    SubExpr(AuxCFGSymbol(lhs), type, env, env_names, Int[])
end

"""
Creates a fresh GExpr whose body is an AuxCFGSymbol but with
the environment / path / type / etc of the original GExpr.
The parent pointer is set to nothing.
"""
function from_lhs_detached(pe::GExpr)
    expr = copy(pe.expr) # wont copy underlying Expr
    expr.child = AuxCFGSymbol(pe.lhs) # revert it to a nonterminal symbol
    GExpr(pe.lhs, expr)
end


function rhs_probs_all(pcfg::Grammar, e::GExpr)::Vector{Float64}
    lhs_prod = pcfg.prod_of_sym[e.lhs]
    has_var = any(e.expr.type == return_type(t) for t in e.expr.env)
    has_var ? lhs_prod.probs_all_yesvar : lhs_prod.probs_all_novar
end

function rhs_probs_leaf(pcfg::Grammar, e::GExpr)::Vector{Float64}
    lhs_prod = pcfg.prod_of_sym[e.lhs]
    has_var = any(num_args(t) == 0 && e.expr.type == return_type(t) for t in e.expr.env)
    has_var ? lhs_prod.probs_leaf_yesvar : lhs_prod.probs_leaf_novar
end

function rhs_probs_nonleaf(pcfg::Grammar, e::GExpr)::Vector{Float64}
    lhs_prod = pcfg.prod_of_sym[e.lhs]
    has_var = any(num_args(t) > 0 && e.expr.type == return_type(t) for t in e.expr.env)
    has_var ? lhs_prod.probs_nonterm_yesvar : lhs_prod.probs_nonterm_novar
end

function valid_vars_all(pcfg::Grammar, e::GExpr)::Vector{Int}
    Int[i for (i, t) in enumerate(e.expr.env) if e.expr.type == return_type(t)]
end

function valid_vars_leaf(pcfg::Grammar, e::GExpr)::Vector{Int}
    Int[i for (i, t) in enumerate(e.expr.env) if num_args(t) == 0 && e.expr.type == return_type(t)]
end

function valid_vars_nonleaf(pcfg::Grammar, e::GExpr)::Vector{Int}
    Int[i for (i, t) in enumerate(e.expr.env) if num_args(t) > 0 && e.expr.type == return_type(t)]
end

"""
Replaces the old GExpr with the new one. This new one must
already have the right env, type, path, etc.
This function also modifies the underlying Expr thats shared by
all the nodes in the GExpr tree (via setchild!() on old.parent.expr.child)
"""
function swap!(old::GExpr, new::GExpr)
    @assert old.lhs == new.lhs
    @assert old.expr.type == new.expr.type
    @assert old.expr.env == new.expr.env
    @assert new.expr.path == old.expr.path
    @assert !isnothing(old.parent)

    parent = old.parent[1]
    idx = old.parent[2]
    new.parent = (parent, idx)
    old.parent = nothing
    parent.children[idx] = new

    # modify the actual underlying Expr
    setchild!(parent.expr.child, relative_path(parent.expr, new.expr), new.expr.child)
    nothing
end

"""
Replaces the old GExpr with the new one and returns the root – if the old one
*is* the root it isn't mutated inplace we just return the new one.
"""
function replace_parsed_expr(root, old, new)
    if isnothing(old.parent)
        @assert objectid(old) == objectid(root)
        return new
    end
    swap!(old, new)
    root
end


function relative_path(ancestor::SubExpr, descendant::SubExpr)
    @assert length(ancestor.path) <= length(descendant.path)
    for i in 1:length(ancestor.path)
        @assert ancestor.path[i] == descendant.path[i]
    end
    descendant.path[length(ancestor.path)+1:end]
end

function parsed_expr(
    pcfg,
    e::PExpr,
    type::PType,
    env::Vector{PType}
)::GExpr
    parsed_expr(pcfg, SubExpr(e, type, env))
end

function parsed_expr(pcfg, e::SubExpr)
    start_symbol = pcfg.start_sym_of_type[e.type]
    parse_gexpr!(pcfg, GExpr(start_symbol,e))
end

function descendants!(e::GExpr, acc::Vector{GExpr})
    push!(acc, e)
    for child in e.children
        descendants!(child, acc)
    end
end
function descendants!(f::F, e::GExpr, acc::Vector{GExpr})  where {F}
    f(e) && push!(acc, e)
    for child in e.children
        descendants!(f, child, acc)
    end
end
function descendants(e::GExpr)::Vector{GExpr}
    acc = GExpr[]
    descendants!(e, acc)
    acc
end
function descendants(f::F, e::GExpr)::Vector{GExpr} where {F}
    acc = GExpr[]
    descendants!(f, e, acc)
    acc
end
function get_leaves(e::GExpr)::Vector{GExpr}
    acc = descendants(e)
    filter!(is_leaf, acc)
    acc
end

@inline is_leaf(e::GExpr) = isempty(e.children)

num_internal_nodes(e::GExpr) = isempty(e.children) ? 0 : (1 + sum(num_internal_nodes, e.children))
num_leaf_nodes(e::GExpr) = isempty(e.children) ? 1 : sum(num_leaf_nodes, e.children)
num_all_nodes(e::GExpr) = isempty(e.children) ? 1 : (1 + sum(num_all_nodes, e.children))

"""
fresh copy of the GExpr tree with a fresh
underlying Expr and all SubExprs
"""
function reparse(e::GExpr, pcfg::Grammar)
    expr = copy(e.expr.child)
    env = e.expr.env
    type = e.expr.type
    parsed_expr(pcfg, expr, type, env)
end

function modify_expression(
    e::GExpr,
    pcfg::Grammar,
    size_dist,
)
    all_subexpressions = descendants(e)

    # uniformly pick a subtree
    selected_subexpression = all_subexpressions[rand(1:length(all_subexpressions))]

    # sample a replacement for it
    # replacement_size = random(size_dist)
    # replacement = random(fixed_size_dist, pcfg, replacement_size, from_lhs_detached(selected_subexpression))
    # logprior_replacement = logprob(size_dist, replacement_size) + logprob(fixed_size_dist, pcfg, replacement_size, replacement)
    replacement = random(pcfg_dist, pcfg, from_lhs_detached(selected_subexpression))
    logprior_replacement = logprob(pcfg_dist, pcfg, replacement)

    # forward proposal probability is P(chose_this_subtree) * P(sampled_this_replacement)
    log_forward_proposal = -log(length(all_subexpressions)) + logprior_replacement

    # logprior_selected_subexpression = logprob(size_dist, num_internal_nodes(selected_subexpression)) + logprob(fixed_size_dist, pcfg, num_internal_nodes(selected_subexpression), selected_subexpression) # for reverse

    logprior_selected_subexpression = logprob(pcfg_dist, pcfg, selected_subexpression) # for reverse

    # println("replacement ", replacement.expr.child)

    # Replace the subexpression with the replacement
    # println("before ", e.expr.child)
    e = replace_parsed_expr(e, selected_subexpression, replacement)
    # println("after ", e.expr.child)

    # now calculate backward direction – how many subtrees do we have to choose among now?
    all_subexpressions_after = descendants(e)

    # backward proposal probability is P(chose_this_subtree from the new set of subtrees) * P(sampled original expr)
    log_backward_proposal = -log(length(all_subexpressions_after)) + logprior_selected_subexpression

    logproposal_ratio = log_backward_proposal - log_forward_proposal

    return e, logproposal_ratio, selected_subexpression.expr.path
end

function modify_expression_same_size(
    e::GExpr,
    pcfg::Grammar
)
    all_subexpressions = descendants(e)

    # uniformly pick a subtree
    selected_subexpression = all_subexpressions[rand(1:length(all_subexpressions))]
    selected_size = num_internal_nodes(selected_subexpression)

    # sample a replacement for it
    replacement = random(fixed_size_dist, pcfg, selected_size, from_lhs_detached(selected_subexpression))
    logprior_repplacement = logprob(fixed_size_dist, pcfg, selected_size, replacement)
    # forward proposal probability is P(chose_this_subtree) * P(sampled_this_replacement)
    log_forward_proposal = -log(length(all_subexpressions)) + logprior_replacement

    logprior_selected_subexpression = logprob(fixed_size_dist, pcfg, selected_size, selected_subexpression) # for reverse
    # println("replacement ", replacement.expr.child)

    # Replace the subexpression with the replacement
    # println("before ", e.expr.child)
    e = replace_parsed_expr(e, selected_subexpression, replacement)
    # println("after ", e.expr.child)

    # now calculate backward direction – how many subtrees do we have to choose among now?
    all_subexpressions_after = descendants(e)

    # backward proposal probability is P(chose_this_subtree from the new set of subtrees) * P(sampled original expr)
    log_backward_proposal = -log(length(all_subexpressions_after)) + logprior_selected_subexpression

    logproposal_ratio = log_backward_proposal - log_forward_proposal

    return e, logproposal_ratio, selected_subexpression.expr.path
end

struct SMCProposalResult
    e::GExpr
    logK::Float64
    logL::Float64
    highlight_paths::Vector{Path}
end

@kwdef struct ExpandLeafProposal
    select_random_only::Bool = true # rational rules needs this
    replacement_size::Int = 1
end

function propose(proposal::ExpandLeafProposal, e, pcfg, step)::Union{Nothing, SMCProposalResult}
    # K: uniformly pick a stochastic leaf
    leaves = descendants(e -> num_internal_nodes(e) == 0 && (!proposal.select_random_only || is_random(e.rhs)), e)
    length(leaves) == 0 && return nothing # indicates it's deterministic
    selected = leaves[rand(1:length(leaves))]

    # K: sample a `replacement_size` replacement
    replacement = random(fixed_size_dist, pcfg, proposal.replacement_size, from_lhs_detached(selected))
    logprior_replacement = logprob(fixed_size_dist, pcfg, proposal.replacement_size, replacement)
    logK = -log(length(leaves)) + logprior_replacement

    # L: select a stochastic leaf replacement
    logprior_selected = if proposal.select_random_only
        idx = idx_constrained(selected.expr.child, pcfg.prod_of_sym[selected.lhs].rhs_all)
        probs = pcfg.prod_of_sym[selected.lhs].probs_leaf_novar_random
        log(probs[idx])
    else
        logprob(fixed_size_dist, pcfg, 0, selected) # for later
    end

    # mutate now, only after calculating that part of `L` above
    e = replace_parsed_expr(e, selected, replacement)

    # L: uniformly pick a size `replacement_size` node
    candidates = descendants(e -> num_internal_nodes(e) == proposal.replacement_size, e)
    logL = -log(length(candidates)) + logprior_selected

    return SMCProposalResult(e, logK, logL, Path[selected.expr.path])
end

@kwdef struct ExpandLeafMultistepProposal
    select_random_only::Bool = true # rational rules needs this false
    # size_schedule::Vector{Int} # schedule for max size
    init_size::Int = 0
end

function propose(proposal::ExpandLeafMultistepProposal, e, pcfg, step)::Union{Nothing, SMCProposalResult}
    # K: uniformly pick a stochastic leaf
    leaves = descendants(e -> num_internal_nodes(e) == 0 && (!proposal.select_random_only || is_random(e.rhs)), e)
    length(leaves) == 0 && return nothing # indicates it's deterministic
    selected = leaves[rand(1:length(leaves))]

    # K: sample a size to use as `replacement_size` (uniform), with leaf (0) as smallest option
    # max_replacement_size = proposal.size_schedule[step] - num_internal_nodes(e)
    max_replacement_size = (proposal.init_size + step) - num_internal_nodes(e)
    @assert max_replacement_size >= 0
    replacement_size = rand(0:max_replacement_size)

    # K: sample a `replacement_size` replacement
    replacement = random(fixed_size_dist, pcfg, replacement_size, from_lhs_detached(selected))
    logprior_replacement = logprob(fixed_size_dist, pcfg, replacement_size, replacement)
    logK = -log(max_replacement_size+1) + -log(length(leaves)) + logprior_replacement

    # L: select a stochastic leaf replacement
    logprior_selected = if proposal.select_random_only
        idx = idx_constrained(selected.expr.child, pcfg.prod_of_sym[selected.lhs].rhs_all)
        probs = pcfg.prod_of_sym[selected.lhs].probs_leaf_novar_random
        log(probs[idx])
    else
        logprob(fixed_size_dist, pcfg, 0, selected) # for later
    end

    # mutate now, only after calculating that part of `L` above
    e = replace_parsed_expr(e, selected, replacement)

    # L: uniformly pick any node.
    candidates = descendants(e)
    logL = -log(length(candidates)) + logprior_selected

    return SMCProposalResult(e, logK, logL, Path[selected.expr.path])
end



is_var(e::PExpr) = e isa Var || e isa App && getchild(e, 1) isa Var
get_var_idx(e::PExpr)::Int = e isa Var ? e.idx : getchild(e, 1).idx

function idx_constrained(e::PExpr, prods)::Int
    idx = nothing
    for (i, rhs) in enumerate(prods)
        if is_var(rhs) && is_var(e)
            @assert isnothing(idx) "multiple matches for $e: $(prods[i]) and $(prods[idx])"
            idx = i
        elseif !is_var(rhs) && unifies(rhs.expr, e)
            # @show prods[i]
            # @show e
            # isnothing(idx) || @show prods[idx]
            @assert isnothing(idx) "multiple matches for $e: $(prods[i]) and $(prods[idx])"
            idx = i
        end
    end
    @assert !isnothing(idx)
    idx
end


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


function build_var_rhs(e::GExpr, var_idx::Int, pcfg::Grammar)::GrammarProdRHS
    # build the little ProdRHS for the variable use
    var_type = e.expr.env[var_idx]
    var_expr = Var(var_idx, e.expr.env_names[var_idx])
    sym_paths = Tuple{Symbol,Path}[]
    for (i, argtype) in enumerate(arg_types(var_type))
        sym = pcfg.sym_of_type[argtype]
        var_expr = App(var_expr, AuxCFGSymbol(sym))
        push!(sym_paths, (sym,Int[i+1])) # i=1 is `f` so i+1 gets argument i
    end
    GrammarProdRHS(
        var_expr,
        sym_paths,
        true, # is_var
        false, # is_random
    )
end

function make_child!(e::GExpr, path::Path, sym::Symbol)
    child_se = copy(e.expr) # doesnt copy the Expr just the SubExpr
    subexpr!(child_se, path)
    child = GExpr(sym, child_se)
    push!(e.children, child)
    child.parent = (e, length(e.children))
    child
end

function set_underlying_expr!(e::GExpr, expr::PExpr)
    e.expr.child = expr
    if !isnothing(e.parent)
        # if we have a parent, setchild to mutate their expr. note that this
        # mutation will automatically propagate to ancestors since we all share the
        # same Expr object
        (parent, _) = e.parent
        setchild!(parent.expr.child, relative_path(parent.expr, e.expr), e.expr.child)
    end
end

function parse_gexpr!(pcfg::Grammar, e::GExpr)::GExpr
    prods = pcfg.prod_of_sym[e.lhs].rhs_all

    # parse the index
    idx = idx_constrained(e.expr.child, prods)
    rhs = prods[idx]

    # if it's a variable, parse the variable and any App-structure if it's an application of a variable
    if is_var(rhs)
        var_choices = valid_vars_all(pcfg, e)
        var_idx = get_var_idx(e.expr.child)
        @assert var_idx in var_choices
        rhs = build_var_rhs(e, var_idx, pcfg)
    end

    e.rhs = rhs
    e.rhs_idx = idx

    # recursively parse children
    for (sym, path) in rhs.symbol_paths
        child = make_child!(e, path, sym)
        parse_gexpr!(pcfg, child)
    end
    e
end



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
