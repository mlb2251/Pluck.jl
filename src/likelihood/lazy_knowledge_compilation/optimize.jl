export optimize

using .RSDD

function optimize(exprs, η, init, n_steps; kwargs...)
    npartials = length(init)
    cfg = LazyKCConfig(; kwargs..., vector_size=npartials, detailed_results=true, free_manager=false, dual=true)
    rets = [compile(e, cfg) for e in exprs]

    # initialize results
    normalized_results = Vector{Tuple{Any, Tuple{Float64, Vector{Float64}}}}()
    log_true_prob_dual = (0, [0 for _ ∈ 1:npartials])
    # initialize metaparameters
    metaparam_vals = init
    # initialize bdd weights
    for ret in rets
        set_metaparams!(ret.state, metaparam_vals)
    end

    for i=1:n_steps
        # get gradients
        all_normalized_results = [normalize_dual([(v, RSDD.getWmcDual(RSDD.bdd_wmc(bdd))) for (v, bdd) in ret.raw_worlds]) for ret in rets]
        all_true_duals = [get_true_result(result) for result in all_normalized_results]
        # logsumexp over all expressions, so we're maximizing the product of the likelihoods
        log_all_true_duals = log_dual.(all_true_duals)
        log_true_dual = sum_dual(log_all_true_duals)
        true_dual = exp_dual(log_true_dual)
        # update metaparams
        metaparam_vals = clamp.(metaparam_vals + η * true_dual[2], 0.0, 1.0)
        # update bdd weights
        for ret in rets
            set_metaparams!(ret.state, metaparam_vals)
        end
    end
    # get prob given metaparams
    all_normalized_results = [normalize_dual([(v, RSDD.getWmcDual(RSDD.bdd_wmc(bdd))) for (v, bdd) in ret.raw_worlds]) for ret in rets]
    all_true_prob_duals = [[res for res ∈ normalized_results if res[1].constructor == :True][1][2] for normalized_results in all_normalized_results]
    log_all_true_prob_duals = log_dual.(all_true_prob_duals)
    log_true_prob_dual = sum_dual(log_all_true_prob_duals)
    true_prob_dual = exp_dual(log_true_prob_dual)

    for ret in rets
        free_bdd_manager(ret.state.manager)
    end
    return true_prob_dual, metaparam_vals
end

function set_metaparams!(state, metaparam_vals)
    for (var, metaparam) in state.var2metaparam
        p = metaparam_vals[metaparam+1]
        partials_hi = zeros(Float64, state.manager.vector_size)
        partials_lo = zeros(Float64, state.manager.vector_size)
        partials_hi[metaparam+1] = 1.0
        partials_lo[metaparam+1] = -1.0
        set_weight_deriv(
            state.manager.weights, 
            unsigned(var), 
            1.0 - p,
            partials_lo,
            p,
            partials_hi)
    end
end