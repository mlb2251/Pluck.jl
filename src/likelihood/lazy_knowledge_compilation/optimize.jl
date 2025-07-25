export optimize

function optimize(exprs, η, init, n_steps; kwargs...)
    npartials = length(init)
    cfg = LazyKCConfig(; kwargs..., vector_size=npartials, detailed_results=true, free_manager=false, dual=true)
    rets = [compile(e, cfg) for e in exprs]

    # initialize metaparameters
    metaparam_vals = init
    for ret in rets
        set_metaparams!(ret.state, metaparam_vals)
    end

    for i=1:n_steps
        # get gradients
        all_normalized_results = [normalize_dual([(v, RSDD.bdd_wmc(bdd)) for (v, bdd) in ret.raw_worlds]) for ret in rets]
        all_true_duals = [get_true_result(result) for result in all_normalized_results]
        # logsumexp over all expressions, so we're maximizing the product of the likelihoods
        true_dual = logsumexp_dual(all_true_duals)
        # update metaparams
        metaparam_vals = clamp.(metaparam_vals + η * true_dual[2], 0.0, 1.0)
        # update bdd weights
        for ret in rets
            set_metaparams!(ret.state, metaparam_vals)
        end
    end
    # get prob given metaparams
    all_normalized_results = [normalize_dual([(v, RSDD.bdd_wmc(bdd)) for (v, bdd) in ret.raw_worlds]) for ret in rets]
    all_true_duals = [get_true_result(result) for result in all_normalized_results]
    true_dual = logsumexp_dual(all_true_duals)

    for ret in rets
        free_bdd_manager(ret.state.manager)
    end
    return true_dual, metaparam_vals
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