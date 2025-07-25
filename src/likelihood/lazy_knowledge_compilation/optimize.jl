export optimize

using .RSDD

function optimize(exprs, η, init, n_steps; kwargs...)
    npartials = length(init)
    cfg = LazyKCConfig(; kwargs..., vector_size=npartials, detailed_results=true, free_manager=false)
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
        all_normalized_results = [normalize_dual([(v, RSDD.getWmcDual(RSDD.bdd_wmc(bdd))) for (v, bdd) in ret]) for ret in rets]
        all_true_prob_duals = [[res for res ∈ normalized_results if res[1].constructor == :True][1][2] for normalized_results in all_normalized_results]
        log_all_true_prob_duals = logDual.(all_true_prob_duals)
        log_true_prob_dual = sumDual(log_all_true_prob_duals)
        true_prob_dual = expDual(log_true_prob_dual)
        # update metaparams
        metaparam_vals = clamp.(metaparam_vals + η * true_prob_dual[2], 0.0, 1.0)
        # update bdd weights
        for ret in rets
            set_metaparams!(ret.state, metaparam_vals)
        end
    end
    # get prob given metaparams
    all_normalized_results = [normalize_dual([(v, RSDD.getWmcDual(RSDD.bdd_wmc(bdd))) for (v, bdd) in ret]) for ret in rets]
    all_true_prob_duals = [[res for res ∈ normalized_results if res[1].constructor == :True][1][2] for normalized_results in all_normalized_results]
    log_all_true_prob_duals = logDual.(all_true_prob_duals)
    log_true_prob_dual = sumDual(log_all_true_prob_duals)
    true_prob_dual = expDual(log_true_prob_dual)

    free_bdd_manager(state.manager)
    return true_prob_dual, metaparam_vals
end

function set_metaparams!(state, metaparam_vals)
    for (param, metaparam) in state.param2metaparam
        set_weight_dual(
            state.manager, 
            unsigned(param), 
            unsigned(metaparam), 
            1.0 - metaparam_vals[metaparam+1], 
            metaparam_vals[metaparam+1])
    end
end