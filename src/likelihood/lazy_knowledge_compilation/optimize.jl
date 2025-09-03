export optimize, unnormalized_gradient, logit_log_gradient, logit_linear_gradient, logit_gradient_update, logit_log_gradient_jacobian_adjustment

function unnormalized_gradient(bdd_ptr::Csize_t, params, weights::WmcParams, var2param)
    set_metaparams!(weights, var2param, params)
    wmc_result = RSDD.bdd_wmc_raw(bdd_ptr, weights)
    val, grad = wmc_result
    
    # Compute log, then make safe
    log_val = val > 0 ? log(val) : -1e10  # Large negative instead of -Inf
    safe_grad = val > 0 ? grad ./ val : zeros(length(grad))  # Zero gradient when val=0
    
    return log_val, safe_grad
end

function logit_linear_gradient(bdd_ptr::Csize_t, params, weights::WmcParams, var2param)
    set_metaparams!(weights, var2param, params)
    wmc_result = RSDD.bdd_wmc_raw(bdd_ptr, weights)
    val, grad = wmc_result
    if grad == []
	grad = zeros(length(params))
    end
    logit_grad = grad .* params .* (1.0 .- params)
    return val, logit_grad
end

function logit_log_gradient_jacobian_adjustment(bdd_ptr::Csize_t, params, weights::WmcParams, var2param)
    set_metaparams!(weights, var2param, params)
    wmc_result = RSDD.bdd_wmc_raw(bdd_ptr, weights)
    val, grad = wmc_result
    if grad == []
        grad = zeros(length(params))
    end
    
    # Jacobian determinant for logit transformation: prod(p * (1 - p))
    jacobian_det = prod(params .* (1 .- params))
    adjusted_val = val * jacobian_det
    
    # Correct logit gradient with Jacobian adjustment
    # d/d(logit) log(f(p) * J) = p(1-p) * df/dp / f + (1-2p)
    logit_grad = params .* (1 .- params) .* (grad ./ val) .+ (1 .- 2 .* params)
    
    log_val = adjusted_val > 0 ? log(adjusted_val) : -1e10
    safe_grad = adjusted_val > 0 ? logit_grad : zeros(length(logit_grad))
    return log_val, safe_grad
end

function logit_log_gradient(bdd_ptr::Csize_t, params, weights::WmcParams, var2param)
    set_metaparams!(weights, var2param, params)
    wmc_result = RSDD.bdd_wmc_raw(bdd_ptr, weights)
    val, grad = wmc_result
    if grad == []
	grad = zeros(length(params))
    end
    logit_grad = grad .* params .* (1.0 .- params)
    log_val = val > 0 ? log(val) : -1e10  # Large negative instead of -Inf
    safe_grad = val > 0 ? logit_grad ./ val : zeros(length(logit_grad))  # Zero gradient when val=0
    return log_val, safe_grad
end

function logit_gradient_update(params, gradient, step_size)
    num = params .* exp.(step_size * gradient)
    denom = 1.0 .+ params .* (exp.(step_size * gradient) .- 1.0)
    return num ./ denom
end

function max_native_int_used(e::PExpr)
    max_used = -1 # -1 means no native ints used
    for arg in e.args
        max_used = max(max_used, max_native_int_used(arg))
    end
    max_used
end
function max_native_int_used(e::PExpr{ConstNative})
    e.head.val isa Int && return e.head.val
    return -1
end

function optimize(exprs, η, init, n_steps; kwargs...)
    npartials = length(init)
    cfg = LazyKCConfig(; kwargs..., vector_size=npartials, detailed_results=true, free_manager=false, free_weights=false, dual=true)
    rets = [compile(e, cfg) for e in exprs]

    # initialize metaparameters
    metaparam_vals = init
    for ret in rets
        set_metaparams!(ret.state.manager.weights, ret.state.var2metaparam, metaparam_vals)
    end

    for _=1:n_steps
        # get gradients
	all_true_results = [get_true_result(ret.raw_worlds) for ret in rets]
	all_duals = [isnothing(bdd) ? (0.0, zeros(npartials)) : RSDD.bdd_wmc(bdd) for bdd in all_true_results]
        # logsumexp over all expressions, so we're maximizing the product of the likelihoods
        true_dual = expsumlog_dual(all_duals)
        # update metaparams
        metaparam_vals = clamp.(metaparam_vals + η * true_dual[2], 0.0, 1.0)
        # update bdd weights
        for ret in rets
            set_metaparams!(ret.state.manager.weights, ret.state.var2metaparam, metaparam_vals)
        end
    end
    # get prob given metaparams
    all_normalized_results = [get_true_result(ret.raw_worlds, ret.state.manager.BDD_FALSE) for ret in rets]
    all_true_duals = [RSDD.bdd_wmc(bdd) for bdd in all_normalized_results]
    true_dual = expsumlog_dual(all_true_duals)

    for ret in rets
        free_bdd_manager(ret.state.manager)
        free_wmc_params(ret.state.manager.weights)
    end
    return true_dual, metaparam_vals
end

function set_metaparams!(weights, var2metaparam, metaparam_vals)
    for (var, metaparam) in var2metaparam
        p = metaparam_vals[metaparam+1]
        partials_hi = zeros(Float64, length(metaparam_vals))
        partials_lo = zeros(Float64, length(metaparam_vals))
        partials_hi[metaparam+1] = 1.0
        partials_lo[metaparam+1] = -1.0
        set_weight_deriv(
            weights, 
            unsigned(var), 
            1.0 - p,
            partials_lo,
            p,
            partials_hi)
    end
end
