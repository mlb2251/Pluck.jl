abstract type InferenceMode end
struct ExactInference <: InferenceMode end
struct SMCInference <: InferenceMode
    k::Int
end


# Add this helper function to process queries
function eval_query(val, state::LazyKCState)
    mode = ExactInference()

    if val.constructor == :SubproblemMonteCarlo
        # should be safe to use the same state because we're forced to be deterministic here anyways so it won't write anything to the state
        k, = from_value(force_thunks(toplevel_evaluate(val.args[1], state)))
        mode = SMCInference(k)
        val = deterministic_world(toplevel_evaluate(val.args[2], state))
    end

    if val.constructor == :Marginal
        return thunk_marginal(val.args[1], state, mode)
    elseif val.constructor == :NormalizedMarginal
        return normalize(thunk_marginal(val.args[1], state, mode))
    elseif val.constructor == :Posterior
        return thunk_posterior(val.args[1], val.args[2], state, mode)
    elseif val.constructor == :PosteriorSamples
        # Get a single sample from the posterior
        @assert mode isa ExactInference "SubproblemMonteCarlo has not yet been implemented for PosteriorSamples queries."
        return posterior_sample(val, state)
    elseif val.constructor == :AdaptiveRejection
        return adaptive_rejection_sampling(val, state)
    else
        error("Expected Marginal, NormalizedMarginal, Posterior, or PosteriorSample query, got $(val.constructor)")
    end
end

function thunk_marginal(thunk, state, ::ExactInference)
    # (Marginal e) => simply force and enumerate the thunk `e`
    ret = toplevel_evaluate(thunk, state)
    return wmc(force_thunks(ret.worlds, state))
end

function thunk_marginal(thunk, state, mode::SMCInference)
    # (Marginal e) in subproblem mode => force the thunk `e`, call subproblem_monte_carlo on result, then force and enumerate the result of that
    ret = toplevel_evaluate(thunk, state)
    ret_thunk_union = subproblem_monte_carlo(ret, mode.k)
    ret = toplevel_evaluate(ret_thunk_union, state)
    return wmc(force_thunks(ret.worlds, state))
end

function thunk_posterior(query_thunk, evidence_thunk, state, ::ExactInference)
    e, env = posterior_expr(query_thunk, evidence_thunk, "given")
    ret = toplevel_compile(e; state, env)
    return normalize(wmc(force_thunks(ret.worlds, state)))
end

function thunk_posterior(query_thunk, evidence_thunk, state, mode::SMCInference)
    e, env = posterior_expr(query_thunk, evidence_thunk, "given-suspend")
    ret = toplevel_compile(e; state, env)
    ret_thunk_union = subproblem_monte_carlo(ret, mode.k)
    ret = toplevel_evaluate(ret_thunk_union, state)
    return normalize(wmc(force_thunks(ret.worlds, state)))
end

"""
(Posterior qry evidence) => compile the expression `(given evidence qry)`
"""
function posterior_expr(query_thunk, evidence_thunk, given) # given = "given" or "given-suspend"
    expr = parse_expr("($given evidence qry)"; env=["evidence", "qry"])
    env = EnvCons(:evidence, evidence_thunk, EnvCons(:qry, query_thunk, EnvNil()))
    return expr, env
end


function unnormalized_posterior(val, state, given) # given = "given" or "given-suspend"
    env = EnvCons(:a, val.args[1], EnvCons(:b, val.args[2], EnvNil()))
    given_expr = parse_expr("($given b a)"; env=["a", "b"])
    return toplevel_compile(given_expr; state, env)
end

