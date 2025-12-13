abstract type InferenceMode end
struct ExactInference <: InferenceMode end
struct SMCInference <: InferenceMode
    k::Int
end


# Add this helper function to process queries
function eval_query(val, state::LazyKCState)
    mode = ExactInference()

    if val.constructor == :SubproblemMonteCarlo
        sample_k_state = SampleValueState(nothing, [], nothing, false, state.manager)
        k, = from_value(force_value(evaluate(val.args[1], nothing, sample_k_state), nothing, sample_k_state))
        mode = SMCInference(k)

        ret, used_information = evaluate(val.args[2], state.manager.BDD_TRUE, state)
        @assert length(ret) == 1 "SubproblemMonteCarlo must have a second argument that deterministically evaluates to another query, got $(val.args[2])."
        val, bdd = ret[1]
        @assert RSDD.bdd_is_true(bdd) "SubproblemMonteCarlo must have a second argument that deterministically evaluates to another query, got $(val.args[2])."
    end

    if val.constructor == :Marginal
        return marginal_query(val, state, mode)
    elseif val.constructor == :Posterior
        return posterior_query(val, state, mode)
    elseif val.constructor == :PosteriorSamples
        # Get a single sample from the posterior
        @assert mode isa ExactInference "SubproblemMonteCarlo has not yet been implemented for PosteriorSamples queries."
        return posterior_sample(val, state)
    elseif val.constructor == :AdaptiveRejection
        return adaptive_rejection_sampling(val, state)
    else
        error("Expected Marginal, Posterior, or PosteriorSample query, got $(val.constructor)")
    end
end

function marginal_query(val, state, mode::ExactInference)
    ret, _ = evaluate(val.args[1], state.manager.BDD_TRUE, state)
    full_ret = infer_full_distribution(ret, state)
    results = [v => RSDD.bdd_wmc(b) for (v, b) in full_ret]
    return results
end

function marginal_query(val, state, mode::SMCInference)
    ret, _ = evaluate(val.args[1], state.manager.BDD_TRUE, state)
    ret_thunk_union, normalizer = subproblem_monte_carlo(ret, mode.k, state)
    ret, _ = evaluate(ret_thunk_union, state.manager.BDD_TRUE, state)
    full_ret = infer_full_distribution(ret, state)
    results = [v => RSDD.bdd_wmc(b) for (v, b) in full_ret]
    return results
end

function posterior_query(val, state, mode::ExactInference)
    env = EnvCons(:a, val.args[1], EnvCons(:b, val.args[2], EnvNil()))
    given_expr = parse_expr("(given b a)"; env=["a", "b"])
    # TODO: reconsider strict order index to use?
    ret, _ = traced_compile_inner(given_expr, env, state.manager.BDD_TRUE, state, 0)
    full_ret = infer_full_distribution(ret, state)
    results = normalize([v => RSDD.bdd_wmc(b) for (v, b) in full_ret])
    return results
end

function posterior_query(val, state, mode::SMCInference)
    env = EnvCons(:a, val.args[1], EnvCons(:b, val.args[2], EnvNil()))
    given_expr = parse_expr("(given-suspend b a)"; env=["a", "b"])
    ret, _ = traced_compile_inner(given_expr, env, state.manager.BDD_TRUE, state, 0)
    ret_thunk_union, normalizer = subproblem_monte_carlo(ret, mode.k, state)
    ret, _ = evaluate(ret_thunk_union, state.manager.BDD_TRUE, state)
    full_ret = infer_full_distribution(ret, state)
    results = normalize([v => RSDD.bdd_wmc(b) for (v, b) in full_ret])
    return results
end