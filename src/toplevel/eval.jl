mutable struct ToplevelEvalState
    defs::Dict{Symbol, Definition}
    parser::ParseState
    silent::Bool
end

# Load and process definitions from a file
function load_pluck_file(filename::String; defs=DEFINITIONS, silent=false)
    content = read(filename, String)
    tokens = tokenize(content)
    parser = ParseState(defs, [], dirname(abspath(filename)), content, filename)
    toplevel_state = ToplevelEvalState(defs, parser, silent)

    while !isempty(tokens)
        expr, tokens = parse_toplevel(tokens, parser)
        eval_toplevel(expr, toplevel_state)
    end
end

function eval_toplevel(expr::PExpr{DefineOp}, toplevel_state)
    toplevel_state.defs[expr.head.name] = Definition(expr.head.name, expr.head.expr)
end

function eval_toplevel(expr::PExpr{DefineTypeOp}, toplevel_state)
    define_type!(expr.head.name, expr.head.constructors)
end

function eval_toplevel(expr::PExpr{IncludeOp}, toplevel_state)
    load_pluck_file(expr.head.path; defs=toplevel_state.defs, silent=toplevel_state.silent)
end



function sample_output(expr::String; kwargs...)
    process_query("(PosteriorSamples $expr true 1)"; silent=true, kwargs...)[1]
end

function traced_compile_deterministic(expr::PExpr, env::Env, state::LazyKCState, strict_order_index::Int)
    res, _ = traced_compile_inner(expr, env, state.manager.BDD_TRUE, state, strict_order_index)
    @assert length(res) == 1 "Expected deterministic compilation to return a single value, got $(res)"
    @assert RSDD.bdd_is_true(res[1][2]) "Expected deterministic compilation to return a value with probability 1, got $(res[1][2])"
    return res[1][1]
end

# Add this helper function to process queries
function eval_toplevel(expr::PExpr{QueryOp}, toplevel_state)
    state = LazyKCState()
    body = traced_compile_deterministic(expr.head.query, EMPTY_ENV, state, 0)
    results = eval_query(body, state)
    if !toplevel_state.silent
        print_query_results_by_type(body, results, expr.head.name)
    end
    return results
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