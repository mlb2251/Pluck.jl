# Load and process definitions from a file
function load_pluck_file(filename::String)
    content = read(filename, String)
    eval_forms(content; base_dir=dirname(abspath(filename)), filename=filename)
end

function sample_output(expr::String; kwargs...)
    process_query("(PosteriorSamples $expr true 1)"; silent=true, kwargs...)[1]
end


function process_query(expr::String, args...; env=EMPTY_ENV, kwargs...)
    process_query(parse_expr(expr; env=parse_env(env)), args...; env=env, kwargs...)
end

function traced_compile_deterministic(expr::PExpr, env::Env, state::LazyKCState, strict_order_index::Int)
    res, _ = traced_compile_inner(expr, env, state.manager.BDD_TRUE, state, strict_order_index)
    @assert length(res) == 1 "Expected deterministic compilation to return a single value, got $(res)"
    @assert RSDD.bdd_is_true(res[1][2]) "Expected deterministic compilation to return a value with probability 1, got $(res[1][2])"
    return res[1][1]
end

# Add this helper function to process queries
function process_query(expr::PExpr{QueryOp}, query_str::AbstractString=string(expr); silent=false, env=EMPTY_ENV, kwargs...)

    state = LazyKCState(; kwargs...)

    # this is a little weird – we dont allow name compilation to affect body – but also why would you want that.
    name = compile_deterministic(expr.args[1])
    body = traced_compile_deterministic(expr.args[2], env, state, 1)

    results = eval_query(body, state)

    if !silent
        print_query_results_by_type(body, results, name)
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

# Modify eval_form to handle queries
function eval_form(tokens, defs; silent=false, base_dir=pwd(), source="", filename="<unknown>")
    if length(tokens) == 0
        error("unexpected end of input")
    end

    token = tokens[1]
    if token != "("
        error("Expected opening paren at start of toplevel form, got: $token")
    end

    state = ParseState(defs, [], base_dir, source, filename)
    query_expr, rest = parse_expr_inner(tokens, state)
    if tokens[2] != "query"
        # implicitly wrap in a Marginal Query
        name_expr = ConstNative(Symbol(string(query_expr)))()
        body_expr = Construct(:Marginal)(query_expr)
        query_expr = QueryOp()(name_expr, body_expr)
        silent = true
    end

    result = process_query(query_expr; silent=silent)
    return (:query, query_expr, result), rest
end

# Parse and process a sequence of top-level forms
function eval_forms(s::String, defs=DEFINITIONS; silent=false, base_dir=pwd(), filename="<unknown>")
    tokens = tokenize(s)
    while !isempty(tokens)
        _, tokens = eval_form(tokens, defs; silent=silent, base_dir=base_dir, source=s, filename=filename)
    end
    nothing
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