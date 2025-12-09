export load_pluck_file, eval_forms, sample_output, @pluck_str


abstract type InferenceMode end
struct ExactInference <: InferenceMode end
struct SMCInference <: InferenceMode
    k::Int
end

"""
pluck"..." is equivalent to eval_forms("...")
"""
macro pluck_str(str)
    # Handle string interpolation
    # interpolated_str = Meta.parse("\"$str\"")
    :(eval_forms($(esc(str))))
end

function print_query_results(results, query_str; save = false)
    printstyled("$query_str:\n", color=:yellow, bold=true)

    if isempty(results)
        printstyled("  impossible constraint", bold=true)
        return
    end

    max_val_length = maximum(length(string(v)) for (v, _) in results)

    # Sort results by probability
    function _sortkey(val)
        if isa(val, Number)
            return (0, val)
        elseif isa(val, AbstractString)
            return (1, val)
        else
            return (2, string(val))
        end
    end

    sorted_results = sort(results, by = x -> (-x[2], _sortkey(x[1])))
    for (v, p) in sorted_results
        if p == 0
            continue
        end
        val_str = string(v)
        padding = " " ^ (max_val_length - length(val_str) + 2)  # +2 for minimum spacing
        printstyled("  $val_str", bold=true)
        printstyled(padding)
        printstyled("$p\n", color=:cyan)
    end


    if !isnothing(save)
        results_json = (query_str=query_str,
                        results=[(prob=p, val=v) for (v, p) in sorted_results])

        # check if file exists
        prev_results = []
        if isfile(save)
            prev_results = JSON.parse(read(save, String))
        end
        push!(prev_results, results_json)
        open(save, "w") do f
            JSON.print(f, prev_results)
        end
        println("http://localhost:8000/html/factored/factored.html?path=$save")
        println("Wrote $save")
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


function sample_output(expr::String; kwargs...)
    process_query("(PosteriorSamples $expr true 1)"; silent=true, kwargs...)[1]
end

function process_query(expr::String, args...; env=EMPTY_ENV, kwargs...)
    process_query(parse_expr(expr; env=parse_env(env)), args...; env=env, kwargs...)
end

# Add this helper function to process queries
function process_query(expr::PExpr, query_str::AbstractString=string(expr); silent=false, env=EMPTY_ENV, kwargs...)
    state = LazyKCState(; kwargs...)
    ret, used_information = traced_compile_inner(expr, env, state.manager.BDD_TRUE, state, 0)

    if length(ret) != 1
        error("A query must either be a Marginal, Posterior, or PosteriorSample query, got $(expr).")
    end

    val, bdd = first(ret)

    @assert RSDD.bdd_is_true(bdd) "Query expression must evaluate to either (Marginal ...), (Posterior ...), or (PosteriorSample ...) with probability 1."

    mode = ExactInference()

    if val.constructor == :SubproblemMonteCarlo
        sample_k_state = SampleValueState(nothing, [], nothing, false, state.manager)
        k, = from_value(force_value(evaluate(val.args[1], nothing, sample_k_state), nothing, sample_k_state))
        mode = SMCInference(k)

        ret, used_information = evaluate(val.args[2], state.manager.BDD_TRUE, state)
        if length(ret) != 1
            error("SubproblemMonteCarlo must have a second argument that deterministically evaluates to another query, got $(val.args[2]).")
        end
        val, bdd = first(ret)
    end

    if val.constructor == :Marginal
        results = marginal_query(val, state, mode)
        silent || print_query_results(results, query_str; save = state.cfg.results_file)
    elseif val.constructor == :Posterior
        results = posterior_query(val, state, mode)
        silent || print_query_results(results, query_str; save = state.cfg.results_file)
    elseif val.constructor == :PosteriorSamples
        # Get a single sample from the posterior
        @assert mode isa ExactInference "SubproblemMonteCarlo has not yet been implemented for PosteriorSamples queries."
        results = posterior_sample(val, state)
        # Print the sample
        if !silent
            printstyled("$query_str:\n", color=:yellow, bold=true)
            for (i, result) in enumerate(results)
                printstyled("  $result\n", bold=true)
            end
        end
    elseif val.constructor == :AdaptiveRejection
        results = adaptive_rejection_sampling(val, state)
        # Print the sample
        silent || printstyled("$query_str:\n", color=:yellow, bold=true)
        silent || printstyled("  $results\n", bold=true)
    else
        error("Expected Marginal, Posterior, or PosteriorSample query, got $(val.constructor)")
    end

    silent || println()

    return results
end

function find_ending_paren(tokens)
    depth = 1
    end_idx = 1
    while depth > 0 && end_idx <= length(tokens)
        if tokens[end_idx] == "("
            depth += 1
        elseif tokens[end_idx] == ")"
            depth -= 1
        end
        end_idx += 1
    end
    return end_idx-1
end

function parse_and_process_query(tokens, defs; silent=false, base_dir=pwd())
    # Skip past "(" and "query"
    tokens = view(tokens, 3:length(tokens))
    
    # Find the end of the query form
    end_idx = find_ending_paren(tokens)
    query_tokens = tokens[1:end_idx]
    
    # Count tokens before first parenthesis
    first_paren = findfirst(t -> t == "(", query_tokens)
    if isnothing(first_paren)
        # No parentheses - must be one or two names
        if length(query_tokens) == 1
            # Single name case
            query_expr, tokens = parse_expr_inner(query_tokens, ParseState(defs, [], base_dir))
            display_str = query_tokens[1]
        else
            # Name followed by expression name
            display_str = query_tokens[1]
            query_expr, tokens = parse_expr_inner(query_tokens[2:end], ParseState(defs, [], base_dir))
        end
    elseif first_paren == 1
        # Starts with parenthesis - single expression
        query_expr, rest_query_tokens = parse_expr_inner(query_tokens, ParseState(defs, [], base_dir))
        @assert length(rest_query_tokens) == 1 "Expected empty rest_query_tokens"
        # Format expression as before
        display_str = detokenize(query_tokens)
    else
        # Name followed by expression
        display_str = query_tokens[1]
        query_expr, rest_query_tokens = parse_expr_inner(view(query_tokens, 2:length(query_tokens)), ParseState(defs, [], base_dir))
        @assert length(rest_query_tokens) == 1 "Expected empty rest_query_tokens"
    end

    @assert tokens[end_idx] == ")" "Expected closing paren"

    # Process the query and get result
    result = process_query(query_expr, display_str; silent=silent)

    return (:query, query_expr, result), view(tokens, end_idx+1:length(tokens))

end


# Modify eval_form to handle queries
function eval_form(tokens, defs; silent=false, base_dir=pwd())
    if length(tokens) == 0
        error("unexpected end of input")
    end

    token = tokens[1]
    if token != "("
        error("Expected opening paren at start of toplevel form, got: $token")
    end

    # Peek at what follows the opening paren
    if tokens[2] == "query"
        return parse_and_process_query(tokens, defs; silent=silent, base_dir=base_dir)

    # elseif tokens[2] == "include"
    #     return parse_and_process_include(tokens, defs; base_dir=base_dir, silent=silent)
    end
    
    # Regular expression in parentheses - wrap in Marginal
    expr, rest = parse_expr_inner(tokens, ParseState(defs, [], base_dir))
    query_expr = Construct(:Marginal)(expr)
    result = process_query(query_expr; silent=true)
    return (:expr, expr, result), rest
end

# Parse and process a sequence of top-level forms
function eval_forms(s::String, defs=DEFINITIONS; silent=false, base_dir=pwd())
    tokens = tokenize(s)
    while !isempty(tokens)
        _, tokens = eval_form(tokens, defs; silent=silent, base_dir=base_dir)
    end
    nothing
end

# Load and process definitions from a file
function load_pluck_file(filename::String)
    content = read(filename, String)
    eval_forms(content; base_dir=dirname(abspath(filename)))
end
