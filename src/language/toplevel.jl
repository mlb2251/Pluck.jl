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


function print_query_results_by_type(val, results, query_str; save = nothing)
    if val.constructor == :Marginal
        print_query_results(results, query_str; save)
    elseif val.constructor == :Posterior
        print_query_results(results, query_str; save)
    elseif val.constructor == :PosteriorSamples
        printstyled("$query_str:\n", color=:yellow, bold=true)
        for (i, result) in enumerate(results)
            printstyled("  $result\n", bold=true)
        end
    elseif val.constructor == :AdaptiveRejection
        printstyled("$query_str:\n", color=:yellow, bold=true)
        printstyled("  $results\n", bold=true)
    else
        error("printing not supported for query type $(val.constructor)")
    end
    println()
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

    results = eval_query(val, query_str, state)

    if !silent
        print_query_results_by_type(val, results, query_str; save = state.cfg.results_file)
    end
    return results
end

# Add this helper function to process queries
function eval_query(val::Value, query_str, state::LazyKCState)
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

function parse_query_expr(tokens, defs; silent=false, base_dir=pwd())
    @assert tokens[1] == "(" "Expected opening paren at start of query"
    tokens = view(tokens, 2:length(tokens))
    end_idx = find_ending_paren(tokens)
    # Skip past "query"
    @assert tokens[1] == "query" "Expected query keyword"
    query_tokens = view(tokens, 2:end_idx)

    if findfirst(t -> t == "(", query_tokens) == 1
        # Name is the entire expression
        display_str = detokenize(query_tokens)
    else
        # Name followed by expression
        display_str = query_tokens[1]
        @assert String(display_str)[1] == '\'' "Expected query name to be a symbol, got: $display_str"
        query_tokens = view(query_tokens, 2:length(query_tokens))
    end

    query_expr, rest_query_tokens = parse_expr_inner(query_tokens, ParseState(defs, [], base_dir))
    @assert length(rest_query_tokens) == 1 && query_tokens[end] == ")" "Expected closing paren and nothing else, got $(detokenize(rest_query_tokens))"

    return query_expr, display_str, view(tokens, end_idx+1:length(tokens))
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
        query_expr, display_str, rest = parse_query_expr(tokens, defs; silent=silent, base_dir=base_dir)
        silent = false
    else
        # Regular expression in parentheses - wrap in Marginal
        expr, rest = parse_expr_inner(tokens, ParseState(defs, [], base_dir))
        query_expr = Construct(:Marginal)(expr)
        display_str = string(expr)
        silent = true
    end
    
    result = process_query(query_expr, display_str; silent=silent)
    return (:query, query_expr, result), rest
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
