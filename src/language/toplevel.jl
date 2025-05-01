export load_pluck_file, parse_toplevel

# Parse a single constructor definition of form (Constructor arg1 arg2 ...)
function parse_constructor(tokens)
    @assert tokens[1] == "(" "Expected opening paren in constructor definition"
    @assert tokens[end] == ")" "Expected closing paren in constructor definition"

    # Get constructor name and args (if any)
    constructor = Symbol(tokens[2])
    args = Symbol[Symbol(arg) for arg in tokens[3:end-1]]

    constructor => args
end

function print_query_results(results, query_str; save = false)
    printstyled("$query_str:\n", color=:yellow, bold=true)

    if isempty(results)
        printstyled("  impossible constraint", bold=true)
        return
    end

    max_val_length = maximum(length(string(v)) for (v, _) in results)
    # Sort results by probability
    sorted_results = sort(results, by = x -> x[2], rev = true)
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

function marginal_query(val, state)
    ret, _ = evaluate(val.args[1], state.manager.BDD_TRUE, state)
    full_ret = infer_full_distribution(ret, state)
    results = [v => RSDD.bdd_wmc(b) for (v, b) in full_ret]
    return results
end

function posterior_query(val, state)
    env = Any[val.args[1], val.args[2]]
    given_expr = App(App(Defined(:given), Var(2, :b)), Var(1, :a))
    # TODO: reconsider strict order index to use?
    ret, _ = traced_compile_inner(given_expr, env, state.manager.BDD_TRUE, state, 0)
    full_ret = infer_full_distribution(ret, state)
    results = normalize([v => RSDD.bdd_wmc(b) for (v, b) in full_ret])
    return results
end

# Add this helper function to process queries
function process_query(expr::PExpr, query_str::AbstractString; kwargs...)
    state = LazyKCState(; kwargs...)
    ret, used_information = traced_compile_inner(expr, EMPTY_ENV, state.manager.BDD_TRUE, state, 0)

    if length(ret) != 1
        error("A query must either be a Marginal, Posterior, or PosteriorSample query, got $(expr).")
    end

    val, bdd = first(ret)

    @assert RSDD.bdd_is_true(bdd) "Query expression must evaluate to either (Marginal ...), (Posterior ...), or (PosteriorSample ...) with probability 1."

    if val.constructor == :Marginal
        results = marginal_query(val, state)
        print_query_results(results, query_str; save = state.cfg.results_file)

    elseif val.constructor == :Posterior
        results = posterior_query(val, state)
        print_query_results(results, query_str; save = state.cfg.results_file)
    elseif val.constructor == :PosteriorSamples
        # Get a single sample from the posterior
        results = posterior_sample(val, state)
        # Print the sample
        printstyled("$query_str:\n", color=:yellow, bold=true)
        for (i, result) in enumerate(results)
            printstyled("  $result\n", bold=true)
        end
    elseif val.constructor == :AdaptiveRejection
        results = adaptive_rejection_sampling(val, state)
        # Print the sample
        printstyled("$query_str:\n", color=:yellow, bold=true)
        printstyled("  $results\n", bold=true)
    else
        error("Expected Marginal, Posterior, or PosteriorSample query, got $(val.constructor)")
    end

    println()

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

function detokenize(tokens)
    result_str = ""
    for (i, token) in enumerate(tokens)
        if token == "(" || token == ")"
            result_str *= token
            if token == ")" && i < length(tokens) && tokens[i+1] == "("
                result_str *= " "
            end
        else
            if i > 1 && tokens[i-1] != "("
                result_str *= " "
            end
            result_str *= token
            if i < length(tokens) && tokens[i+1] != ")"
                result_str *= " "
            end
        end
    end
    return result_str
end

function parse_and_process_query(tokens, defs)
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
            query_expr, tokens = parse_expr_inner(query_tokens, defs, [])
            display_str = query_tokens[1]
        else
            # Name followed by expression name
            display_str = query_tokens[1]
            query_expr, tokens = parse_expr_inner(query_tokens[2:end], defs, [])
        end
    elseif first_paren == 1
        # Starts with parenthesis - single expression
        query_expr, rest_query_tokens = parse_expr_inner(query_tokens, defs, [])
        @assert length(rest_query_tokens) == 1 "Expected empty rest_query_tokens"
        # Format expression as before
        display_str = detokenize(query_tokens)
    else
        # Name followed by expression
        display_str = query_tokens[1]
        query_expr, rest_query_tokens = parse_expr_inner(view(query_tokens, 2:length(query_tokens)), defs, [])
        @assert length(rest_query_tokens) == 1 "Expected empty rest_query_tokens"
    end

    @assert tokens[end_idx] == ")" "Expected closing paren"

    # Process the query and get result
    result = process_query(query_expr, display_str)

    return (:query, query_expr, result), view(tokens, end_idx+1:length(tokens))

end

function parse_and_process_define_function(tokens, defs)
    # Function definition form
    tokens = view(tokens, 2:length(tokens))
    fname = Symbol(tokens[1])
    # Set up dummy binding before parsing the body
    defs[fname] = Definition(fname, DUMMY_EXPRESSION)

    tokens = view(tokens, 2:length(tokens))
    # Collect args and parse body as before...
    args = Symbol[]
    new_env = []
    while tokens[1] != ")"
        arg = Symbol(tokens[1])
        push!(args, arg)
        new_env = [tokens[1], new_env...]
        tokens = view(tokens, 2:length(tokens))
    end
    tokens = view(tokens, 2:length(tokens))

    # For zero-argument case, add dummy unit variable
    if isempty(args)
        new_env = ["_", new_env...]
    end

    # Parse body with updated environment
    body, tokens = parse_expr_inner(tokens, defs, new_env)

    # @show body
    # Construct lambda expression
    expr = body
    if isempty(args)
        expr = Abs(expr, Symbol("_"))
    else
        for arg in reverse(args)
            expr = Abs(expr, arg)
        end
    end

    @assert tokens[1] == ")" "Expected closing paren when defining $fname, instead got: $(tokens[1:min(length(tokens), 10)])"

    # Update the definition with the actual expression
    defs[fname] = Definition(fname, expr)

    return (:define, fname, expr), view(tokens, 2:length(tokens))
end

function parse_and_process_define_value(tokens, defs)
    # Regular (define x e) form
    name = Symbol(tokens[1])
    # Set up dummy binding
    defs[name] = Definition(name, DUMMY_EXPRESSION)

    tokens = view(tokens, 2:length(tokens))
    expr, tokens = parse_expr_inner(tokens, defs, [])

    @assert tokens[1] == ")" "Expected closing paren"

    # Update with actual expression
    defs[name] = Definition(name, expr)

    return (:define, name, expr), view(tokens, 2:length(tokens))
end

function parse_and_process_define_type(tokens, defs)
    # Parse (define-type name (Constructor1 args...) (Constructor2 args...) ...)
    tokens = view(tokens, 3:length(tokens))

    # Get the type name
    type_name = Symbol(tokens[1])
    tokens = view(tokens, 2:length(tokens))

    # Parse each constructor definition
    constructors = Dict{Symbol,Vector{Symbol}}()
    while tokens[1] != ")"
        # Each constructor is a parenthesized list
        end_idx = findfirst(t -> t == ")", tokens)
        constructor, args = parse_constructor(tokens[1:end_idx])
        constructors[constructor] = args
        tokens = view(tokens, end_idx+1:length(tokens))
    end

    # Define the type
    spt = define_type!(type_name, constructors)

    return (:define_type, spt), view(tokens, 2:length(tokens))
end

# Modify process_toplevel_form to handle queries
function process_toplevel_form(tokens, defs)
    if length(tokens) == 0
        error("unexpected end of input")
    end

    token = tokens[1]
    if token != "("
        # Ordinary expression without parentheses
        expr, rest = parse_expr_inner(tokens, defs, [])
        return (:expr, expr), rest
    end

    # Peek at what follows the opening paren
    if tokens[2] == "query"
        return parse_and_process_query(tokens, defs)

    elseif tokens[2] == "define-type"
        return parse_and_process_define_type(tokens, defs)

    elseif tokens[2] == "define"
        # Now consume the paren and "define"
        tokens = view(tokens, 3:length(tokens))

        # Get the name being defined
        if tokens[1] == "("
            return parse_and_process_define_function(tokens, defs)

        else
            return parse_and_process_define_value(tokens, defs)
            
        end
    else
        # Regular expression in parentheses
        expr, rest = parse_expr_inner(tokens, defs, [])
        return (:expr, expr), rest
    end
end

# Parse and process a sequence of top-level forms
function parse_toplevel(s::String, defs=DEFINITIONS)
    tokens = tokenize(s)
    forms = []

    while !isempty(tokens)
        form, tokens = process_toplevel_form(tokens, defs)
        push!(forms, form)
    end

    forms
end

# Load and process definitions from a file
function load_pluck_file(filename::String)
    content = read(filename, String)
    parse_toplevel(content)
end