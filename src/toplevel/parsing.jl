abstract type ToplevelHead <: Head end

struct DefineOp <: ToplevelHead
    name::Symbol
    expr::PExpr
end

struct ToplevelPassOp <: ToplevelHead end

struct IncludeOp <: ToplevelHead
    path::String
end

struct QueryOp <: ToplevelHead
    name::String
    query::PExpr
end

struct AssertQueryOp <: ToplevelHead
    name::String
    query::PExpr
    expected::Vector{Tuple{String, Float64}}
end


# forbid compiling toplevel heads
compile_inner(expr::PExpr{H}, env, path_condition, state) where H <: ToplevelHead = error("ToplevelHeads cannot be compiled")

function parse_toplevel(tokens, state)
    @assert tokens[1] == "(" || parse_error(state, tokens, "expected opening paren at start of toplevel expression")
    tokens = view(tokens, 2:length(tokens))

    token = tokens[1]

    if token == "include"
        # Special parsing for include: (include "path/to/file.pluck")
        tokens = view(tokens, 2:length(tokens))

        path_token = tokens[1]
        (startswith(path_token, "\"") && endswith(path_token, "\"")) || parse_error(state, tokens, "include expects a string literal path")
        rel_path = path_token[2:end-1]

        # Resolve relative paths using the base directory of the current file
        full_path = isabspath(rel_path) ? rel_path : joinpath(state.base_dir, rel_path)

        # Don't load at parse time - let it happen at eval time

        tokens = view(tokens, 2:length(tokens))
        tokens[1] == ")" || parse_error(state, tokens, "expected closing paren in include")

        # Return IncludeOp with path as ConstNative
        return IncludeOp(full_path)(), view(tokens, 2:length(tokens))
    elseif token == "define-type"
        # Special parsing for define-type: (define-type name (Constructor1 args...) ...)
        tokens = view(tokens, 2:length(tokens))

        # Get the type name
        type_name = Symbol(tokens[1])
        tokens = view(tokens, 2:length(tokens))

        # Parse each constructor definition
        while tokens[1] != ")"
            # Each constructor is a parenthesized list
            end_idx = findfirst(t -> t == ")", tokens)
            constructor, args = parse_constructor(tokens[1:end_idx], state)
            tokens = view(tokens, end_idx+1:length(tokens))
        end

        tokens[1] == ")" || parse_error(state, tokens, "expected closing paren in define-type")

        # Return DefineTypeOp with type name and constructors as ConstNative
        return ToplevelPassOp()(), view(tokens, 2:length(tokens))
    elseif token == "define"
        # Special parsing for define: (define (fname args...) body) or (define x expr)
        tokens = view(tokens, 2:length(tokens))

        if tokens[1] == "("
            # Function definition: (define (fname args...) body)
            tokens = view(tokens, 2:length(tokens))
            fname = Symbol(tokens[1])
            tokens = view(tokens, 2:length(tokens))

            # Collect args
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

            # Set up dummy binding so the body can reference the function recursively
            state.defs[fname] = Definition(fname, DUMMY_EXPRESSION)

            # Parse body with updated environment using parse_with_env to preserve env_stack
            body, tokens = parse_with_env(tokens, state, new_env)

            # Construct lambda expression
            expr = body
            if isempty(args)
                expr = Abs(Symbol("_"))(expr)
            else
                for arg in reverse(args)
                    expr = Abs(arg)(expr)
                end
            end

            tokens[1] == ")" || parse_error(state, tokens, "expected closing paren in define")

            # Return DefineOp with fname as ConstNative and lambda as expr
            return DefineOp(fname, expr)(), view(tokens, 2:length(tokens))
        else
            # Value definition: (define x expr)
            name = Symbol(tokens[1])
            tokens = view(tokens, 2:length(tokens))

            # Set up dummy binding so the expression can reference the name recursively
            state.defs[name] = Definition(name, DUMMY_EXPRESSION)

            # Parse expression - just use current state which already has the right env_stack
            expr, tokens = parse_expr_inner(tokens, state)

            tokens[1] == ")" || parse_error(state, tokens, "expected closing paren in define")

            # Return DefineOp with name as ConstNative
            return DefineOp(name, expr)(), view(tokens, 2:length(tokens))
        end
    elseif token == "query"
        tokens = view(tokens, 2:length(tokens))
        end_idx = find_ending_paren(tokens)
        query_tokens = view(tokens, 1:end_idx)
    
        if findfirst(t -> t == "(", query_tokens) == 1
            # Name is the entire expression
            name = detokenize(query_tokens)
        else
            # Name followed by expression
            name = String(query_tokens[1])[2:end]
            query_tokens = view(query_tokens, 2:length(query_tokens))
        end
    
        query_body, rest_query_tokens = parse_expr_inner(query_tokens, state)
        length(rest_query_tokens) == 1 && query_tokens[end] == ")" || parse_error(state, rest_query_tokens, "expected closing paren and nothing else")
    
        query_expr = QueryOp(name, query_body)()
    
        return query_expr, view(tokens, end_idx+1:length(tokens))
    elseif token == "assert-query"
        tokens = view(tokens, 2:length(tokens))

        # Parse name (quoted symbol like 'name)
        name = String(tokens[1])[2:end]
        tokens = view(tokens, 2:length(tokens))

        # Parse query expression
        query_body, tokens = parse_expr_inner(tokens, state)

        # Parse expected (value, probability) pairs until closing paren
        expected = Tuple{String, Float64}[]
        while tokens[1] != ")"
            tokens[1] == "(" || parse_error(state, tokens, "expected opening paren for expected pair")
            tokens = view(tokens, 2:length(tokens))

            # Parse value: could be a parenthesized expression like (False),
            # a bracketed list like [2, 4, 6], or a bare token like 9 or "goat"
            if tokens[1] == "("
                end_idx = find_ending_paren(view(tokens, 2:length(tokens)))
                val_str = detokenize_value(view(tokens, 1:end_idx+1))
                tokens = view(tokens, end_idx+2:length(tokens))
            elseif tokens[1] == "["
                end_idx = find_ending_bracket(view(tokens, 2:length(tokens)))
                val_str = detokenize_value(view(tokens, 1:end_idx+1))
                tokens = view(tokens, end_idx+2:length(tokens))
            else
                val_str = String(tokens[1])
                tokens = view(tokens, 2:length(tokens))
            end

            # Parse probability
            prob = parse(Float64, tokens[1])
            tokens = view(tokens, 2:length(tokens))

            tokens[1] == ")" || parse_error(state, tokens, "expected closing paren for expected pair")
            tokens = view(tokens, 2:length(tokens))

            push!(expected, (val_str, prob))
        end

        tokens[1] == ")" || parse_error(state, tokens, "expected closing paren in assert-query")

        return AssertQueryOp(name, query_body, expected)(), view(tokens, 2:length(tokens))
    else
        parse_error(state, tokens, "unexpected token at toplevel: $token")
    end
end
