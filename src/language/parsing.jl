export parse_expr


parse_expr(s::String) = parse_expr(s, DEFINITIONS)

function parse_expr(s::String, defs)
    tokens = tokenize(s)
    expr, rest = parse_expr_inner(tokens, defs, [])
    @assert isempty(rest)
    return expr
end

function const_to_expr(v::Int)
    parse_expr(pluck_nat(v))
end

const_to_expr(v::Float64) = ConstReal(v)
const_to_expr(v::Bool) =
    v ? Construct(:True, Symbol[]) : Construct(:False, Symbol[])


# Parse from Scheme notation (string) into PExpr
function tokenize(s)
    # First remove line comments
    lines = split(s, '\n')
    processed_lines = String[]
    for line in lines
        # Find comment start if it exists
        comment_start = findfirst(";;", line)
        if isnothing(comment_start)
            push!(processed_lines, line)
        else
            # Keep only the part before the comment
            push!(processed_lines, line[1:comment_start.start-1])
        end
    end
    s = join(processed_lines, " ")

    # Now process the comment-free string as before
    s = replace(
        s,
        r"\(" => " ( ",
        r"\)" => " ) ",
        "{" => " { ",
        "}" => " } ",
        "->" => " -> ",
        "λ" => " λ ",
        "," => " , ",
    )
    # Remove all extraneous whitespace
    s = replace(s, r"\s+" => " ")
    # Split on spaces
    return split(strip(s))
end

function parse_expr_inner(tokens, defs, env)
    if length(tokens) == 0
        error("unexpected end of input")
    end
    token = tokens[1]
    if token == "("
        # Possible expression heads
        tokens = view(tokens, 2:length(tokens))
        token = tokens[1]
        if token == "lam" || token == "lambda" || token == "λ" || token == "fn"
            # parse (λx y z -> body) or (λx,y,z -> body) or (λ_ _ _ -> body) or (λ_ -> body)
            # or (λ -> body) for 0-argument lambda. A zero-argument lambda is actually just 
            # syntactic sugar for a one-argument lambda with a unit argument.
            tokens = view(tokens, 2:length(tokens))
            num_args = 0

            # Handle 0-argument lambda case
            if tokens[1] == "->"
                tokens = view(tokens, 2:length(tokens))
                # Add dummy unit variable to environment
                env = ["_", env...]
                body, tokens = parse_expr_inner(tokens, defs, env)
                tokens[1] != ")" && error("expected closing paren")
                return Abs(body, Symbol("_")), view(tokens, 2:length(tokens))
            end

            # Handle regular lambda cases
            while true
                name = tokens[1]
                @assert Base.isidentifier(name) "expected identifier for lambda argument, got $name"
                env = [name, env...]
                num_args += 1
                tokens = view(tokens, 2:length(tokens))
                if tokens[1] == "," # optional comma
                    tokens = view(tokens, 2:length(tokens))
                end
                if tokens[1] == "->" # end of arg list
                    tokens = view(tokens, 2:length(tokens))
                    break
                end
            end
            body, tokens = parse_expr_inner(tokens, defs, env)
            for i ∈ 1:num_args
                body = Abs(body, Symbol(env[i]))
            end
            tokens[1] != ")" && error("expected closing paren")
            return body, view(tokens, 2:length(tokens))
        elseif token == "if"
            # Parse an if
            tokens = view(tokens, 2:length(tokens))
            cond, tokens = parse_expr_inner(tokens, defs, env)
            then_expr, tokens = parse_expr_inner(tokens, defs, env)
            else_expr, tokens = parse_expr_inner(tokens, defs, env)
            tokens[1] != ")" && error("expected closing paren")
            # Parse as a CaseOf expression.
            # return If(cond, then_expr, else_expr), view(tokens,2:length(tokens))
            return CaseOf(cond, OrderedDict(:True => then_expr, :False => else_expr)), view(tokens, 2:length(tokens))
        elseif token == "ylamlam"
            # Parse a Y lam lam
            tokens = view(tokens, 2:length(tokens))
            body, tokens = parse_expr_inner(tokens, defs, env)
            tokens[1] != ")" && error("expected closing paren")
            return Ylamlam(body), view(tokens, 2:length(tokens))
        elseif token == "Y"
            # parse a Y
            tokens = view(tokens, 2:length(tokens))
            f, tokens = parse_expr_inner(tokens, defs, env)
            e = Y(f)
            if tokens[1] != ")"
                # parse (Y f x) into App(Y(f), x)
                x, tokens = parse_expr_inner(tokens, defs, env)
                e = App(e, x)
            end
            tokens[1] != ")" && error("expected closing paren")
            return e, view(tokens, 2:length(tokens))
        elseif token == "case" || token == "match"
            # case e1 of Cons => (λ_->(λ_->e2)) | Nil => e3
            tokens = view(tokens, 2:length(tokens))
            scrutinee, tokens = parse_expr_inner(tokens, defs, env)
            @assert tokens[1] == "of" || token == "match"
            tokens[1] == "of" && (tokens = view(tokens, 2:length(tokens)))
            cases = OrderedDict{Symbol, PExpr}()
            while tokens[1] != ")"
                constructor = Symbol(tokens[1])
                tokens = view(tokens, 2:length(tokens))
                # Allow for the syntax (Cons x xs => body) instead of (Cons => (λ x xs -> body))
                if tokens[1] == "=>"
                    body, tokens = parse_expr_inner(view(tokens, 2:length(tokens)), defs, env)
                else
                    # parse (Cons x xs => body)
                    arguments = []
                    new_env = env
                    while tokens[1] != "=>"
                        push!(arguments, Symbol(tokens[1]))
                        new_env = [tokens[1], new_env...]
                        tokens = view(tokens, 2:length(tokens))
                    end
                    tokens = view(tokens, 2:length(tokens))
                    body, tokens = parse_expr_inner(tokens, defs, new_env)
                    # Wrap body in Abs for each argument, in the proper order.
                    for arg in reverse(arguments)
                        body = Abs(body, arg)
                    end
                end
                @assert !haskey(cases, constructor) "duplicate constructor $constructor in case..of"
                cases[constructor] = body
                if tokens[1] == "|"
                    tokens = view(tokens, 2:length(tokens))
                end
            end
            return CaseOf(scrutinee, cases), view(tokens, 2:length(tokens))
        elseif token == "let"
            # Parse a let expression
            tokens = view(tokens, 2:length(tokens))
            @assert tokens[1] == "(" "Expected opening parenthesis after 'let'"
            tokens = view(tokens, 2:length(tokens))

            bindings = []
            while tokens[1] != ")"
                # Handle both formats:
                # 1. Flat list: var1 val1 var2 val2
                # 2. Nested pairs: (var1 val1) (var2 val2)
                if tokens[1] == "("
                    # Nested pair format
                    tokens = view(tokens, 2:length(tokens))  # Skip opening paren
                    var = tokens[1]
                    tokens = view(tokens, 2:length(tokens))
                    val, tokens = parse_expr_inner(tokens, defs, env)
                    @assert tokens[1] == ")" "Expected closing parenthesis in let binding"
                    tokens = view(tokens, 2:length(tokens))  # Skip closing paren
                else
                    # Flat list format
                    var = tokens[1]
                    tokens = view(tokens, 2:length(tokens))
                    val, tokens = parse_expr_inner(tokens, defs, env)
                end
                push!(bindings, (var, val))
                env = [var, env...]
            end
            tokens = view(tokens, 2:length(tokens))  # Skip closing paren of bindings list
            body, tokens = parse_expr_inner(tokens, defs, env)

            @assert tokens[1] == ")" "Expected closing parenthesis at end of let expression"

            # Desugar to nested lambdas and applications
            expr = body
            for (var, val) in reverse(bindings)
                expr = App(Abs(expr, Symbol(var)), val)
            end

            return expr, view(tokens, 2:length(tokens))
        elseif haskey(args_of_constructor, Symbol(token))
            # parse a sum product type constructor
            constructor = Symbol(token)
            type = type_of_constructor[constructor]
            args = args_of_constructor[constructor]
            tokens = view(tokens, 2:length(tokens))
            args = []
            while tokens[1] != ")"
                arg, tokens = parse_expr_inner(tokens, defs, env)
                push!(args, arg)
            end
            if length(args) != length(args_of_constructor[constructor])
                error("wrong number of arguments for constructor $constructor. Expected $(length(args_of_constructor[constructor])), got $(length(args)) at: $(detokenize(tokens))")
            end
            return Construct(constructor, args), view(tokens, 2:length(tokens))
        elseif has_prim(token) && !haskey(defs, Symbol(token))
            op_type = lookup_prim(token)
            arity = prim_arity(op_type)
            tokens = view(tokens, 2:length(tokens))
            op = op_type()
            args = PExpr[]
            for i ∈ 1:arity
                arg, tokens = parse_expr_inner(tokens, defs, env)
                push!(args, arg)
            end
            tokens[1] != ")" && error("expected closing paren")
            return PrimOp(op, args), view(tokens, 2:length(tokens))
        elseif token == "discrete"
            # Parse (discrete (e1 p1) (e2 p2) ...)
            tokens = view(tokens, 2:length(tokens))
            
            options = PExpr[]
            probabilities = Float64[]
            
            while tokens[1] != ")"
                @assert tokens[1] == "(" "Expected opening paren in discrete distribution pair"
                tokens = view(tokens, 2:length(tokens))
                
                # Parse the expression
                expr, tokens = parse_expr_inner(tokens, defs, env)
                push!(options, expr)
                
                # Parse the probability (must be a literal number)
                prob_str = tokens[1]
                @assert all(c -> isdigit(c) || c == '.', prob_str) "Probability must be a literal number in discrete distribution"
                prob = parse(Float64, prob_str)
                push!(probabilities, prob)
                
                tokens = view(tokens, 2:length(tokens))  # Skip probability and closing paren
                @assert tokens[1] == ")" "Expected closing paren in discrete distribution pair"
                tokens = view(tokens, 2:length(tokens))
            end
            
            # Generate the nested if-expression using the discrete function
            expr_str = discrete(options, probabilities)
            expr, rest = parse_expr_inner(tokenize(expr_str), defs, env)
            @assert isempty(rest)
            
            return expr, view(tokens, 2:length(tokens))
        elseif token == "uniform"
            # Parse (uniform e1 e2 e3 ...)
            tokens = view(tokens, 2:length(tokens))
            options = PExpr[]
            while tokens[1] != ")"
                expr, tokens = parse_expr_inner(tokens, defs, env)
                push!(options, expr)
            end
            
            n = length(options)
            probabilities = fill(1.0/n, n)
            
            # Generate the nested if-expression using the discrete function
            expr_str = discrete(options, probabilities)
            expr, rest = parse_expr_inner(tokenize(expr_str), defs, env)
            @assert isempty(rest)
            
            return expr, view(tokens, 2:length(tokens))
        else
            # Parse an application
            f, tokens = parse_expr_inner(tokens, defs, env)
            args = []
            while tokens[1] != ")"
                arg, tokens = parse_expr_inner(tokens, defs, env)
                push!(args, arg)
            end

            # If no arguments provided, insert Unit constructor
            if isempty(args)
                args = [Construct(:Unit, PExpr[])]
            end

            expr = f
            for arg in args
                expr = App(expr, arg)
            end
            return expr, view(tokens, 2:length(tokens))
        end
    elseif token == "??"
        return NULL, view(tokens, 2:length(tokens))
    elseif token[1] == '?'
        name = Symbol(token[2:end])
        return AuxCFGSymbol(name), view(tokens, 2:length(tokens))
    elseif token[1] == '&'
        val = parse(Int, token[2:end])
        return RawInt(val), view(tokens, 2:length(tokens))
    elseif token[1] == '~'
        type = parse_type(token[2:end])
        return RandomnessCFGSymbol(type), view(tokens, 2:length(tokens))
    elseif token ∈ env
        # Parse a var by name like "foo"
        idx = findfirst(x -> x == token, env) # shadowing
        return Var(idx, Symbol(token)), view(tokens, 2:length(tokens))
    elseif token[1] == '#'
        # parse debruijn index
        idx = parse(Int, token[2:end])
        @assert idx > 0 "need one-index debruijn"
        return Var(idx), view(tokens, 2:length(tokens))
    elseif '#' ∈ token
        # variable combining name and debruijn like x#4
        parts = split(token, "#")
        name = Symbol(parts[1])
        idx = parse(Int, parts[2])
        @assert parts[1] == env[idx] "debruijn index must match variable name"
        return Var(idx, name), view(tokens, 2:length(tokens))
    elseif '@' ∈ token
        idx = parse(Int, token[2:end])
        return DiffVar(idx), view(tokens, 2:length(tokens))
    elseif all(isdigit, token)
        val = parse(Int, token)
        return const_to_expr(val), view(tokens, 2:length(tokens))
    elseif all(c -> isdigit(c) || c == '.', token)
        val = parse(Float64, token)
        return const_to_expr(val), view(tokens, 2:length(tokens))
    elseif token == "true" || token == "false"
        val = parse(Bool, token)
        return const_to_expr(val), view(tokens, 2:length(tokens))
        # Look up in defs
    elseif haskey(defs, Symbol(token))
        # return defs[Symbol(token)], view(tokens,2:length(tokens))
        # TODO: do gensyms need to be regenerated?
        return Defined(Symbol(token)), view(tokens, 2:length(tokens))
    else
        context = detokenize(tokens)
        context = context[1:min(length(context), 30)]
        error("unknown token: $token at \"$context\"")
    end
end
