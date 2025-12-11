export parse_expr, @expr_str

"""
expr"..." is equivalent to parse_expr("...")
No string interpolation is done - this simplifies \$var parsing to not require escaping.
If you need string interpolation, just do parse_expr() directly.
"""
macro expr_str(str)
    # interpolated_str = Meta.parse("\"$str\"")
    :(parse_expr($(esc(str))))
end

mutable struct ParseState
    defs
    env_stack
    query
    base_dir
    ParseState(defs, env, base_dir=pwd()) = new(defs, [env], nothing, base_dir)
end

# Parse a single constructor definition of form (Constructor arg1 arg2 ...)
function parse_constructor(tokens)
    @assert tokens[1] == "(" "Expected opening paren in constructor definition at $(detokenize(tokens))"
    @assert tokens[end] == ")" "Expected closing paren in constructor definition"

    # Get constructor name and args (if any)
    constructor = Symbol(tokens[2])
    args = Symbol[Symbol(arg) for arg in tokens[3:end-1]]

    constructor => args
end


function parse_expr(s::String; defs=DEFINITIONS, env=[])
    tokens = tokenize(s)
    state = ParseState(defs, env)
    state.query = s
    expr, rest = parse_expr_inner(tokens, state)
    @assert isempty(rest)
    return expr
end

function const_to_expr(v::Int)
    parse_expr(pluck_nat(v))
end

const_to_expr(v::Float64) = ConstNative(v)()
const_to_expr(v::Bool) =
    v ? Construct(:True)() : Construct(:False)()


# Parse from Scheme notation (string) into PExpr
function tokenize(s)
    # First remove line comments
    lines = split(s, '\n')
    processed_lines = String[]
    for line in lines
        comment_start = findfirst(";;", line)
        if isnothing(comment_start)
            push!(processed_lines, line)
        else
            push!(processed_lines, line[1:comment_start.start-1])
        end
    end
    s = join(processed_lines, "\n")

    tokens = String[]
    i = firstindex(s)
    while i <= lastindex(s)
        c = s[i]
        if isspace(c)
            i = nextind(s, i)
            continue
        elseif c == '"'
            start = i
            i = nextind(s, i)
            while i <= lastindex(s) && s[i] != '"'
                i = nextind(s, i)
            end
            i <= lastindex(s) || error("unterminated string literal")
            token = s[start:i]
            push!(tokens, token)
            i = nextind(s, i)
            continue
        elseif c == '-' && i < lastindex(s) && s[nextind(s, i)] == '>'
            push!(tokens, "->")
            i = nextind(s, nextind(s, i))
            continue
        elseif c in ('(', ')', '{', '}', '[', ']', ',', '~', '`', 'λ')
            push!(tokens, string(c))
            i = nextind(s, i)
            continue
        else
            start = i
            while i <= lastindex(s)
                c = s[i]
                if isspace(c) || c in ('(', ')', '{', '}', '[', ']', ',', '~', '`', '"', 'λ')
                    break
                elseif c == '-' && i < lastindex(s) && s[nextind(s, i)] == '>'
                    break
                end
                i = nextind(s, i)
            end
            push!(tokens, s[start:prevind(s, i)])
        end
    end
    return tokens
end

function parse_with_env(tokens, state, env)
    pushfirst!(state.env_stack, env)
    expr, tokens = parse_expr_inner(tokens, state)
    popfirst!(state.env_stack)
    return expr, tokens
end

function parse_expr_inner(tokens, state)
    env = state.env_stack[1]
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
                body, tokens = parse_with_env(tokens, state, env)
                tokens[1] != ")" && error("expected closing paren")
                return Abs(Symbol("_"))(body), view(tokens, 2:length(tokens))
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
            body, tokens = parse_with_env(tokens, state, env)
            for i ∈ 1:num_args
                body = Abs(Symbol(env[i]))(body)
            end
            tokens[1] != ")" && error("expected closing paren")
            return body, view(tokens, 2:length(tokens))
        elseif token == "if"
            # Parse an if
            tokens = view(tokens, 2:length(tokens))
            cond, tokens = parse_expr_inner(tokens, state)
            then_expr, tokens = parse_expr_inner(tokens, state)
            else_expr, tokens = parse_expr_inner(tokens, state)
            tokens[1] != ")" && error("expected closing paren")
            # Parse as a CaseOf expression.
            # return If(cond, then_expr, else_expr), view(tokens,2:length(tokens))
            return CaseOf(CaseOfGuard[CaseOfGuard(:True, Symbol[]), CaseOfGuard(:False, Symbol[])])(cond, then_expr, else_expr), view(tokens, 2:length(tokens))
        elseif token == "Y"
            # parse a Y
            tokens = view(tokens, 2:length(tokens))
            f, tokens = parse_expr_inner(tokens, state)
            e = Y()(f)
            if tokens[1] != ")"
                # parse (Y f x) into App(Y(f), x)
                x, tokens = parse_expr_inner(tokens, state)
                e = App()(e, x)
            end
            tokens[1] != ")" && error("expected closing paren")
            return e, view(tokens, 2:length(tokens))
        elseif token == "case" || token == "match"
            # case e1 of Cons => (λ_->(λ_->e2)) | Nil => e3
            tokens = view(tokens, 2:length(tokens))
            scrutinee, tokens = parse_expr_inner(tokens, state)
            @assert tokens[1] == "of" || token == "match"
            tokens[1] == "of" && (tokens = view(tokens, 2:length(tokens)))
            guards = CaseOfGuard[]
            branches = PExpr[]
            while tokens[1] != ")"
                @assert tokens[1] != "(" "unnecessary parens around pattern match guard at $(detokenize(tokens))" # common mistake
                if tokens[1] == "|"
                    tokens = view(tokens, 2:length(tokens))
                end
                constructor = Symbol(tokens[1])
                tokens = view(tokens, 2:length(tokens))
                args = Symbol[]
                # Else branch of this allows for the syntax (Cons x xs => body) instead of (Cons => (λ x xs -> body))
                if tokens[1] == "=>"
                    body, tokens = parse_expr_inner(view(tokens, 2:length(tokens)), state)
                    while body isa PExpr{Abs}
                        push!(args, body.head.var)
                        body = body.args[1]
                    end
                else
                    # parse `Cons x xs => body`
                    new_env = env
                    while tokens[1] != "=>"
                        push!(args, Symbol(tokens[1]))
                        new_env = [tokens[1], new_env...]
                        tokens = view(tokens, 2:length(tokens))
                    end
                    tokens = view(tokens, 2:length(tokens))
                    body, tokens = parse_with_env(tokens, state, new_env)
                    # Wrap body in Abs for each argument, in the proper order.
                end
                @assert !any(g -> g.constructor == constructor, guards) "duplicate constructor $constructor in case..of"

                guard = CaseOfGuard(constructor, args)
                push!(guards, guard)
                push!(branches, body)
                if tokens[1] == "|"
                    tokens = view(tokens, 2:length(tokens))
                end
            end
            return CaseOf(guards)(scrutinee, branches...), view(tokens, 2:length(tokens))
        elseif token == "let"
            # Parse a let expression
            tokens = view(tokens, 2:length(tokens))
            @assert tokens[1] == "(" || tokens[1] == "[" "Expected opening parenthesis or open bracket after 'let' at $(detokenize(tokens))"
            close_token = tokens[1] == "(" ? ")" : "]"
            tokens = view(tokens, 2:length(tokens))

            bindings = []
            while tokens[1] != close_token
                # Handle both formats:
                # 1. Flat list: var1 val1 var2 val2
                # 2. Nested pairs: (var1 val1) (var2 val2)
                if tokens[1] == "("
                    # Nested pair format
                    tokens = view(tokens, 2:length(tokens))  # Skip opening paren
                    var = tokens[1]
                    tokens = view(tokens, 2:length(tokens))
                    val, tokens = parse_with_env(tokens, state, env)
                    @assert tokens[1] == ")" "Expected closing parenthesis in let binding"
                    tokens = view(tokens, 2:length(tokens))  # Skip closing paren
                else
                    # Flat list format
                    var = tokens[1]
                    tokens = view(tokens, 2:length(tokens))
                    val, tokens = parse_with_env(tokens, state, env)
                end
                push!(bindings, (var, val))
                env = [var, env...]
            end
            tokens = view(tokens, 2:length(tokens))  # Skip closing paren of bindings list
            body, tokens = parse_with_env(tokens, state, env)

            @assert tokens[1] == ")" "Expected closing parenthesis at end of let expression"

            # Desugar to nested lambdas and applications
            expr = body
            for (var, val) in reverse(bindings)
                expr = App()(Abs(Symbol(var))(expr), val)
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
                    arg, tokens = parse_expr_inner(tokens, state)
                push!(args, arg)
            end
            if length(args) != length(args_of_constructor[constructor])
                error("wrong number of arguments for constructor $constructor. Expected $(length(args_of_constructor[constructor])), got $(length(args)) at: $(detokenize(tokens))")
            end
            return Construct(constructor)(args...), view(tokens, 2:length(tokens))
        elseif token == "include"
            # Special parsing for include: (include "path/to/file.pluck")
            tokens = view(tokens, 2:length(tokens))
            
            path_token = tokens[1]
            @assert startswith(path_token, "\"") && endswith(path_token, "\"") "include expects a string literal path"
            rel_path = path_token[2:end-1]
            
            # Resolve relative paths using the base directory of the current file
            full_path = isabspath(rel_path) ? rel_path : joinpath(state.base_dir, rel_path)
            
            # Don't load at parse time - let it happen at eval time
            
            tokens = view(tokens, 2:length(tokens))
            @assert tokens[1] == ")" "Expected closing paren in include"
            
            # Return IncludeOp with path as ConstNative
            return IncludeOp()(ConstNative(full_path)()), view(tokens, 2:length(tokens))
        elseif token == "define-type"
            # Special parsing for define-type: (define-type name (Constructor1 args...) ...)
            tokens = view(tokens, 2:length(tokens))
            
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
            
            # Define the type immediately at parse time so constructors are available
            define_type!(type_name, constructors)
            
            @assert tokens[1] == ")" "Expected closing paren in define-type"
            
            # Return DefineTypeOp with type name and constructors as ConstNative
            return DefineTypeOp()(ConstNative(type_name)(), ConstNative(constructors)()), view(tokens, 2:length(tokens))
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

                @assert tokens[1] == ")" "Expected closing paren in define"

                # Return DefineOp with fname as ConstNative and lambda as expr
                return DefineOp()(ConstNative(fname)(), expr), view(tokens, 2:length(tokens))
            else
                # Value definition: (define x expr)
                name = Symbol(tokens[1])
                tokens = view(tokens, 2:length(tokens))

                # Set up dummy binding so the expression can reference the name recursively
                state.defs[name] = Definition(name, DUMMY_EXPRESSION)

                # Parse expression - just use current state which already has the right env_stack
                expr, tokens = parse_expr_inner(tokens, state)

                @assert tokens[1] == ")" "Expected closing paren in define"

                # Return DefineOp with name as ConstNative
                return DefineOp()(ConstNative(name)(), expr), view(tokens, 2:length(tokens))
            end
        elseif token == "query"
            tokens = view(tokens, 2:length(tokens))
            return parse_query_expr(tokens, state.defs, base_dir=state.base_dir)
        elseif has_prim(token) && !haskey(state.defs, Symbol(token))
            head_type = lookup_prim(token)
            arity = prim_arity(head_type)
            tokens = view(tokens, 2:length(tokens))
            head = head_type()
            args = PExpr[]
            for i ∈ 1:arity
                arg, tokens = parse_expr_inner(tokens, state)
                push!(args, arg)
            end
            tokens[1] != ")" && error("too few arguments for primitive $token, expected $arity, got $(length(args)) at: $(detokenize(tokens))")
            return head(args...), view(tokens, 2:length(tokens))
        elseif token == "discrete"
            # Parse (discrete (e1 p1) (e2 p2) ...)
            tokens = view(tokens, 2:length(tokens))
            
            options = PExpr[]
            probabilities = Float64[]
            
            while tokens[1] != ")"
                @assert tokens[1] == "(" "Expected opening paren in discrete distribution pair"
                tokens = view(tokens, 2:length(tokens))
                
                # Parse the expression
                expr, tokens = parse_expr_inner(tokens, state)
                push!(options, expr)
                
                # Parse the probability (must be a literal number)
                prob_str = tokens[1]
                @assert all(c -> isdigit(c) || c == '.' || c =='e' || c == '-', prob_str) "Probability must be a literal number in discrete distribution, got $prob_str"
                prob = parse(Float64, prob_str)
                push!(probabilities, prob)
                
                tokens = view(tokens, 2:length(tokens))  # Skip probability and closing paren
                @assert tokens[1] == ")" "Expected closing paren in discrete distribution pair"
                tokens = view(tokens, 2:length(tokens))
            end
            
            # Generate the nested if-expression using the discrete function
            expr_str = discrete(options, probabilities)
            expr, rest = parse_expr_inner(tokenize(expr_str), state)
            @assert isempty(rest)
            
            return expr, view(tokens, 2:length(tokens))
        elseif token == "uniform"
            # Parse (uniform e1 e2 e3 ...)
            tokens = view(tokens, 2:length(tokens))
            options = PExpr[]
            while tokens[1] != ")"
                expr, tokens = parse_expr_inner(tokens, state)
                push!(options, expr)
            end
            
            n = length(options)
            probabilities = fill(1.0/n, n)
            
            # Generate the nested if-expression using the discrete function
            expr_str = discrete(options, probabilities)
            expr, rest = parse_expr_inner(tokenize(expr_str), state)
            @assert isempty(rest)
            
            return expr, view(tokens, 2:length(tokens))
        else
            # Parse an application
            f, tokens = parse_expr_inner(tokens, state)
            args = []
            while tokens[1] != ")"
                arg, tokens = parse_expr_inner(tokens, state)
                push!(args, arg)
            end

            # If no arguments provided, insert Unit constructor
            if isempty(args)
                args = [Construct(:Unit)()]
            end

            expr = f
            for arg in args
                expr = App()(expr, arg)
            end
            return expr, view(tokens, 2:length(tokens))
        end
    elseif token[1] == '\''
        # parse a symbol
        sym = Symbol(token[2:end])
        return ConstNative(sym)(), view(tokens, 2:length(tokens))
    elseif startswith(token, "0c") && length(token) == 3
        # byte literal: 0cX for a single ASCII byte X
        inner = token[3]
        @assert ncodeunits(string(inner)) == 1 "byte literal must be exactly one byte, got \"$inner\""
        byte = Int(codeunit(string(inner), 1))
        bitwidth = ConstNative(8)()
        val = ConstNative(byte)()
        return MkIntOp()(bitwidth, val), view(tokens, 2:length(tokens))
    elseif startswith(token, "\"") && endswith(token, "\"")
        # string literal -> list of 8-bit ints
        # Use proper character indexing for UTF-8 safety
        start_idx = nextind(token, firstindex(token))
        end_idx = prevind(token, lastindex(token))
        inner = token[start_idx:end_idx]
        bytes = collect(codeunits(inner))
        expr = Construct(:Nil)()
        for b in reverse(bytes)
            bitwidth = ConstNative(8)()
            val = ConstNative(Int(b))()
            expr = Construct(:Cons)(MkIntOp()(bitwidth, val), expr)
        end
        return expr, view(tokens, 2:length(tokens))
    elseif token == "["
        # parse a list: parse expressions until ]
        tokens = view(tokens, 2:length(tokens))
        vals = []
        while tokens[1] != "]"
            head, tokens = parse_expr_inner(tokens, state)
            # @assert tokens[1] == "," || tokens[1] == "]" "expected comma or closing bracket in list at $(detokenize(tokens))"
            if tokens[1] == ","
                tokens = view(tokens, 2:length(tokens))
            end
            push!(vals, head)
        end
        tokens = view(tokens, 2:length(tokens))
        expr = Construct(:Nil)()
        for val in reverse(vals)
            expr = Construct(:Cons)(val, expr)
        end
        return expr, tokens
    elseif token[1] == '?'
        name = Symbol(token[2:end])
        return GSymbol(name)(), view(tokens, 2:length(tokens))
    elseif token[1] == '#'
        # parse CFG symbol variable like "#int"
        type = Symbol(token[2:end])
        return GVarSymbol(type)(), view(tokens, 2:length(tokens))
    elseif token[1] == '@'
        idx = parse(Int, token[2:end])
        return ConstNative(idx)(), view(tokens, 2:length(tokens))
    elseif all(isdigit, token)
        val = parse(Int, token)
        return const_to_expr(val), view(tokens, 2:length(tokens))
    elseif all(c -> isdigit(c) || c == '.', token)
        val = parse(Float64, token)
        res = const_to_expr(val)
        return res, view(tokens, 2:length(tokens))
    elseif token == "true" || token == "false"
        val = parse(Bool, token)
        return const_to_expr(val), view(tokens, 2:length(tokens))
    elseif token == "nothing"
        return Construct(:Unit)(), view(tokens, 2:length(tokens))
    elseif token ∈ env || token[1] == '$' # leading with a $ forces variable parsing even if it isn't statically present in the environment
        # Parse a var by name like "foo"
        if token[1] == '$'
            @assert length(token) > 1 "expected variable name after \$ around $(detokenize(tokens))"
            token = token[2:end]
        end
        return Var(Symbol(token))(), view(tokens, 2:length(tokens))
    elseif haskey(state.defs, Symbol(token))
        return Defined(Symbol(token))(), view(tokens, 2:length(tokens))
    else
        parse_error(state, "unknown token: $token", tokens)
    end
end


function parse_error(state, msg, tokens)
    context = detokenize(tokens)
    context = context[1:min(length(context), 50)]
    printstyled("Pluck Parse Error: ", color=:red)
    println(msg)
    println("Context: $context")
    println("Env: ", state.env_stack[1])
    println("Query: ", state.query)
    throw(ErrorException("Pluck Parse Error"))
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
            result_str *= token
            if i < length(tokens) && tokens[i+1] != ")"
                result_str *= " "
            end
        end
    end
    return result_str
end

function parse_query_expr(tokens, defs; silent=false, base_dir=pwd())
    # @assert tokens[1] == "(" "Expected opening paren at start of query"
    # tokens = view(tokens, 2:length(tokens))
    end_idx = find_ending_paren(tokens)
    # Skip past "query"
    # @assert tokens[1] == "query" "Expected query keyword"
    query_tokens = view(tokens, 1:end_idx)

    if findfirst(t -> t == "(", query_tokens) == 1
        # Name is the entire expression
        name_expr = parse_expr("\"$(replace(detokenize(query_tokens), "\"" => "\""))\"")
    else
        # Name followed by expression
        name = String(query_tokens[1])[2:end]
        name_expr = parse_expr("\"$name\"")
        query_tokens = view(query_tokens, 2:length(query_tokens))
    end

    query_body, rest_query_tokens = parse_expr_inner(query_tokens, ParseState(defs, [], base_dir))
    @assert length(rest_query_tokens) == 1 && query_tokens[end] == ")" "Expected closing paren and nothing else, got $(detokenize(rest_query_tokens))"

    query_expr = QueryOp()(name_expr, query_body)

    return query_expr, view(tokens, end_idx+1:length(tokens))
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