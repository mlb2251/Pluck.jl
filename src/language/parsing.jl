export parse_expr, @expr_str, enable_location_tracking!, disable_location_tracking!, location_tracking_enabled, expr_location, expr_span

"""
expr"..." is equivalent to parse_expr("...")
No string interpolation is done - this simplifies \$var parsing to not require escaping.
If you need string interpolation, just do parse_expr() directly.
"""
macro expr_str(str)
    # interpolated_str = Meta.parse("\"$str\"")
    :(parse_expr($(esc(str))))
end

# ---------------------
# Optional span tracking
# ---------------------
const _TRACK_LOCATIONS = Ref(false)
const _TOKEN_LOCATIONS = IdDict{Any, Vector{Tuple{Int, Int}}}() # token collection -> [(line, col)]
const _PEXPR_LOCATIONS = IdDict{PExpr, Tuple{String, Int, Int}}() # expr -> (file, line, col)
const _PEXPR_SPANS = IdDict{PExpr, Tuple{String, Int, Int, Int, Int}}() # expr -> (file, start_line, start_col, end_line, end_col)
const _CURRENT_SOURCE_NAME = Ref("<string>")

enable_location_tracking!() = (_TRACK_LOCATIONS[] = true)
disable_location_tracking!() = (_TRACK_LOCATIONS[] = false)
location_tracking_enabled() = _TRACK_LOCATIONS[]

expr_location(e::PExpr) = get(_PEXPR_LOCATIONS, e, nothing)
expr_span(e::PExpr) = get(_PEXPR_SPANS, e, nothing)

function _record_token_locs!(tokens, locs)
    location_tracking_enabled() || return
    _TOKEN_LOCATIONS[tokens] = locs
end

function _token_loc(tokens, idx)
    location_tracking_enabled() || return nothing
    locs = get(_TOKEN_LOCATIONS, tokens, nothing)
    if locs !== nothing
        return locs[idx]
    end
    # If this is a view, map back to parent locations.
    try
        parent_tokens = parent(tokens)
        locs_parent = get(_TOKEN_LOCATIONS, parent_tokens, nothing)
        locs_parent === nothing && return nothing
        parent_range = parentindices(tokens)[1]
        parent_idx = parent_range[idx]
        return locs_parent[parent_idx]
    catch
        return nothing
    end
end

function _record_expr_loc!(expr::PExpr, tokens, idx)
    location_tracking_enabled() || return
    loc = _token_loc(tokens, idx)
    loc === nothing && return
    _PEXPR_LOCATIONS[expr] = (_CURRENT_SOURCE_NAME[], loc[1], loc[2])
end

function _record_expr_span!(expr::PExpr, tokens, consumed)
    location_tracking_enabled() || return
    consumed < 1 && return
    start_loc = _token_loc(tokens, 1)
    start_loc === nothing && return
    end_loc = _token_loc(tokens, consumed)
    end_loc === nothing && return
    tok_str = tokens[consumed]
    end_col = end_loc[2] + length(tok_str) - 1
    _PEXPR_SPANS[expr] = (_CURRENT_SOURCE_NAME[], start_loc[1], start_loc[2], end_loc[1], end_col)
end

"""
Tokenize while also recording start line/column (1-based) for each token.
Only used when location tracking is enabled to avoid overhead otherwise.
"""
function tokenize_with_locs(s::String)
    tokens = String[]
    locs = Tuple{Int, Int}[]

    # First remove line comments (but keep line structure)
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

    i = firstindex(s)
    line = 1
    col = 1
    while i <= lastindex(s)
        c = s[i]
        if isspace(c)
            if c == '\n'
                line += 1
                col = 1
            else
                col += 1
            end
            i = nextind(s, i)
            continue
        elseif c == '"'
            start_i = i
            start_col = col
            i = nextind(s, i)
            col += 1
            while i <= lastindex(s) && s[i] != '"'
                if s[i] == '\n'
                    line += 1
                    col = 1
                else
                    col += 1
                end
                i = nextind(s, i)
            end
            i <= lastindex(s) || error("unterminated string literal")
            token = s[start_i:i]
            push!(tokens, token)
            push!(locs, (line, start_col))
            i = nextind(s, i)
            col += 1
            continue
        elseif c == '-' && i < lastindex(s) && s[nextind(s, i)] == '>'
            push!(tokens, "->")
            push!(locs, (line, col))
            i = nextind(s, nextind(s, i))
            col += 2
            continue
        elseif c in ('(', ')', '{', '}', '[', ']', ',', '~', '`')
            push!(tokens, string(c))
            push!(locs, (line, col))
            i = nextind(s, i)
            col += 1
            continue
        else
            start = i
            start_col = col
            while i <= lastindex(s)
                c = s[i]
                if isspace(c) || c in ('(', ')', '{', '}', '[', ']', ',', '~', '`', '"')
                    break
                elseif c == '-' && i < lastindex(s) && s[nextind(s, i)] == '>'
                    break
                end
                i = nextind(s, i)
                col += 1
            end
            push!(tokens, s[start:prevind(s, i)])
            push!(locs, (line, start_col))
        end
    end
    return tokens, locs
end

function parse_expr(s::String; defs=DEFINITIONS, env=[], source_name="<string>", track_locations=location_tracking_enabled())
    old_track = location_tracking_enabled()
    old_source = _CURRENT_SOURCE_NAME[]
    _TRACK_LOCATIONS[] = track_locations
    _CURRENT_SOURCE_NAME[] = source_name
    tokens = if track_locations
        ts, locs = tokenize_with_locs(s)
        _record_token_locs!(ts, locs)
        ts
    else
        tokenize(s)
    end
    expr, rest = parse_expr_inner(tokens, defs, env)
    @assert isempty(rest)
    _TRACK_LOCATIONS[] = old_track
    _CURRENT_SOURCE_NAME[] = old_source
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
        elseif c in ('(', ')', '{', '}', '[', ']', ',', '~', '`')
            push!(tokens, string(c))
            i = nextind(s, i)
            continue
        else
            start = i
            while i <= lastindex(s)
                c = s[i]
                if isspace(c) || c in ('(', ')', '{', '}', '[', ']', ',', '~', '`', '"')
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

function parse_expr_inner(tokens, defs, env)
    start_tokens = tokens
    record_and_return(expr, rest) = begin
        _record_expr_loc!(expr, start_tokens, 1)
        consumed = length(start_tokens) - length(rest)
        _record_expr_span!(expr, start_tokens, consumed)
        return expr, rest
    end
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
                return record_and_return(Abs(Symbol("_"))(body), view(tokens, 2:length(tokens)))
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
                body = Abs(Symbol(env[i]))(body)
            end
            tokens[1] != ")" && error("expected closing paren")
            return record_and_return(body, view(tokens, 2:length(tokens)))
        elseif token == "if"
            # Parse an if
            tokens = view(tokens, 2:length(tokens))
            cond, tokens = parse_expr_inner(tokens, defs, env)
            then_expr, tokens = parse_expr_inner(tokens, defs, env)
            else_expr, tokens = parse_expr_inner(tokens, defs, env)
            tokens[1] != ")" && error("expected closing paren")
            # Parse as a CaseOf expression.
            # return If(cond, then_expr, else_expr), view(tokens,2:length(tokens))
            return record_and_return(CaseOf(CaseOfGuard[CaseOfGuard(:True, Symbol[]), CaseOfGuard(:False, Symbol[])])(cond, then_expr, else_expr), view(tokens, 2:length(tokens)))
        elseif token == "Y"
            # parse a Y
            tokens = view(tokens, 2:length(tokens))
            f, tokens = parse_expr_inner(tokens, defs, env)
            e = Y()(f)
            if tokens[1] != ")"
                # parse (Y f x) into App(Y(f), x)
                x, tokens = parse_expr_inner(tokens, defs, env)
                e = App()(e, x)
            end
            tokens[1] != ")" && error("expected closing paren")
            return record_and_return(e, view(tokens, 2:length(tokens)))
        elseif token == "case" || token == "match"
            # case e1 of Cons => (λ_->(λ_->e2)) | Nil => e3
            tokens = view(tokens, 2:length(tokens))
            scrutinee, tokens = parse_expr_inner(tokens, defs, env)
            @assert tokens[1] == "of" || token == "match"
            tokens[1] == "of" && (tokens = view(tokens, 2:length(tokens)))
            guards = CaseOfGuard[]
            branches = PExpr[]
            while tokens[1] != ")"
                @assert tokens[1] != "(" "unnecessary parens around pattern match guard at $(detokenize(tokens))" # common mistake
                constructor = Symbol(tokens[1])
                tokens = view(tokens, 2:length(tokens))
                args = Symbol[]
                # Else branch of this allows for the syntax (Cons x xs => body) instead of (Cons => (λ x xs -> body))
                if tokens[1] == "=>"
                    body, tokens = parse_expr_inner(view(tokens, 2:length(tokens)), defs, env)
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
                    body, tokens = parse_expr_inner(tokens, defs, new_env)
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
            return record_and_return(CaseOf(guards)(scrutinee, branches...), view(tokens, 2:length(tokens)))
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
                expr = App()(Abs(Symbol(var))(expr), val)
            end

            return record_and_return(expr, view(tokens, 2:length(tokens)))
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
            return record_and_return(Construct(constructor)(args...), view(tokens, 2:length(tokens)))
        elseif has_prim(token) && !haskey(defs, Symbol(token))
            head_type = lookup_prim(token)
            arity = prim_arity(head_type)
            tokens = view(tokens, 2:length(tokens))
            head = head_type()
            args = PExpr[]
            for i ∈ 1:arity
                arg, tokens = parse_expr_inner(tokens, defs, env)
                push!(args, arg)
            end
            tokens[1] != ")" && error("too few arguments for primitive $token, expected $arity, got $(length(args)) at: $(detokenize(tokens))")
            return record_and_return(head(args...), view(tokens, 2:length(tokens)))
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
                @assert all(c -> isdigit(c) || c == '.' || c =='e' || c == '-', prob_str) "Probability must be a literal number in discrete distribution, got $prob_str"
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
            
            return record_and_return(expr, view(tokens, 2:length(tokens)))
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
            
            return record_and_return(expr, view(tokens, 2:length(tokens)))
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
                args = [Construct(:Unit)()]
            end

            expr = f
            for arg in args
                expr = App()(expr, arg)
            end
            return record_and_return(expr, view(tokens, 2:length(tokens)))
        end
    elseif token[1] == '\''
        # parse a symbol
        sym = Symbol(token[2:end])
        return record_and_return(ConstNative(sym)(), view(tokens, 2:length(tokens)))
    elseif startswith(token, "0c") && length(token) == 3
        # byte literal: 0cX for a single ASCII byte X
        inner = token[3]
        @assert ncodeunits(string(inner)) == 1 "byte literal must be exactly one byte, got \"$inner\""
        byte = Int(codeunit(string(inner), 1))
        bitwidth = ConstNative(8)()
        val = ConstNative(byte)()
        return record_and_return(MkIntOp()(bitwidth, val), view(tokens, 2:length(tokens)))
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
        return record_and_return(expr, view(tokens, 2:length(tokens)))
    elseif token == "["
        # parse a list: parse expressions until ]
        tokens = view(tokens, 2:length(tokens))
        vals = []
        while tokens[1] != "]"
            head, tokens = parse_expr_inner(tokens, defs, env)
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
        return record_and_return(expr, tokens)
    elseif token[1] == '?'
        name = Symbol(token[2:end])
        return record_and_return(GSymbol(name)(), view(tokens, 2:length(tokens)))
    elseif token[1] == '#'
        # parse CFG symbol variable like "#int"
        type = Symbol(token[2:end])
        return record_and_return(GVarSymbol(type)(), view(tokens, 2:length(tokens)))
    elseif token[1] == '@'
        idx = parse(Int, token[2:end])
        return record_and_return(ConstNative(idx)(), view(tokens, 2:length(tokens)))
    elseif all(isdigit, token)
        val = parse(Int, token)
        return record_and_return(const_to_expr(val), view(tokens, 2:length(tokens)))
    elseif all(c -> isdigit(c) || c == '.', token)
        val = parse(Float64, token)
        res = const_to_expr(val)
        return record_and_return(res, view(tokens, 2:length(tokens)))
    elseif token == "true" || token == "false"
        val = parse(Bool, token)
        return record_and_return(const_to_expr(val), view(tokens, 2:length(tokens)))
    elseif token == "nothing"
        return record_and_return(Construct(:Unit)(), view(tokens, 2:length(tokens)))
    elseif token ∈ env || token[1] == '$' # leading with a $ forces variable parsing even if it isn't statically present in the environment
        # Parse a var by name like "foo"
        if token[1] == '$'
            @assert length(token) > 1 "expected variable name after \$ around $(detokenize(tokens))"
            token = token[2:end]
        end
        return record_and_return(Var(Symbol(token))(), view(tokens, 2:length(tokens)))
    elseif haskey(defs, Symbol(token))
        return record_and_return(Defined(Symbol(token))(), view(tokens, 2:length(tokens)))
    else
        context = detokenize(tokens)
        context = context[1:min(length(context), 30)]
        error("unknown token: $token at \"$context\" with env $env")
    end
end
