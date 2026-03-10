export parse_expr

"""
Token with source position information for better error messages.
"""
struct Token
    value::String
    line::Int      # 1-indexed line number
    col::Int       # 1-indexed column number (character position in line)
    offset::Int    # 0-indexed byte offset in source
end

# Make Token comparable with String for backward compatibility
Base.:(==)(t::Token, s::String) = t.value == s
Base.:(==)(s::String, t::Token) = s == t.value
Base.:(==)(t1::Token, t2::Token) = t1.value == t2.value
Base.getindex(t::Token, i) = t.value[i]
Base.firstindex(t::Token) = firstindex(t.value)
Base.lastindex(t::Token) = lastindex(t.value)
Base.startswith(t::Token, s::String) = startswith(t.value, s)
Base.endswith(t::Token, s::String) = endswith(t.value, s)
Base.String(t::Token) = t.value
Base.Symbol(t::Token) = Symbol(t.value)
Base.show(io::IO, t::Token) = print(io, t.value)
Base.length(t::Token) = length(t.value)
Base.all(pred, t::Token) = all(pred, t.value)
Base.parse(::Type{T}, t::Token) where T = parse(T, t.value)
Base.in(t::Token, collection) = t.value in collection
Base.isdigit(t::Token) = all(isdigit, t.value)
Base.isidentifier(t::Token) = Base.isidentifier(t.value)
Base.nextind(t::Token, i::Int) = nextind(t.value, i)
Base.prevind(t::Token, i::Int) = prevind(t.value, i)

mutable struct ParseState
    defs
    env_stack
    query
    base_dir
    source::String      # Original source code
    filename::String    # Source filename for error messages
    ParseState(defs, env, base_dir=pwd(), source="", filename="<unknown>") =
        new(defs, [env], nothing, base_dir, source, filename)
end

# Parse a single constructor definition of form (Constructor arg1 arg2 ...)
function parse_constructor(tokens, state)
    tokens[1] == "(" || parse_error(state, tokens, "expected opening paren in constructor definition")
    tokens[end] == ")" || parse_error(state, view(tokens, length(tokens):length(tokens)), "expected closing paren in constructor definition")

    # Get constructor name and args (if any)
    constructor = Symbol(tokens[2])
    args = Symbol[Symbol(arg) for arg in tokens[3:end-1]]

    constructor => args
end


function parse_expr(s::String; defs=DEFINITIONS, env=[], filename="<unknown>")
    tokens = tokenize(s)
    state = ParseState(defs, env, pwd(), s, filename)
    expr, rest = parse_expr_inner(tokens, state)
    isempty(rest) || parse_error(state, rest, "unexpected tokens after end of expression")
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
    # First remove line comments, but keep track of line positions
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

    tokens = Token[]
    i = firstindex(s)
    line = 1
    col = 1

    while i <= lastindex(s)
        c = s[i]
        if c == '\n'
            # Track newlines
            line += 1
            col = 1
            i = nextind(s, i)
            continue
        elseif isspace(c)
            # Track column position through whitespace
            col += 1
            i = nextind(s, i)
            continue
        end

        # Record token start position
        token_line = line
        token_col = col
        token_offset = i - 1  # 0-indexed byte offset

        if c == '"'
            # String literal
            start = i
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
            token_value = s[start:i]
            push!(tokens, Token(token_value, token_line, token_col, token_offset))
            col += 1
            i = nextind(s, i)
            continue
        elseif c == '-' && i < lastindex(s) && s[nextind(s, i)] == '>'
            # Arrow token
            push!(tokens, Token("->", token_line, token_col, token_offset))
            col += 2
            i = nextind(s, nextind(s, i))
            continue
        elseif c in ('(', ')', '{', '}', '[', ']', ',', '~', '`', 'λ')
            # Single character token
            push!(tokens, Token(string(c), token_line, token_col, token_offset))
            col += 1
            i = nextind(s, i)
            continue
        else
            # Identifier or number
            start = i
            start_col = col
            while i <= lastindex(s)
                c = s[i]
                if isspace(c) || c in ('(', ')', '{', '}', '[', ']', ',', '~', '`', '"', 'λ')
                    break
                elseif c == '-' && i < lastindex(s) && s[nextind(s, i)] == '>'
                    break
                end
                col += 1
                i = nextind(s, i)
            end
            token_value = s[start:prevind(s, i)]
            push!(tokens, Token(token_value, token_line, token_col, token_offset))
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
        parse_error(state, tokens, "unexpected end of input")
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
                tokens[1] == ")" || parse_error(state, tokens, "expected closing paren after lambda body")
                return Abs(Symbol("_"))(body), view(tokens, 2:length(tokens))
            end

            # Handle regular lambda cases
            while true
                name = tokens[1]
                Base.isidentifier(name) || parse_error(state, tokens, "expected identifier for lambda argument, got $name")
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
            tokens[1] == ")" || parse_error(state, tokens, "expected closing paren after lambda body")
            return body, view(tokens, 2:length(tokens))
        elseif token == "if"
            # Parse an if
            tokens = view(tokens, 2:length(tokens))
            cond, tokens = parse_expr_inner(tokens, state)
            then_expr, tokens = parse_expr_inner(tokens, state)
            else_expr, tokens = parse_expr_inner(tokens, state)
            tokens[1] == ")" || parse_error(state, tokens, "expected closing paren after if expression")
            # Parse as a CaseOf expression.
            # return If(cond, then_expr, else_expr), view(tokens,2:length(tokens))
            return CaseOf(CaseOfGuard[CaseOfGuard(:True, Symbol[]), CaseOfGuard(:False, Symbol[])])(cond, then_expr, else_expr), view(tokens, 2:length(tokens))
        elseif token == "case" || token == "match"
            # case e1 of Cons => (λ_->(λ_->e2)) | Nil => e3
            tokens = view(tokens, 2:length(tokens))
            scrutinee, tokens = parse_expr_inner(tokens, state)
            (tokens[1] == "of" || token == "match") || parse_error(state, tokens, "expected 'of' after match scrutinee")
            tokens[1] == "of" && (tokens = view(tokens, 2:length(tokens)))
            guards = CaseOfGuard[]
            branches = PExpr[]
            while tokens[1] != ")"
                tokens[1] != "(" || parse_error(state, tokens, "unnecessary parens around pattern match guard") # common mistake
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
                any(g -> g.constructor == constructor, guards) && parse_error(state, tokens, "duplicate constructor $constructor in match expression")

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
            (tokens[1] == "(" || tokens[1] == "[") || parse_error(state, tokens, "expected opening parenthesis or bracket after 'let'")
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
                    tokens[1] == ")" || parse_error(state, tokens, "expected closing parenthesis in let binding")
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

            tokens[1] == ")" || parse_error(state, tokens, "expected closing parenthesis at end of let expression")

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
            length(args) == length(args_of_constructor[constructor]) || parse_error(state, tokens, "wrong number of arguments for constructor $constructor: expected $(length(args_of_constructor[constructor])), got $(length(args))")
            return Construct(constructor)(args...), view(tokens, 2:length(tokens))
        elseif has_prim(String(token)) && !haskey(state.defs, Symbol(token))
            head_type = lookup_prim(String(token))
            arity = prim_arity(head_type)
            tokens = view(tokens, 2:length(tokens))
            head = head_type()
            args = PExpr[]
            for i ∈ 1:arity
                arg, tokens = parse_expr_inner(tokens, state)
                push!(args, arg)
            end
            tokens[1] == ")" || parse_error(state, tokens, "wrong number of arguments for primitive $token: expected $arity, got $(length(args))")
            return head(args...), view(tokens, 2:length(tokens))
        elseif token == "discrete"
            # Parse (discrete (e1 p1) (e2 p2) ...)
            tokens = view(tokens, 2:length(tokens))

            options = PExpr[]
            probabilities = Float64[]

            while tokens[1] != ")"
                tokens[1] == "(" || parse_error(state, tokens, "expected opening paren in discrete distribution pair")
                tokens = view(tokens, 2:length(tokens))

                # Parse the expression
                expr, tokens = parse_expr_inner(tokens, state)
                push!(options, expr)

                # Parse the probability (must be a literal number)
                prob_str = tokens[1]
                all(c -> isdigit(c) || c == '.' || c =='e' || c == '-', prob_str) || parse_error(state, tokens, "probability must be a literal number in discrete distribution, got $prob_str")
                prob = parse(Float64, prob_str)
                push!(probabilities, prob)

                tokens = view(tokens, 2:length(tokens))  # Skip probability and closing paren
                tokens[1] == ")" || parse_error(state, tokens, "expected closing paren in discrete distribution pair")
                tokens = view(tokens, 2:length(tokens))
            end

            # Generate the nested if-expression using the discrete function
            expr_str = discrete(options, probabilities)
            expr, rest = parse_expr_inner(tokenize(expr_str), state)
            isempty(rest) || parse_error(state, rest, "unexpected tokens after discrete expression")

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
            isempty(rest) || parse_error(state, rest, "unexpected tokens after uniform expression")

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
        ncodeunits(string(inner)) == 1 || parse_error(state, tokens, "byte literal must be exactly one byte, got \"$inner\"")
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
    elseif haskey(state.defs, Symbol(token)) || token[1] == '?' && token[2] == '='
        return Defined(Symbol(token))(), view(tokens, 2:length(tokens))
    else
        parse_error(state, tokens, "unknown token: $token")
    end
end


"""
Format a Rust-style error message with source context.

Shows:
- Filename and line:column location
- 2 lines of context before and after the error
- Line numbers in gutter
- Visual highlight (^^^) under the error location
- Rust-style colors: red for errors, blue for line numbers
"""
function format_parse_error(state::ParseState, tokens, msg::String)
    # Handle empty tokens
    if isempty(tokens)
        io = IOBuffer()
        printstyled(io, "error", color=:red, bold=true)
        println(io, ": ", msg)
        printstyled(io, "  --> ", color=:blue)
        println(io, state.filename)
        return String(take!(io))
    end

    # Get the first token's position
    token = tokens[1]
    line = token.line
    col = token.col

    # Split source into lines
    source_lines = split(state.source, '\n')

    # Calculate range of lines to show (2 lines before/after)
    context_lines = 2
    start_line = max(1, line - context_lines)
    end_line = min(length(source_lines), line + context_lines)

    # Build error message
    io = IOBuffer()

    # Header: error: message
    printstyled(io, "error", color=:red, bold=true)
    println(io, ": ", msg)

    # Location: --> filename:line:col
    printstyled(io, "  --> ", color=:blue)
    println(io, state.filename, ":", line, ":", col)
    println(io)

    # Gutter width (for line numbers)
    gutter_width = length(string(end_line))

    # Print context lines
    for i in start_line:end_line
        # Line number gutter
        if i == line
            printstyled(io, lpad(i, gutter_width), " | ", color=:blue, bold=true)
        else
            printstyled(io, lpad(i, gutter_width), " | ", color=:blue)
        end

        # Source line
        println(io, source_lines[i])

        # Highlight line (^^^) for error line
        if i == line
            printstyled(io, repeat(" ", gutter_width), " | ", color=:blue, bold=true)
            # Calculate token length for highlighting
            token_len = length(token.value)
            # Adjust for multi-character start
            highlight_col = col - 1
            printstyled(io, repeat(" ", highlight_col), repeat("^", max(1, token_len)), "\n", color=:red, bold=true)
        end
    end

    return String(take!(io))
end

function parse_error(state, tokens, msg)
    format_parse_error_to_stderr(state, tokens, msg)
    throw(ErrorException("Pluck Parse Error"))
end

"""
Print a Rust-style error message directly to stderr with colors.
"""
function format_parse_error_to_stderr(state::ParseState, tokens, msg::String)
    # Handle empty tokens
    if isempty(tokens)
        printstyled(stderr, "error", color=:red, bold=true)
        println(stderr, ": ", msg)
        printstyled(stderr, "  --> ", color=:blue)
        println(stderr, state.filename)
        return
    end

    # Get the first token's position
    token = tokens[1]
    line = token.line
    col = token.col

    # Split source into lines
    source_lines = split(state.source, '\n')

    # Calculate range of lines to show (2 lines before/after)
    context_lines = 2
    start_line = max(1, line - context_lines)
    end_line = min(length(source_lines), line + context_lines)

    # Header: error: message
    printstyled(stderr, "error", color=:red, bold=true)
    println(stderr, ": ", msg)

    # Location: --> filename:line:col
    printstyled(stderr, "  --> ", color=:blue)
    println(stderr, state.filename, ":", line, ":", col)
    println(stderr)

    # Gutter width (for line numbers)
    gutter_width = length(string(end_line))

    # Print context lines
    for i in start_line:end_line
        # Line number gutter
        if i == line
            printstyled(stderr, lpad(i, gutter_width), " | ", color=:blue, bold=true)
        else
            printstyled(stderr, lpad(i, gutter_width), " | ", color=:blue)
        end

        # Source line
        println(stderr, source_lines[i])

        # Highlight line (^^^) for error line
        if i == line
            printstyled(stderr, repeat(" ", gutter_width), " | ", color=:blue, bold=true)
            # Calculate token length for highlighting
            token_len = length(token.value)
            # Adjust for multi-character start
            highlight_col = col - 1
            printstyled(stderr, repeat(" ", highlight_col), repeat("^", max(1, token_len)), "\n", color=:red, bold=true)
        end
    end
end


function detokenize(tokens)
    result_str = ""
    for (i, token) in enumerate(tokens)
        # Convert Token to String if needed
        token_str = String(token)
        if token_str == "(" || token_str == ")"
            result_str *= token_str
            if token_str == ")" && i < length(tokens) && String(tokens[i+1]) == "("
                result_str *= " "
            end
        else
            result_str *= token_str
            if i < length(tokens) && String(tokens[i+1]) != ")"
                result_str *= " "
            end
        end
    end
    return result_str
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

function find_ending_bracket(tokens)
    depth = 1
    end_idx = 1
    while depth > 0 && end_idx <= length(tokens)
        if tokens[end_idx] == "["
            depth += 1
        elseif tokens[end_idx] == "]"
            depth -= 1
        end
        end_idx += 1
    end
    return end_idx-1
end

# Reconstruct a value string from tokens to match string(v) output exactly.
# Rules: no space after ( or [, no space before ) or ] or comma, space after comma,
# space between other adjacent tokens.
function detokenize_value(tokens)
    result = ""
    for (i, token) in enumerate(tokens)
        token_str = String(token)
        result *= token_str
        if i < length(tokens)
            next_str = String(tokens[i+1])
            if token_str in ("(", "[") || next_str in (")", "]", ",")
                # no space
            elseif token_str == ","
                result *= " "
            else
                result *= " "
            end
        end
    end
    return result
end