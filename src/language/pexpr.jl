export Var,
    is_closed,
    App,
    Abs,
    Const,
    ConstReal,
    ConstBool,
    Ylamlam,
    If,
    Root,
    Defined,
    PrimOp,
    NULL,
    nulls,
    setchild!,
    getchild,
    tokenize,
    parse_expr_inner,
    parse_expr,
    parse_expr,
    stitch_str,
    get_func,
    strip_abs,
    num_abs,
    get_args,
    num_args,
    PExpr,
    has_null,
    null_paths,
    haschild,
    num_apps,
    getchildtype,
    randomness_terminal_paths,
    is_randomness_terminal,
    typeof_randomness_terminal,
    randomness_terminals_of_type,
    Y,
    RandomnessCFGSymbol,
    AuxCFGSymbol,
    RawInt,
    CFGSymbol,
    VarCFGSymbol,
    shortname,
    unifies,
    setchild_or_root,
    is_random
export CaseOf, Construct, RenderedHole, highlight_subexpression

abstract type PExpr end


mutable struct CaseOf <: PExpr
    scrutinee::PExpr
    cases::Dict{Symbol,PExpr}
    constructors::Vector{Symbol} # for deterministic enumeration of the cases
end

num_children(e::CaseOf) = 1 + length(e.cases)
setchild!(e::CaseOf, i::Int, child) =
    i == 1 ? (e.scrutinee = child) : (e.cases[e.constructors[i-1]] = child)
getchild(e::CaseOf, i::Int) = i == 1 ? e.scrutinee : e.cases[e.constructors[i-1]]
unifies(e1::CaseOf, e2::CaseOf) =
    unifies(e1.scrutinee, e2.scrutinee) &&
    e1.constructors == e2.constructors &&
    all(
        unifies(e1.cases[constructor], e2.cases[constructor]) for
        constructor in e1.constructors
    )


mutable struct Construct <: PExpr
    spt::SumProductType
    constructor::Symbol
    args::Vector{PExpr}
end

num_children(e::Construct) = length(e.args)
setchild!(e::Construct, i::Int, child) = (e.args[i] = child)
getchild(e::Construct, i::Int) = e.args[i]
unifies(e1::Construct, e2::Construct) =
    e1.spt.name === e2.spt.name &&
    e1.constructor === e2.constructor &&
    all([unifies(e1.args[i], e2.args[i]) for i ∈ 1:length(e1.args)])



function getchildtype(e, path::Vector{Int}, t, env)
    for i in path
        t = getchildtype(e, i, t, env)
        e = getchild(e, i)
    end
    t
end

function getchild(e, path::Vector{Int})
    for i in path
        e = getchild(e, i)
    end
    e
end

function haschild(e, path::Vector{Int})
    for i in path
        if num_children(e) < i
            return false
        end
        e = getchild(e, i)
    end
    return true
end

function haschild(e, i::Int)
    num_children(e) >= i
end

function setchild!(e, path::Vector{Int}, child)
    @assert !isempty(path)
    for i ∈ 1:length(path)-1
        e = getchild(e, path[i])
    end
    setchild!(e, path[end], child)
end

unifies(e1::PExpr, e2::PExpr) = false


abstract type CFGSymbol <: PExpr end

unifies(e1::CFGSymbol, e2::PExpr) = true
unifies(e1::PExpr, e2::CFGSymbol) = true


struct AuxCFGSymbol <: CFGSymbol
    name::Symbol
end

struct RawInt <: PExpr
    val::Int
end

struct RandomnessCFGSymbol <: CFGSymbol
    type::PType
end

struct VarCFGSymbol <: CFGSymbol
    type::PType
end

num_children(e::AuxCFGSymbol) = 0
num_children(e::RandomnessCFGSymbol) = 0
num_children(e::VarCFGSymbol) = 0
num_children(e::RawInt) = 0


const vars_names::Vector{Symbol} = [Symbol("#$i") for i ∈ 1:100]

# deBruijn indexing
struct Var <: PExpr
    idx::Int
    name::Symbol
end
Var(idx::Int) = Var(idx, :noname)
num_children(e::Var) = 0
unifies(e1::Var, e2::Var) = e1.idx == e2.idx

# function application
mutable struct App <: PExpr
    f::PExpr
    x::PExpr
end
unifies(e1::App, e2::App) = unifies(e1.f, e2.f) && unifies(e1.x, e2.x)




function getchild(e::App, i::Int)
    if i == 1
        get_func(e)
    else
        getarg(e, i - 1)
    end
end

function setchild!(e::App, i::Int, child)
    apps = num_apps(e)
    # i > apps + 1 && error("Trying to access child $i of an App that has $(args+1) children (including the function itself)")
    # silly temp hard coding
    @assert apps > 0
    if apps == 1
        if i == 1
            e.f = child
        elseif i == 2
            e.x = child
        else
            error("unreachable")
        end
    elseif apps == 2
        if i == 1
            e.f.f = child
        elseif i == 2
            e.f.x = child
        elseif i == 3
            e.x = child
        else
            error("unreachable")
        end
    elseif apps == 3
        if i == 1
            e.f.f.f = child
        elseif i == 2
            e.f.f.x = child
        elseif i == 3
            e.f.x = child
        elseif i == 4
            e.x = child
        else
            error("unreachable")
        end
    else
        error("too many apps")
    end
end

# setchild!(e::App, i::Int, child) = (if i == 1 e.f = child else e.args[i-1] = child end;)
# getchild(e::App, i::Int) = (if i == 1 e.f else e.args[i-1] end)

# function abstraction
mutable struct Abs <: PExpr
    body::PExpr
    name::Symbol
end
num_children(e::Abs) = 1
setchild!(e::Abs, i::Int, child) = (@assert i == 1; (e.body = child))
getchild(e::Abs, i::Int) = (@assert i == 1; e.body)
unifies(e1::Abs, e2::Abs) = unifies(e1.body, e2.body)

num_abs(e::Abs) = 1 + num_abs(e.body)
num_abs(e::PExpr) = 0

strip_abs(e::Abs) = strip_abs(e.body)
strip_abs(e::PExpr) = e



# Integer constants
struct Const <: PExpr
    val::Int
end
num_children(e::Const) = 0
unifies(e1::Const, e2::Const) = e1.val == e2.val

# Real constants
struct ConstReal <: PExpr
    val::Float64
end
num_children(e::ConstReal) = 0
unifies(e1::ConstReal, e2::ConstReal) = e1.val == e2.val

# Bool constants
struct ConstBool <: PExpr
    val::Bool
end
num_children(e::ConstBool) = 0
unifies(e1::ConstBool, e2::ConstBool) = e1.val == e2.val

mutable struct Y <: PExpr
    f::PExpr
    t0::Union{PType,Nothing}
    t1::Union{PType,Nothing}
end
Y(f) = Y(f, nothing, nothing)


num_children(e::Y) = 1
setchild!(e::Y, i::Int, child) = (@assert i == 1 && (e.f = child))
getchild(e::Y, i::Int) = (@assert i == 1 && return e.f)
unifies(e1::Y, e2::Y) = unifies(e1.f, e2.f) && e1.t0 == e2.t0 && e1.t1 == e2.t1



mutable struct Ylamlam <: PExpr
    body::PExpr
end
num_children(e::Ylamlam) = 1
setchild!(e::Ylamlam, i::Int, child) = (@assert i == 1 && (e.body = child))
getchild(e::Ylamlam, i::Int) = (@assert i == 1 && e.body)
unifies(e1::Ylamlam, e2::Ylamlam) = unifies(e1.body, e2.body)

mutable struct If <: PExpr
    cond::PExpr
    then_expr::PExpr
    else_expr::PExpr
end
num_children(e::If) = 3
setchild!(e::If, i::Int, child) = (
    if i == 1
        e.cond = child
    elseif i == 2
        e.then_expr = child
    elseif i == 3
        e.else_expr = child
    else
        error("If only has 3 children")
    end
)
getchild(e::If, i::Int) = (
    if i == 1
        e.cond
    elseif i == 2
        e.then_expr
    elseif i == 3
        e.else_expr
    else
        error("If only has 3 children")
    end
)
unifies(e1::If, e2::If) =
    unifies(e1.cond, e2.cond) &&
    unifies(e1.then_expr, e2.then_expr) &&
    unifies(e1.else_expr, e2.else_expr)

struct NullExpr <: PExpr end
const NULL::NullExpr = NullExpr()
nulls(n) = fill(NULL, n)
# null unifies with anything
num_children(e::NullExpr) = 0
unifies(e1::NullExpr, e2::PExpr) = true
unifies(e1::PExpr, e2::NullExpr) = true

# struct HoleExpr <: PExpr end
# nulls(n) = fill(NULL, n)
# # null unifies with anything
# num_children(e::NullExpr) = 0
# unifies(e1::NullExpr, e2::PExpr) = true
# unifies(e1::PExpr, e2::NullExpr) = true


mutable struct Root <: PExpr
    body::PExpr
end
num_children(e::Root) = 1
setchild!(e::Root, i::Int, child) = (@assert i == 1; (e.body = child))
getchild(e::Root, i::Int) = (@assert i == 1; e.body)
unifies(e1::Root, e2::Root) = unifies(e1.body, e2.body)

# TODO: should constructing this (or looking it up?) change the gensyms?
struct Defined <: PExpr
    name::Symbol
end
num_children(e::Defined) = 0
unifies(e1::Defined, e2::Defined) = e1.name == e2.name


abstract type Primitive end
abstract type RandomPrimitive <: Primitive end

is_random(e::RandomPrimitive) = true
is_random(e::Primitive) = false

mutable struct PrimOp <: PExpr
    op::Primitive
    args::Vector{PExpr}
end
num_children(e::PrimOp) = length(e.args)
setchild!(e::PrimOp, i::Int, child) = (e.args[i] = child)
getchild(e::PrimOp, i::Int) = e.args[i]
unifies(e1::PrimOp, e2::PrimOp) =
    e1.op == e2.op &&
    length(e1.args) == length(e2.args) &&
    all([unifies(e1.args[i], e2.args[i]) for i ∈ 1:length(e1.args)])

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
            return CaseOf(cond, Dict(:True => then_expr, :False => else_expr), [:True, :False]), view(tokens, 2:length(tokens))
        elseif token == "ylamlam"
            # Parse a Y lam lam
            tokens = view(tokens, 2:length(tokens))
            body, tokens = parse_expr_inner(tokens, defs, env)
            tokens[1] != ")" && error("expected closing paren")
            return Ylamlam(body), view(tokens, 2:length(tokens))
        elseif token == "Y"
            # parse a Y
            tokens = view(tokens, 2:length(tokens))
            type_params, tokens = parse_type_params(tokens)
            f, tokens = parse_expr_inner(tokens, defs, env)
            e = Y(f, type_params...)
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
            cases = Dict()
            constructors = []
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
                @assert !in(constructor, constructors) "duplicate constructor in case..of"
                push!(constructors, constructor)
                cases[constructor] = body
                if tokens[1] == "|"
                    tokens = view(tokens, 2:length(tokens))
                end
            end
            return CaseOf(scrutinee, cases, constructors), view(tokens, 2:length(tokens))
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
        elseif haskey(spt_of_constructor, Symbol(token))
            # parse a sum product type constructor
            constructor = Symbol(token)
            spt = spt_of_constructor[constructor]
            tokens = view(tokens, 2:length(tokens))
            args = []
            while tokens[1] != ")"
                arg, tokens = parse_expr_inner(tokens, defs, env)
                push!(args, arg)
            end
            return Construct(spt, constructor, args), view(tokens, 2:length(tokens))
        elseif haskey(primops, token) && !haskey(defs, Symbol(token))
            op_type, arity = primops[token]
            tokens = view(tokens, 2:length(tokens))
            type_params, tokens = parse_type_params(tokens)
            op = op_type(type_params...)
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
                args = [Construct(spt_of_constructor[:Unit], :Unit, PExpr[])]
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
        if isdigit(token[2])
            # parse debruijn index
            idx = parse(Int, token[2:end])
            @assert idx > 0 "need one-index debruijn"
            return Var(idx), view(tokens, 2:length(tokens))
        else
            # parse CFG symbol variable like "#int"
            type = parse_type(token[2:end])
            return VarCFGSymbol(type), view(tokens, 2:length(tokens))
        end
    elseif '#' ∈ token
        # variable combining name and debruijn like x#4
        parts = split(token, "#")
        name = Symbol(parts[1])
        idx = parse(Int, parts[2])
        @assert parts[1] == env[idx] "debruijn index must match variable name"
        return Var(idx, name), view(tokens, 2:length(tokens))
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
        error("unknown token: $token")
    end
end

value_mode::Symbol = :peano
@inline get_value_mode()::Symbol = value_mode
function set_value_mode(m::Symbol)
    global value_mode
    value_mode = m
    make_digits_values()
end


function const_to_expr(v::Int)
    if value_mode === :peano
        parse_expr(peano_str(v))
    else
        Const(v)
    end
end
const_to_expr(v::Float64) = ConstReal(v)
const_to_expr(v::Bool) =
    v ? Construct(bool, :True, Symbol[]) : Construct(bool, :False, Symbol[])


function parse_type_params(tokens)
    tokens[1] != "{" && return (PType[], tokens)
    tokens = view(tokens, 2:length(tokens))
    type_params = PType[]
    idx_end = findfirst(x -> x == "}", tokens)
    @assert !isnothing(idx_end)
    annotation_str = join(tokens[1:idx_end-1], " ")
    type_params = parse_type.(split(annotation_str, ","))
    tokens = tokens[idx_end+1:end]
    return (type_params, tokens)
end

function parse_expr(s::String, defs)
    tokens = tokenize(s)
    expr, rest = parse_expr_inner(tokens, defs, [])
    @assert isempty(rest)
    return expr
end

parse_expr(s::String) = parse_expr(s, DEFINITIONS)


has_null(e::PExpr) = e == NULL || any(has_null(getchild(e, i)) for i ∈ 1:num_children(e))
function null_paths(e::PExpr; path=[])
    if e == NULL
        return [path]
    end
    paths = []
    for i ∈ 1:num_children(e)
        if has_null(getchild(e, i))
            push!(paths, null_paths(getchild(e, i); path=[path..., i])...)
        end
    end
    paths
end

@inline function is_randomness_terminal(e::PExpr, dsl)
    any(term -> term[1] == e, dsl.randomness_terminals)
end

@inline function typeof_randomness_terminal(e::PExpr, dsl)
    for (term, ty) in dsl.randomness_terminals
        if term == e
            return ty
        end
    end
end

randomness_terminals_of_type(dsl, ty) =
    (term for (term, ty2) in dsl.randomness_terminals if ty2 == ty)
randomness_terminals_of_type(dsl, ty::String) =
    randomness_terminals_of_type(dsl, parse_type(ty))

function randomness_terminals_of_types(dsl, tys)
    arg_options = Vector{Vector{PExpr}}(undef, length(tys))
    # could be condensed into one iterator
    for (i, argtype) in enumerate(tys)
        arg_options[i] = PExpr[]
        for term in randomness_terminals_of_type(dsl, argtype)
            push!(arg_options[i], term)
        end
    end
    Iterators.product(arg_options...)
end


# function randomness_terminals_of_types(dsl, tys)
#     arg_options = Vector{Vector{PExpr}}(undef, num_args(t))
#     for argtype in tys
#         arg_options[argtype.idx] = PExpr[]
#         for term in randomness_terminals_of_type(dsl, argtype)
#             push!(arg_options[argtype.idx], term[1])
#         end
#     end
#     Iterators.product(arg_options...)
# end






has_randomness_terminal(e::PExpr, dsl) =
    is_randomness_terminal(e, dsl) ||
    any(has_randomness_terminal(getchild(e, i), dsl) for i ∈ 1:num_children(e))

function randomness_terminal_paths(e::PExpr, dsl; path=[])
    if is_randomness_terminal(e, dsl)
        return [(path, typeof_randomness_terminal(e, dsl))]
    end
    paths = []
    for i ∈ 1:num_children(e)
        if has_randomness_terminal(getchild(e, i), dsl)
            push!(
                paths,
                randomness_terminal_paths(getchild(e, i), dsl; path=[path..., i])...,
            )
        end
    end
    paths
end

# function check_var_types(e::PExpr; path=[])
#     if e isa Var
#         return [path]
#     end
#     paths = []
#     for i in 1:num_children(e)
#         push!(paths, var_paths(getchild(e, i); path=[path..., i])...)
#     end
#     paths
# end

# check_type(e::Var, t, env) = e.idx <= length(env) && env[e.idx] == t


# # function check_type(e, t, env)

# # end

max_free_var(e::Var) = e.idx
max_free_var(e::Abs) = max(0, max_free_var(e.body) - 1)
max_free_var(e::App) = max(max_free_var(e.f), max_free_var(e.x))
max_free_var(e::Const) = 0
max_free_var(e::ConstReal) = 0
max_free_var(e::ConstBool) = 0
max_free_var(e::If) =
    max(max_free_var(e.cond), max(max_free_var(e.then_expr), max_free_var(e.else_expr)))
max_free_var(e::Ylamlam) = max(0, max_free_var(e.body) - 2)
max_free_var(e::Y) = max_free_var(e.f)
max_free_var(e::Defined) = 0
max_free_var(e::Root) = max_free_var(e.body)
max_free_var(e::PrimOp) = reduce(max, max_free_var(arg) for arg in e.args; init=0)
max_free_var(e::NullExpr) = 0
max_free_var(e::CaseOf) = max(
    max_free_var(e.scrutinee),
    reduce(max, max_free_var(case) for case in values(e.cases); init=0),
)
max_free_var(e::Construct) = reduce(max, max_free_var(arg) for arg in e.args; init=0)

# true if #1 is a free var in the expr. Depth should start at 1.
var_is_free(e::Var, var) = e.idx == var
var_is_free(e::Abs, var) = var_is_free(e.body, var + 1)
var_is_free(e::App, var) = var_is_free(e.f, var) || var_is_free(e.x, var)
var_is_free(e::Const, var) = false
var_is_free(e::ConstReal, var) = false
var_is_free(e::ConstBool, var) = false
var_is_free(e::If, var) =
    var_is_free(e.cond, var) ||
    var_is_free(e.then_expr, var) ||
    var_is_free(e.else_expr, var)
var_is_free(e::Ylamlam, var) = var_is_free(e.body, var + 2)
var_is_free(e::Y, var) = var_is_free(e.f, var)
var_is_free(e::Defined, var) = false
var_is_free(e::Root, var) = var_is_free(e.body, var)
var_is_free(e::PrimOp, var) = any(var_is_free(arg, var) for arg in e.args)
var_is_free(e::NullExpr, var) = false
var_is_free(e::CaseOf, var) =
    var_is_free(e.scrutinee, var) || any(case -> var_is_free(case, var), values(e.cases))
var_is_free(e::Construct, var) = any(arg -> var_is_free(arg, var), e.args)
var_is_free(e::RawInt, var) = false


is_random(e::Var) = false
is_random(e::Abs) = is_random(e.body)
is_random(e::App) = is_random(e.f) || is_random(e.x)
is_random(e::Const) = false
is_random(e::ConstReal) = false
is_random(e::ConstBool) = false
is_random(e::If) = is_random(e.cond) || is_random(e.then_expr) || is_random(e.else_expr)
is_random(e::Ylamlam) = is_random(e.body)
is_random(e::Y) = is_random(e.f)
is_random(e::Defined) = lookup(e.name).is_random
is_random(e::Root) = is_random(e.body)
is_random(e::PrimOp) = is_random(e.op) || any(is_random(arg) for arg in e.args)
is_random(e::NullExpr) = false
is_random(e::CaseOf) = is_random(e.scrutinee) || any(is_random(case) for case in values(e.cases))
is_random(e::Construct) = any(is_random(arg) for arg in e.args)
is_random(e::AuxCFGSymbol) = false
is_random(e::VarCFGSymbol) = false
is_random(e::RawInt) = false


shortname(e::PExpr) = string(e)
shortname(e::App) = "App"
shortname(e::Abs) = "λ" * string(e.name)
shortname(e::If) = "If"
shortname(e::Ylamlam) = "Ylamlam"
shortname(e::Y) = "Y"
shortname(e::PrimOp) = string(e.op)
shortname(e::CaseOf) = "CaseOf"
shortname(e::Construct) = string(e.constructor)
shortname(e::RawInt) = "&"

Base.show(io::IO, e::Var) =
    e.name === :noname ? print(io, "#", e.idx) : print(io, e.name, "#", e.idx)
Base.show(io::IO, e::Root) = print(io, "(root ", e.body, ")")
function Base.show(io::IO, e::Abs)
    print(io, "(λ", e.name)
    while e.body isa Abs
        e = e.body
        print(io, " ", e.name)
    end
    print(io, " -> ", e.body, ")")
end
Base.show(io::IO, e::Ylamlam) = print(io, "(ylamlam", e.body, ")")
function Base.show(io::IO, e::Y)
    annotation = isnothing(e.t0) ? "" : "{$(e.t0),$(e.t1)}"
    print(io, "(Y$annotation ", e.f, ")")
end
Base.show(io::IO, e::Const) = print(io, e.val)
Base.show(io::IO, e::ConstReal) = print(io, e.val)
Base.show(io::IO, e::ConstBool) = print(io, e.val)
Base.show(io::IO, e::If) =
    print(io, "(if ", e.cond, " ", e.then_expr, " ", e.else_expr, ")")

function Base.show(io::IO, e::App)
    print(io, "(", get_func(e))
    for i ∈ 1:num_apps(e)
        print(io, " ", getarg(e, i))
    end
    print(io, ")")
end

function Base.show(io::IO, e::PrimOp)
    print(io, "(", e.op)
    for arg in e.args
        print(io, " ", arg)
    end
    print(io, ")")
end
Base.show(io::IO, e::Defined) = print(io, e.name)
Base.show(io::IO, e::NullExpr) = print(io, "??")
Base.show(io::IO, e::RandomnessCFGSymbol) = print(io, "~", e.type)
Base.show(io::IO, e::AuxCFGSymbol) = print(io, "?", e.name)
Base.show(io::IO, e::RawInt) = print(io, "&", e.val)
Base.show(io::IO, e::VarCFGSymbol) = print(io, "#", e.type)
function Base.show(io::IO, e::CaseOf)
    print(io, "(case ", e.scrutinee, " of ")
    for (i, constructor) in enumerate(e.constructors)
        print(io, constructor, " => ", e.cases[constructor])
        if i < length(e.constructors)
            print(io, " | ")
        end
    end
    print(io, ")")
end

function Base.show(io::IO, e::Construct)
    as_const = maybe_const(e)
    if !isnothing(as_const)
        print(io, as_const)
        return
    end
    print(io, "(", e.constructor)
    for arg in e.args
        print(io, " ", arg)
    end
    print(io, ")")
end


stitch_str(e::Var) = "\$" * string(e.idx - 1)
stitch_str(e::Abs) = "(lam " * stitch_str(e.body) * ")"
function stitch_str(e::App)
    res = "("
    res *= stitch_str(get_func(e))
    for i ∈ 1:num_apps(e)
        res *= " " * stitch_str(getarg(e, i))
    end
    res * ")"
end
stitch_str(e::Const) = string(e.val)
stitch_str(e::ConstReal) = string(e.val)
stitch_str(e::ConstBool) = string(e.val)
stitch_str(e::If) = "(if " * stitch_str(e.cond) * " " * stitch_str(e.then_expr) * " " * stitch_str(e.else_expr) * ")"
stitch_str(e::Y) = "(Y{$(e.t0),$(e.t1)} " * stitch_str(e.f) * ")"
stitch_str(e::Defined) = string(e.name)
stitch_str(e::PrimOp) = "(" * string(e.op) * " " * join((stitch_str(arg) for arg in e.args), " ") * ")"
function stitch_str(e::CaseOf)
    # this one is pretty annoying since stitch doesnt have caseof.
    # first we make a special function primitive for this caseof based on its constructors / their order:
    res = "(case{" * join(string.(e.constructors), ",") * "}"
    # then we say the first argument is the scrutinee
    res *= " " * stitch_str(e.scrutinee)
    # then we say the rest of the arguments are the cases in order, and we need to insert the appropriate lambdas
    for constructor in e.constructors
        # num_lams = length(args_of_constructor(constructor))
        # res *= " (lam" ^ num_lams * " (" * stitch_str(e.cases[constructor]) * ")" * ")" ^ num_lams
        res *= " " * stitch_str(e.cases[constructor])
    end
    res * ")"
end
function stitch_str(e::Construct)
    as_const = maybe_const(e)
    !isnothing(as_const) && return string(as_const)
    "(" * string(e.constructor) * (isempty(e.args) ? "" : " ") * join((stitch_str(arg) for arg in e.args), " ") * ")"
end







maybe_const(e) = nothing
function maybe_const(e::Construct)
    if e.spt.name == :nat
        if e.constructor == :O
            return 0
        end
        @assert e.constructor == :S
        inner = maybe_const(e.args[1])
        isnothing(inner) && return nothing
        return inner + 1
    end
    return nothing
end


Base.copy(e::PExpr) = error("not implemented")
Base.copy(e::Var) = Var(e.idx, e.name)
Base.copy(e::Abs) = Abs(copy(e.body), e.name)
Base.copy(e::App) = App(copy(e.f), copy(e.x))
Base.copy(e::Const) = Const(e.val)
Base.copy(e::ConstReal) = ConstReal(e.val)
Base.copy(e::ConstBool) = ConstBool(e.val)
Base.copy(e::If) = If(copy(e.cond), copy(e.then_expr), copy(e.else_expr))
Base.copy(e::Ylamlam) = Ylamlam(copy(e.body))
Base.copy(e::Y) = Y(copy(e.f), e.t0, e.t1)
Base.copy(e::Defined) = Defined(e.name)
Base.copy(e::Root) = Root(copy(e.body))
Base.copy(e::PrimOp) = PrimOp(e.op, [copy(arg) for arg in e.args])
Base.copy(e::NullExpr) = NULL
Base.copy(e::RandomnessCFGSymbol) = RandomnessCFGSymbol(e.type)
Base.copy(e::AuxCFGSymbol) = AuxCFGSymbol(e.name)
Base.copy(e::RawInt) = RawInt(e.val)
Base.copy(e::VarCFGSymbol) = VarCFGSymbol(e.type)
Base.copy(e::CaseOf) = CaseOf(
    copy(e.scrutinee),
    Dict(constructor => copy(e.cases[constructor]) for constructor in keys(e.cases)),
    copy(e.constructors),
)
Base.copy(e::Construct) = Construct(e.spt, e.constructor, [copy(arg) for arg in e.args])

Base.:(==)(a::Var, b::Var) = a.idx == b.idx
Base.:(==)(a::Abs, b::Abs) = a.body == b.body
Base.:(==)(a::App, b::App) = a.f == b.f && a.x == b.x
Base.:(==)(a::Const, b::Const) = a.val == b.val
Base.:(==)(a::ConstReal, b::ConstReal) = a.val == b.val
Base.:(==)(a::ConstBool, b::ConstBool) = a.val == b.val
Base.:(==)(a::If, b::If) =
    a.cond == b.cond && a.then_expr == b.then_expr && a.else_expr == b.else_expr
Base.:(==)(a::Ylamlam, b::Ylamlam) = a.body == b.body
Base.:(==)(a::Y, b::Y) = a.f == b.f
Base.:(==)(a::Defined, b::Defined) = a.name == b.name
Base.:(==)(a::Root, b::Root) = a.body == b.body
Base.:(==)(a::PrimOp, b::PrimOp) = a.op == b.op && a.args == b.args
Base.:(==)(a::NullExpr, b::NullExpr) = true
Base.:(==)(a::RandomnessCFGSymbol, b::RandomnessCFGSymbol) = a.type == b.type
Base.:(==)(a::AuxCFGSymbol, b::AuxCFGSymbol) = a.name == b.name
Base.:(==)(a::RawInt, b::RawInt) = a.val == b.val
Base.:(==)(a::VarCFGSymbol, b::VarCFGSymbol) = a.type == b.type
Base.:(==)(a::CaseOf, b::CaseOf) =
    a.scrutinee == b.scrutinee &&
    a.constructors == b.constructors &&
    all(constructor -> a.cases[constructor] == b.cases[constructor], a.constructors)
Base.:(==)(a::Construct, b::Construct) =
    a.spt.name === b.spt.name && a.constructor === b.constructor && a.args == b.args

# the type inclusion isnt too important here, just deconflicts a bit
# to avoid collision between things like (λx. 3) and 3. 
Base.hash(e::Var, h::UInt) = hash(e.idx, hash(:Var, h))
Base.hash(e::Abs, h::UInt) = hash(e.body, hash(:Abs, h))
Base.hash(e::App, h::UInt) = hash(e.f, hash(e.x, hash(:App, h)))
Base.hash(e::Const, h::UInt) = hash(e.val, hash(:Const, h))
Base.hash(e::ConstReal, h::UInt) = hash(e.val, hash(:ConstReal, h))
Base.hash(e::ConstBool, h::UInt) = hash(e.val, hash(:ConstBool, h))
Base.hash(e::If, h::UInt) = hash(e.cond, hash(e.then_expr, hash(e.else_expr, hash(:If, h))))
Base.hash(e::Ylamlam, h::UInt) = hash(e.body, hash(:Ylamlam, h))
Base.hash(e::Y, h::UInt) = hash(e.f, hash(:Y, h))
Base.hash(e::Defined, h::UInt) = hash(e.name, hash(:Defined, h))
Base.hash(e::Root, h::UInt) = hash(e.body, hash(:Root, h))
Base.hash(e::PrimOp, h::UInt) = hash(e.op, hash(e.args, hash(:PrimOp, h)))
Base.hash(e::NullExpr, h::UInt) = hash(:NullExpr, h)
Base.hash(e::RandomnessCFGSymbol, h::UInt) = hash(e.type, hash(:RandomnessCFGSymbol, h))
Base.hash(e::AuxCFGSymbol, h::UInt) = hash(e.name, hash(:AuxCFGSymbol, h))
Base.hash(e::RawInt, h::UInt) = hash(e.val, hash(:RawInt, h))
Base.hash(e::VarCFGSymbol, h::UInt) = hash(e.type, hash(:VarCFGSymbol, h))
Base.hash(e::CaseOf, h::UInt) =
    hash(e.scrutinee, hash(e.cases, hash(e.constructors, hash(:CaseOf, h))))
Base.hash(e::Construct, h::UInt) =
    hash(e.spt.name, hash(e.constructor, hash(e.args, hash(:Construct, h))))




# Base.hash(e::PExpr, h::UInt) = hash(typeof(e), h)

# shallow_eq(a::PExpr, b::PExpr) = false
# shallow_eq(a::Var, b::Var) = a.idx == b.idx
# shallow_eq(a::Abs, b::Abs) = true
# shallow_eq(a::App, b::App) = true
# shallow_eq(a::Const, b::Const) = a.val == b.val
# shallow_eq(a::ConstReal, b::ConstReal) = a.val == b.val
# shallow_eq(a::ConstBool, b::ConstBool) = a.val == b.val
# shallow_eq(a::If, b::If) = true
# shallow_eq(a::Ylamlam, b::Ylamlam) = true
# shallow_eq(a::Y, b::Y) = true
# shallow_eq(a::Defined, b::Defined) = a.name === b.name
# shallow_eq(a::Root, b::Root) = true
# shallow_eq(a::PrimOp, b::PrimOp) = a.op === b.op
# shallow_eq(a::NullExpr, b::NullExpr) = true
# shallow_eq(a::RandomnessCFGSymbol, b::RandomnessCFGSymbol) = a.type == b.type
# shallow_eq(a::AuxCFGSymbol, b::AuxCFGSymbol) = a.name === b.name
# shallow_eq(a::VarCFGSymbol, b::VarCFGSymbol) = a.type == b.type
# shallow_eq(a::CaseOf, b::CaseOf) = error("todo impl")
# shallow_eq(a::Construct, b::Construct) = error("todo impl")


# (app f x y) -> (app (app f x) y)

num_apps(e::App) = 1 + num_apps(e.f)
num_apps(e::PExpr) = 0

get_func(e::App) = get_func(e.f)
get_func(e::PExpr) = e

get_args(e::App) = [get_args(e.f)..., e.x]
get_args(e::PExpr) = PExpr[]

getarg(e::PExpr, i) = error("arg doesnt exist")
function getarg(e::App, i)
    # for an app chain (app (app f x) y) we want x to be the 1st arg and y to be
    # the second arg.
    which_app = num_apps(e) - i + 1
    for _ ∈ 1:which_app-1
        e = e.f
    end
    e.x
end
getarg(e::PrimOp, i) = e.args[i]


# flatten_args()
num_children(e::App) = num_apps(e) + 1




struct ChildInfo
    e::PExpr
    type::PType
    env::Vector{PType}
    path::Vector{Int}
end


get_func_type(f::Defined, env) = lookup(f.name).type::PType
get_func_type(f::Var, env) = env[f.idx]
function get_func_type(y::Y, env)
    @assert !isnothing(y.t0) && !isnothing(y.t1) "y operator type annotation required for inference"
    Arrow([y.t0], y.t1)
end


getchildtype(e::If, i::Int, t, env) = (i == 1 ? BaseType(:bool) : t)

function getchildtype(e::Construct, i::Int, t, env)
    type_of_spt[args_of_constructor(e.constructor)[i]]
end

function getchildtype(e::CaseOf, i::Int, t, env)
    if i == 1
        # scrutinee - look it up based on the first constructor
        return type_of_spt[spt_of_constructor[e.constructors[1]].name]
    else
        # branches are lambdas from the constructor args to the return type
        constructor = e.constructors[i-1]
        arg_types = [type_of_spt[arg] for arg in args_of_constructor(constructor)]
        length(arg_types) == 0 && return t
        return Arrow(arg_types, t)
    end
end


function getchildtype(e::App, i::Int, t, env)
    f = get_func(e)
    ftype = get_func_type(f, env)
    i == 1 && return ftype
    return arg_types(ftype)[i-1]
end

function getchildtype(e::PrimOp, i::Int, t, env)
    return arg_types(prim_type(e.op))[i]
end

function getchildtype(e::Abs, i::Int, t, env)
    if num_args(t) == 1
        return_type(t)
    else
        Arrow(arg_types(t)[2:end], return_type(t))
    end
end

function getchildtype(y::Y, i::Int, t, env)
    @assert !isnothing(y.t0) && !isnothing(y.t1) "y operator type annotation required for inference"
    # todo could ofc be smarter about this - eg precomputing and stashing in `Y`
    return parse_type("(($(y.t0) -> $(y.t1)) -> $(y.t0) -> $(y.t1))")
end


# expansion_targets(e::Var, t, env, path) = ChildInfo[]
# expansion_targets(e::Const, t, env, path) = ChildInfo[]
# expansion_targets(e::ConstReal, t, env, path) = ChildInfo[]
# expansion_targets(e::ConstBool, t, env, path) = ChildInfo[]
# expansion_targets(e::Defined, t, env, path) = ChildInfo[]
# expansion_targets(e::Ylamlam, t, env, path) = error("not possible")
# expansion_targets(e::Abs, t, env, path) = error("not possible")

# function expansion_targets(e::If, t, env, path)
#     ChildInfo[ChildInfo(e.cond, BaseType(:bool), env, vcat(path, [1])),
#               ChildInfo(e.then_expr, t, env, vcat(path, [2])),
#               ChildInfo(e.else_expr, t, env, vcat(path, [3]))]
# end

# function expansion_targets(e::App, t, env, path)
#     f = get_func(e)
#     args = get_args(e)
#     argtypes = if f isa Var
#         arg_types(env[f.idx])
#     elseif f isa Defined
#         arg_types(DEF_TYPES[f.name])
#     else
#         error("invalid f on lefthand side of App: $f")
#     end

#     # descend into any lambdas
#     [ChildInfo(
#         strip_abs(arg),
#         return_type(argtype),
#         vcat(reverse(arg_types(argtype)), env),
#         vcat(path, [i+1, fill(1, num_abs(arg))...]) # skip over `f` (getchild(1) is `f` for App)
#         ) for (i,argtype,arg) in zip(1:length(args), argtypes, args)]

# end

# function expansion_targets(e::PrimOp, t, env, path)
#     argtypes = arg_types(prim_type(e.op))
#     [ChildInfo(
#         strip_abs(arg),
#         return_type(argtype),
#         vcat(reverse(arg_types(argtype)), env),
#         vcat(path, [i, fill(1, num_abs(arg))...]),
#         ) for (i,argtype,arg) in zip(1:length(argtypes), argtypes, e.args)]
# end

JSON.lower(e::PExpr) = string(e)


function is_closed(e::PExpr, type::PType, env::Vector{PType})
    se = SubExpr(e, type, env)
    for d in descendants_inplace(se)
        if d.child isa Var
            if d.child.idx > length(d.env)
                return false
            end
        end
    end
    return true
end

struct RenderedHole <: PExpr
    expr::PExpr
    prefix::String
    suffix::String
end

function Base.show(io::IO, h::RenderedHole)
    print(io, h.prefix)
    print(io, h.expr)
    print(io, h.suffix)
end

function highlight_subexpression(expr, path, prefix, suffix)

    if isempty(path)
        return string(RenderedHole(expr, prefix, suffix))
    else
        expr = copy(expr)
        child_at_path = getchild(expr, path)
        setchild!(expr, path, RenderedHole(child_at_path, prefix, suffix))
        return string(expr)
    end

end

function setchild_or_root(e::PExpr, path::Vector{Int}, replacement::PExpr)
    isempty(path) && return replacement
    setchild!(e, path, replacement)
    e
end


function cfg_symbol_paths(e::PExpr)
    res = Vector{Tuple{CFGSymbol,Vector{Int}}}()
    for (e, path) in descendants_untyped(e)
        if e isa CFGSymbol
            push!(res, (e, path))
        end
    end
    res
end