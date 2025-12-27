export DEFINITIONS,
    @define, @lookup, reset_definitions, define, isdef,
    defined_name_for_expr, register_definition_expr

struct Definition
    name::Symbol
    expr::PExpr
end

DUMMY_EXPRESSION = Construct(:Unit)()

const DEFINITIONS::Dict{Symbol, Definition} = Dict{Symbol, PExpr}()
const DEF_EXPR_NAME = IdDict{PExpr, Symbol}()

macro define(name, str)
    :(define($(QuoteNode(name)), $str))
end

function define(name, str)
    name = Symbol(name)
    if haskey(DEFINITIONS, name)
        # @warn "definition for $name already exists, overwriting"
    else
        # only do dummy here bc of race condition with @define being called from many threads
        # you dont want it to briefly be set to unit and get used like that by another thread
        DEFINITIONS[name] = Definition(name, DUMMY_EXPRESSION)
    end
    try
        expr = parse_expr(str)
        DEFINITIONS[name] = Definition(name, expr)
        register_definition_expr(name, expr)
    catch e
        delete!(DEFINITIONS, name)
        rethrow(e)
    end
    return name
end

function lookup(name::Symbol)::Definition
    DEFINITIONS[name]
end

function isdef(name::Symbol)
    haskey(DEFINITIONS, name)
end

function reset_definitions()
    empty!(DEFINITIONS)
    empty!(DEF_EXPR_NAME)
end

# Lookup a definition name by the PExpr pointer (used for callframe labeling)
function defined_name_for_expr(expr::PExpr)
    get(DEF_EXPR_NAME, expr, nothing)
end

# Register a mapping from a parsed expression (and any nested curried lambdas) to its definition name.
function register_definition_expr(name::Symbol, expr::PExpr)
    DEF_EXPR_NAME[expr] = name
    # If this is a curried lambda chain, also register nested Abs nodes.
    while expr isa PExpr{Abs}
        expr = expr.args[1]
        expr isa PExpr || break
        DEF_EXPR_NAME[expr] = name
    end
end
