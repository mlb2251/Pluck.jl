export DEFINITIONS,
    @define, @lookup, reset_definitions, define, isdef

struct Definition
    name::Symbol
    expr::PExpr
end

DUMMY_EXPRESSION = Construct(:Unit)()

const DEFINITIONS::Dict{Symbol, Definition} = Dict{Symbol, PExpr}()

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
end
