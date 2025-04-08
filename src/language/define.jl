export DEFINITIONS,
    @define, @lookup, reset_definitions, define

struct Definition
    name::Symbol
    expr::PExpr
end

DUMMY_EXPRESSION = Construct(:Unit, PExpr[])

const DEFINITIONS::Dict{Symbol, Definition} = Dict{Symbol, PExpr}()

macro define(name, str)
    :(define($(QuoteNode(name)), $str))
end

function define(name, str)
    name = Symbol(name)
    if haskey(DEFINITIONS, name)
        @warn "definition for $name already exists, overwriting"
    end
    DEFINITIONS[name] = Definition(name, DUMMY_EXPRESSION)
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

function reset_definitions()
    empty!(DEFINITIONS)
end
