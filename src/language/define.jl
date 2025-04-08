export DEFINITIONS,
    @define, @lookup, reset_definitions, define

struct Definition
    name::Symbol
    expr::PExpr
    type::Union{PType,Nothing}
end

DUMMY_EXPRESSION = Construct(:Unit, PExpr[])

const DEFINITIONS::Dict{Symbol, Definition} = Dict{Symbol, PExpr}()

macro define(name, str)
    :(define($(QuoteNode(name)), $str))
end

macro define(name, typestr, str)
    :(define($(QuoteNode(name)), $str; typestr=$typestr))
end

function define(name, str; typestr=nothing)
    name = Symbol(name)
    type = typestr === nothing ? nothing : parse_type(typestr)
    DEFINITIONS[name] = Definition(name, DUMMY_EXPRESSION, type)
    try
        expr = parse_expr(str)
        DEFINITIONS[name] = Definition(name, expr, type)
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
