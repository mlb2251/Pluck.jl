export DEFINITIONS,
    @define, @lookup, reset_definitions, define


struct Definition
    name::Symbol
    expr::PExpr
    type::Union{PType,Nothing}
    is_random::Bool
end

DUMMY_EXPRESSION = Construct(spt_of_constructor[:Unit], :Unit, PExpr[])

const DEFINITIONS::Dict{Symbol, Definition} = Dict{Symbol, PExpr}()

macro define(name, str)
    :(define($(QuoteNode(name)), $str))
end

macro define(name, typestr, str)
    :(define($(QuoteNode(name)), $typestr, $str))
end


function define(name, typestr, str)
    name = Symbol(name)
    type = parse_type(typestr)
    DEFINITIONS[name] = Definition(name, DUMMY_EXPRESSION, type, false)
    try
        expr = parse_expr(str)
        DEFINITIONS[name] = Definition(name, expr, type, is_random(expr))
    catch e
        delete!(DEFINITIONS, name)
        rethrow(e)
    end
    return name
end

function define(name, str)
    name = Symbol(name)
    DEFINITIONS[name] = Definition(name, DUMMY_EXPRESSION, nothing, false)
    try
        expr = parse_expr(str)
        DEFINITIONS[name] = Definition(name, expr, nothing, is_random(expr))
    catch e
        delete!(DEFINITIONS, name)
        rethrow(e)
    end
    return name
end

function get_def(name::Symbol)::Definition
    DEFINITIONS[name]
end


macro lookup(name)
    :(DEFINITIONS[$(QuoteNode(name))])
end

function reset_definitions()
    empty!(DEFINITIONS)
end
