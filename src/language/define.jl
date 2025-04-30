export DEFINITIONS,
    @define, @lookup, reset_definitions, define, deftype, @deftype, DEF_TYPES


struct Definition
    name::Symbol
    expr::PExpr
    type::Union{PType,Nothing}
end

const DEFINITIONS::Dict{Symbol, Definition} = Dict{Symbol, PExpr}()
const DEF_TYPES::Dict{Symbol, PType} = Dict{Symbol, PType}()

# function deftype(name, str)
#     DEF_TYPES[Symbol(name)] = parse_type(str)
#     return name
# end

macro define(name, str)
    :(define($(QuoteNode(name)), $str))
end

macro define(name, typestr, str)
    :(define($(QuoteNode(name)), $str; typestr=$typestr))
end


function define(name, str; typestr=nothing)
    name = Symbol(name)
    expr = parse_expr(str)
    type = isnothing(typestr) ? nothing : parse_type(typestr)
    DEFINITIONS[name] = Definition(name, expr, type)
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
