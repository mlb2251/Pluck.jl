
# result of evaluating a lambda. Takes 1 argument.
mutable struct Closure <: AbstractValue
    expr::Union{PExpr, Thunk}
    env::Env
    name::Symbol
    origin::PExpr # debug / stacktrace info
end

function Base.show(io::IO, c::Closure)
    print(io, "(Closure from $(c.origin) name=$(c.name) body=$(c.expr))")
end