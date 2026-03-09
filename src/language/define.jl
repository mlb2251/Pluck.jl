export DEFINITIONS

struct Definition
    name::Symbol
    expr::PExpr
end

DUMMY_EXPRESSION = Construct(:Unit)()

const DEFINITIONS::Dict{Symbol, Definition} = Dict{Symbol, PExpr}()