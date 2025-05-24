module Pluck

using JSON: JSON

# include("util/timing.jl")
# using .Timing

include("RSDD/RSDD.jl")
using .RSDD

include("util/util.jl")
include("language/types.jl")
include("language/pexpr.jl")
include("language/parsing.jl")
include("language/values.jl")
include("language/closures.jl")
include("language/define.jl")
include("likelihood/enumeration/enumeration.jl")
include("likelihood/enumeration/thunks.jl")
include("likelihood/enumeration/monad.jl")
include("likelihood/enumeration/compile_inner.jl")
include("likelihood/int_dists.jl")
include("likelihood/lazy_knowledge_compilation/lazy_knowledge_compilation.jl")
include("likelihood/lazy_knowledge_compilation/thunks.jl")
include("likelihood/lazy_knowledge_compilation/monad.jl")
include("likelihood/lazy_knowledge_compilation/optimize.jl")
include("likelihood/lazy_knowledge_compilation/compile_inner.jl")
include("likelihood/LPSMC.jl")
include("likelihood/eager_knowledge_compilation.jl")
include("likelihood/posterior_sampling.jl")
include("language/toplevel.jl")
include("util/bdd_viz.jl")
include("util/tests.jl")
export get_rsdd_time, clear_rsdd_time!, @rsdd_time

load_pluck_file(joinpath(@__DIR__, "language", "stdlib.pluck"))
end # module
