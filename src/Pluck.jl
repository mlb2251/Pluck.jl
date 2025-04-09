module Pluck

using JSON: JSON

include("RSDD/RSDD.jl")
using .RSDD

include("util/util.jl")
include("language/types.jl")
include("language/pexpr.jl")
include("language/parsing.jl")
include("language/values.jl")
include("language/closures.jl")
include("language/primitives.jl")
include("language/define.jl")
include("likelihood/enumeration.jl")
include("likelihood/int_dists.jl")
include("likelihood/lazy_knowledge_compilation.jl")
include("likelihood/LPSMC.jl")
include("likelihood/eager_knowledge_compilation.jl")
include("likelihood/posterior_sampling.jl")
include("language/toplevel.jl")
include("util/bdd_viz.jl")
export get_rsdd_time, clear_rsdd_time!, @rsdd_time

load_pluck_file(joinpath(@__DIR__, "language", "stdlib.pluck"))
end # module
