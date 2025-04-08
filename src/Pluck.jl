module Pluck

using JSON: JSON

include("RSDD/RSDD.jl")
include("util/util.jl")
include("language/types.jl")
include("language/pexpr.jl")
include("language/values.jl")
include("language/primitives.jl")
include("language/define.jl")
include("search/tasks.jl")
include("likelihood/lazy_enumerator.jl")
include("likelihood/bdd.jl")
include("likelihood/bdd_suspend.jl")
include("likelihood/bdd_eager.jl")
include("likelihood/sample_value.jl")
include("likelihood/posterior_sample.jl")
include("language/toplevel.jl")
include("likelihood/bdd_viz.jl")

export get_rsdd_time, clear_rsdd_time!, @rsdd_time

prims_minimal()
load_pluck_file(joinpath(@__DIR__, "language", "stdlib.pluck"))
end # module
