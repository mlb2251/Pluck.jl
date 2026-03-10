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


include("extensions/int_dists.jl")
include("likelihood/error.jl")

include("likelihood/compile_inner_defaults/core_ops.jl")


include("likelihood/lazy_knowledge_compilation/lazy_knowledge_compilation.jl")
include("likelihood/lazy_knowledge_compilation/thunks.jl")
include("likelihood/lazy_knowledge_compilation/monad.jl")
include("likelihood/lazy_knowledge_compilation/compile_inner.jl")
include("extensions/logging.jl")


include("extensions/optimize.jl")
include("likelihood/full_dist.jl")


include("extensions/LPSMC.jl")

include("extensions/sample_value/sample_value.jl")
include("extensions/sample_value/force_value.jl")
include("extensions/sample_value/compile_inner.jl")
include("extensions/sample_value/thunks.jl")
include("extensions/sample_value/monad.jl")
include("extensions/sample_value/int_dists.jl")

include("extensions/posterior_sampling.jl")

include("toplevel/parsing.jl")
include("toplevel/query.jl")
include("toplevel/eval.jl")
include("toplevel/printing.jl")

include("util/tests.jl")

export get_rsdd_time, clear_rsdd_time!, @rsdd_time

load_pluck_file(joinpath(@__DIR__, "language", "stdlib", "stdlib.pluck"))
end # module
