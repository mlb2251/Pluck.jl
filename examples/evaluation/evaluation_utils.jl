using BenchmarkTools
"""
Adaptation of btime from BenchmarkTools.jl
"""
macro bbtime(args...)
    _, params = BenchmarkTools.prunekwargs(args...)
    bench, trial, result = gensym(), gensym(), gensym()
    trialmin, trialallocs = gensym(), gensym()
    tune_phase = BenchmarkTools.hasevals(params) ? :() : :($BenchmarkTools.tune!($bench))
    return esc(
        quote
            local $bench = $BenchmarkTools.@benchmarkable $(args...)
            $tune_phase
            local $trial, $result = $BenchmarkTools.run_result(
                $bench; warmup=$(BenchmarkTools.hasevals(params))
            )
            local $trialmin = $BenchmarkTools.minimum($trial)
            local $trialallocs = $BenchmarkTools.allocs($trialmin)
            println(
                "  ",
                $BenchmarkTools.time($trialmin)/1e6, " ms",
                " (",
                $trialallocs,
                " allocation",
                $trialallocs == 1 ? "" : "s",
                ": ",
                $BenchmarkTools.prettymemory($BenchmarkTools.memory($trialmin)),
                ")",
            )
            $result
        end,
    )
end