# using Pkg
# Pkg.activate("/Users/mauriciobarba/repos/PluckArtifactDependency.jl")
# using Revise
using Pluck
# using .RSDD

# Small number of steps
prob, metaparam_vals = optimize(["(flip 0.5)"], 0.01, [], 1)
@assert isapprox(prob[1], 0.5)

prob, metaparam_vals = optimize(["(let (a (flipd @0)
                            b (not (flipd @0)))
                            (and a b))"], 0.05, [0.5 for _ ∈ 1:3], 1)
@assert prob[1] == 0.25
@assert metaparam_vals == [0.5, 0.5, 0.5]

prob, metaparam_vals = optimize(["(let (a (flipd @0)
                            b (not (flipd @0)))
                            (and a b))",
                            "(let (a (flipd @0)
                            b (not (flipd @0)))
                            (and a b))",], 0.1, [0.5 for _ ∈ 1:3], 1)
@assert prob[1] == 0.0625
@assert metaparam_vals[1] == 0.5

prob, metaparam_vals = optimize(["(let (a (flipd @0)
                            b (not (flipd @1)))
                            (and a b))"], 0.05, [0.5 for _ ∈ 1:3], 1)
@assert isapprox(prob[1], 0.275625)
@assert metaparam_vals[1] == 0.525

prob, metaparam_vals = optimize(["(let (a (flipd @0))
                            a)",
                            "(let (b (not (flipd @1)))
                            b)"], 0.05, [0.5 for _ ∈ 1:3], 1)
@assert isapprox(prob[1], 0.275625)
@assert metaparam_vals[1] == 0.525

prob, metaparam_vals = optimize(["(let (a (flipd @0))
                            a)",
                            "(let (b (not (flipd @1)))
                            b)"], 0.05, [0.5 for _ ∈ 1:3], 0)
@assert prob[1] == 0.25
@assert metaparam_vals[1] == 0.5

# Lots of steps
prob, metaparam_vals = optimize(["""
    (let (rain (flipd @0)
    temp (flipd @1)
    wetGrass (or rain temp))
    (given wetGrass rain)
    )
    """], 0.05, [0.5 for _ ∈ 1:3], 1000)
@assert prob[1] == 1.0
@assert metaparam_vals[1] == 1.0

prob, metaparam_vals = optimize(["(let (a (flipd @0)
                            b (not (flipd @0)))
                            (and a b))",
                            "(let (a (flipd @0))
                            a)",], 0.05, [0.5 for _ ∈ 1:3], 1000)
@assert isapprox(prob[1], 0.148148148)
@assert isapprox(metaparam_vals[1], 0.6666666666)

prob, metaparam_vals = optimize(["(let (a (flipd @0)
                            b (not (flipd @0)))
                            (and a b))",
                            "(let (a (flipd @0))
                            a)",], 0.05, [0.1 for _ ∈ 1:3], 1000)
@assert isapprox(prob[1], 0.148148148)
@assert isapprox(metaparam_vals[1], 0.6666666666)

prob, metaparam_vals = optimize(["(let (a (flipd @0)
                            b (not (flipd @0)))
                            (and a b))",
                            "(let (a (flipd @0))
                            a)"], 0.05, [0.9 for _ ∈ 1:3], 1000)
@assert isapprox(prob[1], 0.148148148)
@assert isapprox(metaparam_vals[1], 0.6666666666)

prob, metaparam_vals = optimize(["(== (geomd @0) 2)",
                             "(== (geomd @0) 3)",
                             "(== (geomd @0) 7)"], 0.5, [0.5 for _ ∈ 1:3], 1000)
@assert isapprox(prob[1], 0.000549755813888)
@assert isapprox(metaparam_vals[1], 0.2)

prob, metaparam_vals = optimize(["(let (a (geomd @0)
                                    b (geomd @1))
                                    (and (and (< a 10) (< b 10)) (== a b)))"], 0.01, [0.9 for _ ∈ 1:3], 1000)
@assert isapprox(prob[1], 1.0)
@assert isapprox(metaparam_vals[1], 1.0)

prob, metaparam_vals = optimize(["(let (a (geom 0.5)
                                    b (geomd @0))
                                    (and (and (< a 10) (< b 10)) (== a b)))"], 0.01, [0.5 for _ ∈ 1:3], 1000)
@assert isapprox(prob[1], 0.5)
@assert isapprox(metaparam_vals[1], 1.0)

prob, metaparam_vals = optimize(["(let (a (geom 0.5)
                                    b (geomd @0))
                                    (and (and (< a 10) (< b 10)) (== a b)))"], 0.01, [0.5 for _ ∈ 1:4], 1000)
@assert isapprox(prob[1], 0.5)
@assert isapprox(metaparam_vals[1], 1.0)

used_vars = diff_vars_used(parse_expr("@0"))
println(used_vars)

used_vars = diff_vars_used(parse_expr("(let (a (flipd @0)
                            b (not (flipd @1)))
                            (and a b))"))
println(used_vars)

used_vars = diff_vars_used(parse_expr("(flipd @0)"))
println(used_vars)
printstyled("passed all tests", color=:green)
