
function deriv_tests()
    # Small number of steps
    prob, metaparam_vals = optimize(["(flip 0.5)"], 0.01, [], 1)
    @assert isapprox(prob[1], 0.5)

    prob, metaparam_vals = optimize(["(let (a (flip @0)
                                b (not (flip @0)))
                                (and a b))"], 0.05, [0.5 for _ ∈ 1:3], 1)
    @assert prob[1] == 0.25
    @assert metaparam_vals == [0.5, 0.5, 0.5]

    prob, metaparam_vals = optimize(["(let (a (flip @0)
                                b (not (flip @0)))
                                (and a b))",
                                "(let (a (flip @0)
                                b (not (flip @0)))
                                (and a b))",], 0.1, [0.5 for _ ∈ 1:3], 1)
    @assert prob[1] == 0.0625
    @assert metaparam_vals[1] == 0.5

    prob, metaparam_vals = optimize(["(let (a (flip @0)
                                b (not (flip @1)))
                                (and a b))"], 0.05, [0.5 for _ ∈ 1:3], 1)
    @assert isapprox(prob[1], 0.275625)
    @assert metaparam_vals[1] == 0.525

    prob, metaparam_vals = optimize(["(let (a (flip @0))
                                a)",
                                "(let (b (not (flip @1)))
                                b)"], 0.05, [0.5 for _ ∈ 1:3], 1)
    @assert isapprox(prob[1], 0.275625)
    @assert metaparam_vals[1] == 0.525

    prob, metaparam_vals = optimize(["(let (a (flip @0))
                                a)",
                                "(let (b (not (flip @1)))
                                b)"], 0.05, [0.5 for _ ∈ 1:3], 0)
    @assert prob[1] == 0.25
    @assert metaparam_vals[1] == 0.5

    # Lots of steps
    prob, metaparam_vals = optimize(["""
        (let (rain (flip @0)
        temp (flip @1)
        wetGrass (or rain temp))
        (given wetGrass rain)
        )
        """], 0.05, [0.5 for _ ∈ 1:3], 1000)
    @assert prob[1] == 1.0
    @assert metaparam_vals[1] == 1.0

    prob, metaparam_vals = optimize(["(let (a (flip @0)
                                b (not (flip @0)))
                                (and a b))",
                                "(let (a (flip @0))
                                a)",], 0.05, [0.5 for _ ∈ 1:3], 1000)
    @assert isapprox(prob[1], 0.148148148)
    @assert isapprox(metaparam_vals[1], 0.6666666666)

    prob, metaparam_vals = optimize(["(let (a (flip @0)
                                b (not (flip @0)))
                                (and a b))",
                                "(let (a (flip @0))
                                a)",], 0.05, [0.1 for _ ∈ 1:3], 1000)
    @assert isapprox(prob[1], 0.148148148)
    @assert isapprox(metaparam_vals[1], 0.6666666666)

    prob, metaparam_vals = optimize(["(let (a (flip @0)
                                b (not (flip @0)))
                                (and a b))",
                                "(let (a (flip @0))
                                a)"], 0.05, [0.9 for _ ∈ 1:3], 1000)
    @assert isapprox(prob[1], 0.148148148)
    @assert isapprox(metaparam_vals[1], 0.6666666666)

    prob, metaparam_vals = optimize(["(== (geom @0) 2)",
                                "(== (geom @0) 3)",
                                "(== (geom @0) 7)"], 0.5, [0.5 for _ ∈ 1:3], 1000)
    @assert isapprox(prob[1], 0.000549755813888)
    @assert isapprox(metaparam_vals[1], 0.2)

    prob, metaparam_vals = optimize(["(let (a (geom @0)
                                        b (geom @1))
                                        (and (and (< a 10) (< b 10)) (== a b)))"], 0.01, [0.9 for _ ∈ 1:3], 1000)
    @assert isapprox(prob[1], 1.0)
    @assert isapprox(metaparam_vals[1], 1.0)

    prob, metaparam_vals = optimize(["(let (a (geom 0.5)
                                        b (geom @0))
                                        (and (and (< a 10) (< b 10)) (== a b)))"], 0.01, [0.5 for _ ∈ 1:3], 1000)
    @assert isapprox(prob[1], 0.5)
    @assert isapprox(metaparam_vals[1], 1.0)

    prob, metaparam_vals = optimize(["(let (a (geom 0.5)
                                        b (geom @0))
                                        (and (and (< a 10) (< b 10)) (== a b)))"], 0.01, [0.5 for _ ∈ 1:4], 1000)
    @assert isapprox(prob[1], 0.5)
    @assert isapprox(metaparam_vals[1], 1.0)

    used_vars = native_ints_used(parse_expr("@0"))
    @assert used_vars == Set([0])

    used_vars = native_ints_used(parse_expr("(let (a (flip @0)
                                b (not (flip @1)))
                                (and a b))"))
    @assert used_vars == Set([0, 1])

    used_vars = native_ints_used(parse_expr("(flip @0)"))
    @assert used_vars == Set([0])
    printstyled("passed all tests", color=:green)
end