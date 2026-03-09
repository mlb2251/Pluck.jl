struct IntDist
    bits::Vector{Any} # BDDs in KC paths; booleans in non-KC interpreters
end
Base.show(io::IO, x::IntDist) = print(io, "IntDist{$(length(x.bits))}")

function combine_int_dists(int_dist_results::Vector{Tuple{IntDist, BDD}}, mgr::RSDD.Manager)
    width = length(int_dist_results[1][1].bits)
    result = IntDist(fill(mgr.BDD_FALSE, width))
    overall_guard = mgr.BDD_FALSE
    for (int_dist, guard) in int_dist_results
        # should we compute an overall guard?
        overall_guard = overall_guard | guard
        @assert width == length(int_dist.bits)
        # For each bit, AND it with the guard then OR it into the result.
        for i = 1:width
            @inbounds bit = int_dist.bits[i]::BDD
            @inbounds new_bit = bit & guard
            @inbounds result.bits[i] = result.bits[i] | new_bit
        end
    end
    return (result, overall_guard)
end

"""
Equality of two int distributions is an AND over the equality (bdd_iff) of each bit.
"""
function int_dist_eq(x::IntDist, y::IntDist, mgr::RSDD.Manager)::BDD
    width = length(x.bits)
    @assert width == length(y.bits)
    result = mgr.BDD_TRUE
    for i = 1:width
        @inbounds xb = x.bits[i]::BDD
        @inbounds yb = y.bits[i]::BDD
        @inbounds result = bdd_and(result, bdd_iff(xb, yb))
        if bdd_is_false(result)
            return mgr.BDD_FALSE
        end
    end
    return result
end

"""
Get the BDD for a given integer value of an IntDist.
"""
function int_dist_at_int(val::IntDist, i::Int, mgr::RSDD.Manager)
    bits = digits(Bool, i, base = 2, pad = length(val.bits))
    # Start with TRUE BDD and conjoin constraints for each bit.
    bdd = mgr.BDD_TRUE

    for (bit_idx, bit_val) in enumerate(bits)
        bit_formula = val.bits[bit_idx]::BDD
        if bit_val
            bdd &= bit_formula
        else
            bdd &= ~bit_formula
        end
    end
    return bdd
end

function enumerate_int_dist(val::IntDist, bdd::BDD, mgr::RSDD.Manager)
    worlds = Tuple{Int, BDD}[]
    # Enumerate all 2^n possibilities (all setting of n bits)
    for i = 0:(2^length(val.bits)-1)
        world_bdd = int_dist_at_int(val, i, mgr) & bdd
        push!(worlds, (i, world_bdd))
    end
    return worlds
end
