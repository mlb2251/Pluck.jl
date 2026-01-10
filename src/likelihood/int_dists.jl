


struct IntDist
    bits::Vector{BDD}
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
            @inbounds new_bit = int_dist.bits[i] & guard
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
        @inbounds result = bdd_and(result, bdd_iff(x.bits[i], y.bits[i]))
        if bdd_is_false(result)
            return mgr.BDD_FALSE
        end
    end
    return result
end

"""
Greater-than comparison for two int distributions.
Returns a BDD representing when x > y.
Compares from MSB to LSB: x > y if at some bit position i,
x[i]=1 and y[i]=0, and all more significant bits are equal.
"""
function int_dist_gt(x::IntDist, y::IntDist, mgr::RSDD.Manager)::BDD
    width = length(x.bits)
    @assert width == length(y.bits)

    result = mgr.BDD_FALSE
    eq_so_far = mgr.BDD_TRUE

    for i = width:-1:1
        @inbounds x_gt_y_here = bdd_and(x.bits[i], bdd_negate(y.bits[i]))
        x_gt_y_here = bdd_and(x_gt_y_here, eq_so_far)

        result = bdd_or(result, x_gt_y_here)

        @inbounds bits_equal = bdd_iff(x.bits[i], y.bits[i])
        eq_so_far = bdd_and(eq_so_far, bits_equal)
    end

    return result
end

"""
Increment an IntDist by 1.
Uses binary addition: new_bit = bit XOR carry, new_carry = bit AND carry.
"""
function int_dist_inc(x::IntDist, mgr::RSDD.Manager)::IntDist
    width = length(x.bits)
    new_bits = Vector{BDD}(undef, width)
    carry = mgr.BDD_TRUE  # Adding 1, so initial carry is TRUE

    for i = 1:width
        @inbounds bit = x.bits[i]
        @inbounds new_bits[i] = bdd_xor(bit, carry)
        carry = bdd_and(bit, carry)
    end

    return IntDist(new_bits)
end

"""
Get the BDD for a given integer value of an IntDist
"""
function int_dist_at_int(val::IntDist, i::Int)
    bits = digits(Bool, i, base = 2, pad = length(val.bits))
    # Get BDD for this setting of the bits
    # Start with TRUE BDD
    bdd = state.manager.BDD_TRUE

    # For each bit, AND with either the bit's BDD or its negation based on our desired value
    for (bit_idx, bit_val) in enumerate(bits)
        bit_formula = val.bits[bit_idx]
        if bit_val
            bdd &= bit_formula
        else
            bdd &= ~bit_formula
        end
    end
    return bdd
end

function enumerate_int_dist(val::IntDist, bdd::BDD)
    worlds = Tuple{Int, BDD}[]
    # Enumerate all 2^n possibilities (all setting of n bits)
    for i = 0:(2^length(val.bits)-1)
        bdd = int_dist_at_int(val, i) & bdd
        push!(worlds, (i, bdd))
    end
    return worlds
end
