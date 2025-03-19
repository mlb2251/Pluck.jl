using Printf
function format_prob(p)
    # Helper function to format probability without scientific notation
    str = @sprintf("%.10f", p)
    str = replace(str, r"0+$" => "")  # Remove trailing zeros
    str = replace(str, r"\.$" => ".0") # Ensure decimal point
    @assert !occursin("e", str)
    return str
end

function discrete(options, probabilities)
    # Filter out options with 0 probability
    nonzero_indices = findall(x -> x > 0, probabilities)
    options = options[nonzero_indices]
    probabilities = probabilities[nonzero_indices]
    n = length(options)

    @assert length(probabilities) == n
    @assert abs(sum(probabilities) - 1.0) < 1e-5 "Probabilities must sum to 1"

    # Base cases
    n == 1 && return "$(options[1])"
    n == 2 && return "(if (flip $(format_prob(probabilities[2]))) $(options[2]) $(options[1]))"

    # Compute number of bits needed to represent integers up to length(options)
    num_bits = ceil(Int, log2(n))

    # Pad probabilities to power of 2
    padded_probs = vcat(probabilities, zeros(2^num_bits - n))

    # Build expression from innermost to outermost
    function build_expr(bit_idx, start_idx, end_idx)
        if bit_idx == 0
            # Return the appropriate option if in range, otherwise first option
            return start_idx <= n ? "$(options[start_idx])" : "$(options[1])"
        end

        mid = Int((start_idx + end_idx + 1) ÷ 2)
        denom = sum(padded_probs[start_idx:end_idx])

        if denom == 0
            return build_expr(bit_idx - 1, start_idx, mid - 1)
        end

        p = sum(padded_probs[mid:end_idx]) / denom

        left = build_expr(bit_idx - 1, mid, end_idx)
        right = build_expr(bit_idx - 1, start_idx, mid - 1)

        return "(if (flip $(format_prob(p))) $left $right)"
    end

    return build_expr(num_bits, 1, 2^num_bits)
end