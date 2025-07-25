export logaddexp, timestamp_dir, set_server_addr, set_server_port, get_server_addr, get_server_port, get_server_base_url, write_out, normalize, get_true_result, timestamp_path, compile_deterministic

using Dates
using Printf

function logaddexp(x::Float64, y::Float64)::Float64
    if x == -Inf
        return y
    elseif y == -Inf
        return x
    else
        # Numerically stable implementation
        res = max(x, y) + log1p(exp(-abs(x - y)))
        # If res is very close to 0, return 0
        return (res > 0.0 && isapprox(res, 0.0; atol = eps(1.0))) ? 0.0 : res
    end
end

function compile(expr::String, cfg::T) where T
    expr = parse_expr(expr)
    compile(expr, cfg)
end
compile(expr::String) = compile(expr, LazyKCConfig())
compile(expr; kwargs...) = compile(expr, LazyKCConfig(; kwargs...))

function compile_deterministic(expr)
    worlds = compile(expr; full_dist=true)
    @assert length(worlds) == 1 "Deterministic compilation returned 0 or 2+ worlds"
    return worlds[1][1]
end

function normalize(results)
    isempty(results) && return results
    probabilities = [res[2] for res in results]
    total = sum(probabilities)
    return [(res[1], res[2] / total) for res in results]
end

function normalize_dual(results)
    isempty(results) && return results
    dual_numbers = [res[2] for res in results]
    probabilities = [d[1] for d in dual_numbers]
    derivs = [d[2] for d in dual_numbers]
    total = sum(probabilities)
    total_deriv = sum(derivs)

    return [(res[1], (res[2][1] / total, (total*res[2][2] - res[2][1]*total_deriv)/(total^2))) for res in results]
end

function get_true_result(results, default=nothing)
    res = nothing
    for (val, x) in results
        if val == Pluck.TRUE_VALUE || (val isa Bool && val == true)
            @assert isnothing(res) "Multiple true results found"
            res = x
        end
    end
    return isnothing(res) ? default : res
end

function timestamp_path(file; base = "out/res")
    dir = timestamp_dir(;base)
    joinpath(dir, file)
end

function timestamp_dir(;base = "out/res")
    date = Dates.format(Dates.now(), "yyyy-mm-dd")
    time = Dates.format(Dates.now(), "HH-MM-SS")
    i = 0
    dir = nothing
    while isnothing(dir) || isdir(dir)
        dir = joinpath(base, date, time * "-$(lpad(i, 3, '0'))")
        i += 1
    end
    mkpath(dir)
    return dir
end

ADDR::String = "http://localhost"
PORT::Int = 8000
function set_server_addr(addr::String)
    global ADDR
    ADDR = addr
end

function set_server_port(port::Int)
    global PORT
    PORT = port
end

function get_server_addr()
    ADDR
end

function get_server_port()
    PORT
end

function get_server_base_url()
    return "$ADDR:$PORT"
end

function write_out(json_data, path; verbose = true)
    if !endswith(path, ".json")
        @warn "Path $path does not end with .json, appending it"
        path *= ".json"
    end
    mkpath(dirname(path))
    open(path, "w") do f
        JSON.print(f, json_data)
    end
    kb = round(Int, filesize(path) / 1000)
    verbose && println("wrote $path [$kb KB]")
end

function log_dual(param)
    primal, deriv = param  
    log_primal = log(primal)
    log_deriv = x -> x / primal
    return (log_primal, log_deriv.(deriv))
end

function exp_dual(param)
    primal, deriv = param
    exp_deriv = x -> x * exp(primal)
    return (exp(primal), exp_deriv.(deriv))
end

function sum_dual(params::Vector)
    primal_sum = sum(p for (p, _) in params)
    dual_sum = sum(d for (_, d) in params)
    return (primal_sum, dual_sum)
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

function format_prob(p)
    # Helper function to format probability without scientific notation
    str = @sprintf("%.10f", p)
    str = replace(str, r"0+$" => "")  # Remove trailing zeros
    str = replace(str, r"\.$" => ".0") # Ensure decimal point
    @assert !occursin("e", str)
    return str
end
