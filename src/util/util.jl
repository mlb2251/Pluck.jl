export logaddexp, timestamp_dir, set_server_addr, set_server_port, get_server_addr, get_server_port, get_server_base_url, write_out, normalize, get_true_result

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

function normalize(results)
    probabilities = [res[2] for res in results]
    total = sum(probabilities)
    return [(res[1], res[2] / total) for res in results]
end

function get_true_result(results, default)
    res = nothing
    for (val, x) in results
        if val == Pluck.TRUE_VALUE || val == true
            @assert isnothing(res) "Multiple true results found"
            res = x
        end
    end
    return isnothing(res) ? default : res
end

function timestamp_dir(; base = "out/results")
    dir = nothing
    while isnothing(dir) || isdir(dir)
        date = Dates.format(Dates.now(), "yyyy-mm-dd")
        time = Dates.format(Dates.now(), "HH-MM-SS")
        dir = joinpath(base, date, time)
    end
    mkpath(dir)
    dir
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