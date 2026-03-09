
function print_query_results(results, query_str; save = false)
    printstyled("$query_str:\n", color=:yellow, bold=true)

    if isempty(results)
        printstyled("  impossible constraint", bold=true)
        return
    end

    max_val_length = maximum(length(string(v)) for (v, _) in results)

    # Sort results by probability
    function _sortkey(val)
        if isa(val, Number)
            return (0, val)
        elseif isa(val, AbstractString)
            return (1, val)
        else
            return (2, string(val))
        end
    end

    sorted_results = sort(results, by = x -> (-x[2], _sortkey(x[1])))
    for (v, p) in sorted_results
        if p == 0
            continue
        end
        val_str = string(v)
        padding = " " ^ (max_val_length - length(val_str) + 2)  # +2 for minimum spacing
        printstyled("  $val_str", bold=true)
        printstyled(padding)
        printstyled("$p\n", color=:cyan)
    end


    if !isnothing(save)
        results_json = (query_str=query_str,
                        results=[(prob=p, val=v) for (v, p) in sorted_results])

        # check if file exists
        prev_results = []
        if isfile(save)
            prev_results = JSON.parse(read(save, String))
        end
        push!(prev_results, results_json)
        open(save, "w") do f
            JSON.print(f, prev_results)
        end
        println("http://localhost:8000/html/factored/factored.html?path=$save")
        println("Wrote $save")
    end
end


function print_query_results_by_type(val, results, query_str; save = nothing, elapsed_ms = nothing)
    time_str = isnothing(elapsed_ms) ? "" : " $(elapsed_ms)ms"
    if val.constructor == :Marginal
        print_query_results(results, "$query_str$time_str"; save)
    elseif val.constructor == :Posterior
        print_query_results(results, "$query_str$time_str"; save)
    elseif val.constructor == :PosteriorSamples
        printstyled("$query_str$time_str:\n", color=:yellow, bold=true)
        for (i, result) in enumerate(results)
            printstyled("  $result\n", bold=true)
        end
    elseif val.constructor == :AdaptiveRejection
        printstyled("$query_str$time_str:\n", color=:yellow, bold=true)
        printstyled("  $results\n", bold=true)
    else
        error("printing not supported for query type $(val.constructor)")
    end
    println()
end