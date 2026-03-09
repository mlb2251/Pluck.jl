export load_pluck_file, eval_forms, sample_output, run_toplevel, run_check, diff_check_results

struct CheckResult
    name::String
    file::String
    passed::Bool
    time_ms::Float64
    num_recursive_calls::Int
    num_forward_calls::Int
    rsdd_time_ms::Float64
    bdd_size::Int
    gc_time_ms::Float64
    alloc_bytes::Int64
    num_allocs::Int64
end

mutable struct ToplevelEvalState
    defs::Dict{Symbol, Definition}
    parser::ParseState
    silent::Bool
    check::Bool
    fail_count::Ref{Int}
    current_file::String
    check_results::Vector{CheckResult}
end

# Load and process definitions from a file
function load_pluck_file(filename::String; kwargs...)
    s = read(filename, String)
    run_toplevel(s; filename, kwargs...)
end


function format_mb(bytes::Int64)
    return @sprintf("%.1f", bytes / 1024^2)
end

function format_check_row(r::CheckResult)
    status = r.passed ? "PASS" : "FAIL"
    time_str = string(r.time_ms)
    rsdd_time_str = string(r.rsdd_time_ms)
    rsdd_pct = r.time_ms > 0 ? "$(round(r.rsdd_time_ms / r.time_ms * 100; digits=1))%" : "N/A"
    gc_time_str = string(r.gc_time_ms)
    alloc_str = format_mb(r.alloc_bytes)
    return (name=r.name, status=status, time=time_str,
            rsdd_time=rsdd_time_str, rsdd_pct=rsdd_pct,
            bdd_size=string(r.bdd_size), gc_time=gc_time_str,
            alloc=alloc_str, num_allocs=string(r.num_allocs),
            num_recursive_calls=string(r.num_recursive_calls), num_forward_calls=string(r.num_forward_calls))
end

function print_check_row(r::CheckResult)
    row = format_check_row(r)
    color = r.passed ? :green : :red
    printstyled(row.status; color)
    print("  $(row.name)  $(row.time)  $(row.rsdd_time)($(row.rsdd_pct))  bdd=$(row.bdd_size)  gc=$(row.gc_time)  $(row.alloc)MB($(row.num_allocs))  fwd=$(row.num_forward_calls)  rec=$(row.num_recursive_calls)\n")
end

function print_check_table(results::Vector{CheckResult})
    rows = [format_check_row(r) for r in results]
    headers = ("", "name", "ms", "rsdd ms", "rsdd%", "bdd", "gc ms", "alloc MB", "nalloc", "fwd", "rec")
    w_status = 4
    w_name = max(length(headers[2]), maximum(length(r.name) for r in rows))
    w_time = max(length(headers[3]), maximum(length(r.time) for r in rows))
    w_rsdd = max(length(headers[4]), maximum(length(r.rsdd_time) for r in rows))
    w_rsdd_pct = max(length(headers[5]), maximum(length(r.rsdd_pct) for r in rows))
    w_bdd = max(length(headers[6]), maximum(length(r.bdd_size) for r in rows))
    w_gc = max(length(headers[7]), maximum(length(r.gc_time) for r in rows))
    w_alloc = max(length(headers[8]), maximum(length(r.alloc) for r in rows))
    w_nalloc = max(length(headers[9]), maximum(length(r.num_allocs) for r in rows))
    w_fwd = max(length(headers[10]), maximum(length(r.num_forward_calls) for r in rows))
    w_rec = max(length(headers[11]), maximum(length(r.num_recursive_calls) for r in rows))

    # Print header
    printstyled("$(rpad("", w_status))  $(rpad(headers[2], w_name))  $(lpad(headers[3], w_time))  $(lpad(headers[4], w_rsdd))  $(lpad(headers[5], w_rsdd_pct))  $(lpad(headers[6], w_bdd))  $(lpad(headers[7], w_gc))  $(lpad(headers[8], w_alloc))  $(lpad(headers[9], w_nalloc))  $(lpad(headers[10], w_fwd))  $(lpad(headers[11], w_rec))\n"; bold=true)

    for (r, row) in zip(results, rows)
        color = r.passed ? :green : :red
        printstyled(rpad(row.status, w_status); color)
        print("  $(rpad(row.name, w_name))  $(lpad(row.time, w_time))  $(lpad(row.rsdd_time, w_rsdd))  $(lpad(row.rsdd_pct, w_rsdd_pct))  $(lpad(row.bdd_size, w_bdd))  $(lpad(row.gc_time, w_gc))  $(lpad(row.alloc, w_alloc))  $(lpad(row.num_allocs, w_nalloc))  $(lpad(row.num_forward_calls, w_fwd))  $(lpad(row.num_recursive_calls, w_rec))\n")
    end
end

function check_result_to_dict(r::CheckResult)
    Dict(
        "name" => r.name,
        "file" => r.file,
        "passed" => r.passed,
        "time_ms" => r.time_ms,
        "rsdd_time_ms" => r.rsdd_time_ms,
        "bdd_size" => r.bdd_size,
        "gc_time_ms" => r.gc_time_ms,
        "alloc_bytes" => r.alloc_bytes,
        "num_allocs" => r.num_allocs,
        "num_recursive_calls" => r.num_recursive_calls,
        "num_forward_calls" => r.num_forward_calls,
    )
end

function save_check_results(results::Vector{CheckResult})
    base = joinpath(@__DIR__, "..", "..", "check-results")
    mkpath(base)

    data = JSON.json(Dict(
        "timestamp" => Dates.format(Dates.now(), "yyyy-mm-dd HH:MM:SS"),
        "results" => [check_result_to_dict(r) for r in results],
    ), 2)

    # Save as latest
    write(joinpath(base, "latest.json"), data)

    # Save timestamped copy
    ts_dir = relpath(timestamp_dir(; base=joinpath(base, "timestamped")))
    write(joinpath(ts_dir, "results.json"), data)

    printstyled("Saved to check-results/latest.json and $(ts_dir)/results.json\n"; color=:light_black)
end

function load_check_results(path::String)
    data = JSON.parsefile(path)
    Dict(r["name"] => r for r in data["results"]), data["timestamp"]
end

function fmt_delta(old, new; higher_is_worse=true, threshold=0.2)
    if old == 0 && new == 0
        return nothing
    end
    if old == 0
        return (str="new", color=:cyan)
    end
    ratio = (new - old) / abs(old)
    if abs(ratio) < threshold
        return nothing
    end
    pct = round(ratio * 100; digits=0)
    sign = pct > 0 ? "+" : ""
    color = (higher_is_worse == (pct > 0)) ? :red : :green
    return (str="$(sign)$(Int(pct))%", color=color)
end

function fmt_val(val, key)
    if key == "alloc_bytes"
        return format_mb(Int64(val))
    elseif key in ("rsdd_time_ms", "time_ms", "gc_time_ms")
        return @sprintf("%.2f", val)
    elseif key == "rsdd_pct"
        return @sprintf("%.1f%%", val)
    else
        return string(Int(val))
    end
end


function diff_check_results(baseline_path::String, latest_path::String="check-results/latest.json")
    base = joinpath(@__DIR__, "..", "..", "check-results")
    baseline_path = isfile(baseline_path) ? baseline_path : joinpath(base, baseline_path)
    latest_path = isfile(latest_path) ? latest_path : joinpath(base, latest_path)

    if !isfile(baseline_path)
        printstyled("Baseline not found: $baseline_path\n"; color=:red)
        return
    end
    if !isfile(latest_path)
        printstyled("Latest not found: $latest_path\n"; color=:red)
        return
    end

    old_results, old_ts = load_check_results(baseline_path)
    new_results, new_ts = load_check_results(latest_path)

    printstyled("Baseline: $old_ts\n"; color=:light_black)
    printstyled("Current:  $new_ts\n"; color=:light_black)
    println()

    # Use ordering from the new results file, then append any old-only names
    new_data = JSON.parsefile(latest_path)
    new_ordered = [r["name"] for r in new_data["results"]]
    old_only = [name for name in keys(old_results) if !haskey(new_results, name)]
    all_names = vcat(new_ordered, sort(old_only))

    # Status changes
    status_changes = []
    for name in all_names
        if !haskey(old_results, name)
            push!(status_changes, (name, "NEW", new_results[name]["passed"] ? :green : :red))
        elseif !haskey(new_results, name)
            push!(status_changes, (name, "REMOVED", :yellow))
        else
            old_pass = old_results[name]["passed"]
            new_pass = new_results[name]["passed"]
            if old_pass && !new_pass
                push!(status_changes, (name, "PASS → FAIL", :red))
            elseif !old_pass && new_pass
                push!(status_changes, (name, "FAIL → PASS", :green))
            end
        end
    end

    if !isempty(status_changes)
        printstyled("Status changes:\n"; bold=true)
        for (name, change, color) in status_changes
            printstyled("  $change"; color)
            println("  $name")
        end
        println()
    end

    # Performance table
    metrics = [
        ("time_ms", "ms", true),
        ("rsdd_time_ms", "rsdd ms", true),
        ("rsdd_pct", "rsdd%", true),
        ("bdd_size", "bdd", true),
        ("gc_time_ms", "gc ms", true),
        ("alloc_bytes", "alloc MB", true),
        ("num_allocs", "nalloc", true),
        ("num_forward_calls", "fwd", true),
        ("num_recursive_calls", "rec", true),
    ]

    # Build table rows
    table_rows = []
    any_changes = false
    for name in all_names
        has_old = haskey(old_results, name)
        has_new = haskey(new_results, name)
        cells = []
        row_has_change = false
        for (key, _, hiw) in metrics
            old_val = if !has_old
                nothing
            elseif key == "rsdd_pct"
                get(old_results[name], "time_ms", nothing) !== nothing && old_results[name]["time_ms"] > 0 && haskey(old_results[name], "rsdd_time_ms") ? old_results[name]["rsdd_time_ms"] / old_results[name]["time_ms"] * 100 : nothing
            else
                get(old_results[name], key, nothing)
            end
            new_val = if !has_new
                nothing
            elseif key == "rsdd_pct"
                get(new_results[name], "time_ms", nothing) !== nothing && new_results[name]["time_ms"] > 0 && haskey(new_results[name], "rsdd_time_ms") ? new_results[name]["rsdd_time_ms"] / new_results[name]["time_ms"] * 100 : nothing
            else
                get(new_results[name], key, nothing)
            end
            old_missing = old_val === nothing
            new_missing = new_val === nothing

            if old_missing && new_missing
                push!(cells, (old_str="-", new_str="-", color=:light_black, changed=false))
            elseif old_missing
                push!(cells, (old_str="-", new_str=fmt_val(new_val, key), color=:white, changed=false))
            elseif new_missing
                push!(cells, (old_str=fmt_val(old_val, key), new_str="-", color=:light_black, changed=false))
            else
                old_fmt = fmt_val(old_val, key)
                new_fmt = fmt_val(new_val, key)
                if old_fmt == new_fmt
                    push!(cells, (old_str=old_fmt, new_str=new_fmt, color=:normal, changed=false))
                else
                    d = fmt_delta(old_val, new_val; higher_is_worse=hiw)
                    color = d !== nothing ? d.color : (new_val < old_val ? (hiw ? :green : :red) : (hiw ? :red : :green))
                    push!(cells, (old_str=old_fmt, new_str=new_fmt, color=color, changed=true))
                    row_has_change = true
                end
            end
        end
        push!(table_rows, (name=name, cells=cells))
        if row_has_change
            any_changes = true
        end
    end

    if !isempty(table_rows)
        printstyled("Performance changes:\n"; bold=true)
        w_name = maximum(length(r.name) for r in table_rows)
        col_widths = [max(length(label), maximum(max(length(row.cells[i].old_str), length(row.cells[i].new_str)) for row in table_rows)) for (i, (_, label, _)) in enumerate(metrics)]
        total_width = 2 + w_name + sum(2 + w for w in col_widths)
        separator = "  " * "─"^(total_width - 2)

        # Print header
        printstyled("  $(rpad("", w_name))"; bold=true)
        for (i, (_, label, _)) in enumerate(metrics)
            printstyled("  $(lpad(label, col_widths[i]))"; bold=true)
        end
        println()
        printstyled(separator, "\n"; color=:light_black)

        for (ri, row) in enumerate(table_rows)
            # Old values line
            printstyled("  $(rpad(row.name, w_name))"; bold=true)
            for (i, cell) in enumerate(row.cells)
                printstyled("  $(lpad(cell.old_str, col_widths[i]))"; color=:light_black)
            end
            println()
            # New values line (colored)
            print("  $(rpad("", w_name))")
            for (i, cell) in enumerate(row.cells)
                printstyled("  $(lpad(cell.new_str, col_widths[i]))"; color=cell.color)
            end
            println()
            if ri < length(table_rows)
                printstyled(separator, "\n"; color=:light_black)
            end
        end
        println()
    end

    if isempty(status_changes) && !any_changes && !isempty(table_rows)
        printstyled("No significant changes.\n"; color=:green)
    end
end

function run_toplevel(s::String; filename="<unknown>", defs=DEFINITIONS, silent=false, check=false, fail_count=Ref(0), check_results=CheckResult[])
    tokens = tokenize(s)
    parser = ParseState(defs, [], dirname(abspath(filename)), s, filename)
    toplevel_state = ToplevelEvalState(defs, parser, silent, check, fail_count, relpath(abspath(filename)), check_results)

    while !isempty(tokens)
        expr, tokens = parse_toplevel(tokens, parser)
        eval_toplevel(expr, toplevel_state)
    end
end

function eval_toplevel(expr::PExpr{DefineOp}, toplevel_state)
    toplevel_state.defs[expr.head.name] = Definition(expr.head.name, expr.head.expr)
end

function eval_toplevel(expr::PExpr{DefineTypeOp}, toplevel_state)
    define_type!(expr.head.name, expr.head.constructors)
end

function eval_toplevel(expr::PExpr{IncludeOp}, toplevel_state)
    load_pluck_file(expr.head.path; defs=toplevel_state.defs, silent=toplevel_state.silent, check=toplevel_state.check, fail_count=toplevel_state.fail_count, check_results=toplevel_state.check_results)
end



function sample_output(expr::String; kwargs...)
    process_query("(PosteriorSamples $expr true 1)"; silent=true, kwargs...)[1]
end

# Add this helper function to process queries
function eval_toplevel(expr::PExpr{QueryOp}, toplevel_state)
    # In check mode, skip non-assert queries (e.g. sampling examples)
    if toplevel_state.check
        return nothing
    end
    state = LazyKCState()
    body = deterministic_world(toplevel_compile(expr.head.query; state))
    t = time()
    results = eval_query(body, state)
    elapsed_ms = round((time() - t) * 1000; digits=2)
    if !toplevel_state.silent
        print_query_results_by_type(body, results, expr.head.name; elapsed_ms)
    end
    free_state(state)
    return results
end

function eval_toplevel(expr::PExpr{AssertQueryOp}, toplevel_state)
    state = LazyKCState()
    body = deterministic_world(toplevel_compile(expr.head.query; state))

    # Warmup run (silent) to avoid measuring JIT compilation
    if toplevel_state.check
        print("$(expr.head.name)... ")
        clear_bdd_stats!()
        eval_query(body, state)
        free_state(state)
        state = LazyKCState()
        body = deterministic_world(toplevel_compile(expr.head.query; state))
    end

    clear_bdd_stats!()
    Base.GC.gc(true)
    gc_before = Base.gc_num()
    t = time()
    results = eval_query(body, state)
    elapsed_ms = round((time() - t) * 1000; digits=2)
    gc_after = Base.gc_num()
    bdd_stats = get_bdd_stats()
    rsdd_ms = round(bdd_stats.rsdd_time * 1000; digits=2)
    total_bdd_size = bdd_stats.total_bdd_size
    gc_time_ms = round((gc_after.total_time - gc_before.total_time) / 1e6; digits=2)
    alloc_bytes = Int64(gc_after.allocd - gc_before.allocd)
    num_allocs = Int64((gc_after.malloc + gc_after.realloc + gc_after.poolalloc + gc_after.bigalloc) -
                       (gc_before.malloc + gc_before.realloc + gc_before.poolalloc + gc_before.bigalloc))
    if !toplevel_state.silent && !toplevel_state.check
        print_query_results_by_type(body, results, expr.head.name; elapsed_ms)
    end
    stats = state.stats
    free_state(state)

    # Check results against expected values
    expected = expr.head.expected
    all_passed = true
    for (val_str, expected_prob) in expected
        found = false
        for (v, prob) in results
            if string(v) == val_str
                found = true
                if !isapprox(prob, expected_prob; rtol=1e-6)
                    all_passed = false
                    if !toplevel_state.check
                        printstyled("  FAIL: $(expr.head.name): value $val_str expected prob $expected_prob, got $prob\n"; color=:red)
                    end
                end
                break
            end
        end
        if !found
            all_passed = false
            if !toplevel_state.check
                printstyled("  FAIL: $(expr.head.name): expected value $val_str not found in results\n"; color=:red)
            end
        end
    end

    if toplevel_state.check
        if !all_passed
            toplevel_state.fail_count[] += 1
        end
        time_ms = stats.time !== nothing ? round(task_time(stats.time) * 1000; digits=2) : elapsed_ms
        cr = CheckResult(expr.head.name, toplevel_state.current_file, all_passed, time_ms, stats.num_recursive_calls, stats.num_forward_calls, rsdd_ms, total_bdd_size, gc_time_ms, alloc_bytes, num_allocs)
        push!(toplevel_state.check_results, cr)
    else
        if all_passed
            printstyled("  PASS: $(expr.head.name) ($(length(expected)) assertions)\n"; color=:green)
        end
    end
    return results
end
