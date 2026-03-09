export load_pluck_file, eval_forms, sample_output, run_toplevel, run_check

struct CheckResult
    name::String
    file::String
    passed::Bool
    time_ms::Float64
    num_recursive_calls::Int
    num_forward_calls::Int
    task_time_ms::Float64
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
    return string(round(bytes / 1024^2; digits=1))
end

function format_check_row(r::CheckResult)
    status = r.passed ? "PASS" : "FAIL"
    name_with_file = "$(r.name) ($(r.file))"
    time_str = string(r.time_ms)
    task_time_str = string(r.task_time_ms)
    rsdd_time_str = string(r.rsdd_time_ms)
    rsdd_pct = r.task_time_ms > 0 ? "$(round(r.rsdd_time_ms / r.task_time_ms * 100; digits=1))%" : "N/A"
    gc_time_str = string(r.gc_time_ms)
    alloc_str = format_mb(r.alloc_bytes)
    return (name=name_with_file, status=status, time=time_str, task_time=task_time_str,
            rsdd_time=rsdd_time_str, rsdd_pct=rsdd_pct,
            bdd_size=string(r.bdd_size), gc_time=gc_time_str,
            alloc=alloc_str, num_allocs=string(r.num_allocs),
            num_recursive_calls=string(r.num_recursive_calls), num_forward_calls=string(r.num_forward_calls))
end

function print_check_row(r::CheckResult)
    row = format_check_row(r)
    color = r.passed ? :green : :red
    printstyled(row.status; color)
    print("  $(row.name)  $(row.time)  $(row.task_time)  $(row.rsdd_time)($(row.rsdd_pct))  bdd=$(row.bdd_size)  gc=$(row.gc_time)  $(row.alloc)MB($(row.num_allocs))  fwd=$(row.num_forward_calls)  rec=$(row.num_recursive_calls)\n")
end

function print_check_table(results::Vector{CheckResult})
    rows = [format_check_row(r) for r in results]
    headers = ("", "name", "ms", "task ms", "rsdd ms", "rsdd%", "bdd", "gc ms", "alloc MB", "nalloc", "fwd", "rec")
    w_status = 4
    w_name = max(length(headers[2]), maximum(length(r.name) for r in rows))
    w_time = max(length(headers[3]), maximum(length(r.time) for r in rows))
    w_task = max(length(headers[4]), maximum(length(r.task_time) for r in rows))
    w_rsdd = max(length(headers[5]), maximum(length(r.rsdd_time) for r in rows))
    w_rsdd_pct = max(length(headers[6]), maximum(length(r.rsdd_pct) for r in rows))
    w_bdd = max(length(headers[7]), maximum(length(r.bdd_size) for r in rows))
    w_gc = max(length(headers[8]), maximum(length(r.gc_time) for r in rows))
    w_alloc = max(length(headers[9]), maximum(length(r.alloc) for r in rows))
    w_nalloc = max(length(headers[10]), maximum(length(r.num_allocs) for r in rows))
    w_fwd = max(length(headers[11]), maximum(length(r.num_forward_calls) for r in rows))
    w_rec = max(length(headers[12]), maximum(length(r.num_recursive_calls) for r in rows))

    # Print header
    printstyled("$(rpad("", w_status))  $(rpad(headers[2], w_name))  $(lpad(headers[3], w_time))  $(lpad(headers[4], w_task))  $(lpad(headers[5], w_rsdd))  $(lpad(headers[6], w_rsdd_pct))  $(lpad(headers[7], w_bdd))  $(lpad(headers[8], w_gc))  $(lpad(headers[9], w_alloc))  $(lpad(headers[10], w_nalloc))  $(lpad(headers[11], w_fwd))  $(lpad(headers[12], w_rec))\n"; bold=true)

    for (r, row) in zip(results, rows)
        color = r.passed ? :green : :red
        printstyled(rpad(row.status, w_status); color)
        print("  $(rpad(row.name, w_name))  $(lpad(row.time, w_time))  $(lpad(row.task_time, w_task))  $(lpad(row.rsdd_time, w_rsdd))  $(lpad(row.rsdd_pct, w_rsdd_pct))  $(lpad(row.bdd_size, w_bdd))  $(lpad(row.gc_time, w_gc))  $(lpad(row.alloc, w_alloc))  $(lpad(row.num_allocs, w_nalloc))  $(lpad(row.num_forward_calls, w_fwd))  $(lpad(row.num_recursive_calls, w_rec))\n")
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
        tt = stats.time !== nothing ? round(task_time(stats.time) * 1000; digits=2) : elapsed_ms
        cr = CheckResult(expr.head.name, toplevel_state.current_file, all_passed, elapsed_ms, stats.num_recursive_calls, stats.num_forward_calls, tt, rsdd_ms, total_bdd_size, gc_time_ms, alloc_bytes, num_allocs)
        push!(toplevel_state.check_results, cr)
        print_check_row(cr)
    else
        if all_passed
            printstyled("  PASS: $(expr.head.name) ($(length(expected)) assertions)\n"; color=:green)
        end
    end
    return results
end
