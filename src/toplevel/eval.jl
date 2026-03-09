export load_pluck_file, eval_forms, sample_output, run_toplevel, run_check

mutable struct ToplevelEvalState
    defs::Dict{Symbol, Definition}
    parser::ParseState
    silent::Bool
    check::Bool
    fail_count::Ref{Int}
    current_file::String
end

# Load and process definitions from a file
function load_pluck_file(filename::String; kwargs...)
    s = read(filename, String)
    run_toplevel(s; filename, kwargs...)
end

function run_toplevel(s::String; filename="<unknown>", defs=DEFINITIONS, silent=false, check=false, fail_count=Ref(0))
    tokens = tokenize(s)
    parser = ParseState(defs, [], dirname(abspath(filename)), s, filename)
    toplevel_state = ToplevelEvalState(defs, parser, silent, check, fail_count, relpath(abspath(filename)))

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
    load_pluck_file(expr.head.path; defs=toplevel_state.defs, silent=toplevel_state.silent, check=toplevel_state.check, fail_count=toplevel_state.fail_count)
end



function sample_output(expr::String; kwargs...)
    process_query("(PosteriorSamples $expr true 1)"; silent=true, kwargs...)[1]
end

# Add this helper function to process queries
function eval_toplevel(expr::PExpr{QueryOp}, toplevel_state)
    state = LazyKCState()
    body = deterministic_world(toplevel_compile(expr.head.query; state))
    t = time()
    results = eval_query(body, state)
    elapsed_ms = round((time() - t) * 1000; digits=2)
    if !toplevel_state.silent && !toplevel_state.check
        print_query_results_by_type(body, results, expr.head.name; elapsed_ms)
    end
    free_state(state)
    return results
end

function eval_toplevel(expr::PExpr{AssertQueryOp}, toplevel_state)
    state = LazyKCState()
    body = deterministic_world(toplevel_compile(expr.head.query; state))
    t = time()
    results = eval_query(body, state)
    elapsed_ms = round((time() - t) * 1000; digits=2)
    if !toplevel_state.silent && !toplevel_state.check
        print_query_results_by_type(body, results, expr.head.name; elapsed_ms)
    end
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
                    if toplevel_state.check
                        printstyled("FAIL: $(expr.head.name) $(elapsed_ms)ms ($(toplevel_state.current_file)): value $val_str expected prob $expected_prob, got $prob\n"; color=:red)
                        toplevel_state.fail_count[] += 1
                    else
                        printstyled("  FAIL: $(expr.head.name): value $val_str expected prob $expected_prob, got $prob\n"; color=:red)
                    end
                end
                break
            end
        end
        if !found
            all_passed = false
            if toplevel_state.check
                printstyled("FAIL: $(expr.head.name) $(elapsed_ms)ms ($(toplevel_state.current_file)): expected value $val_str not found in results\n"; color=:red)
                toplevel_state.fail_count[] += 1
            else
                printstyled("  FAIL: $(expr.head.name): expected value $val_str not found in results\n"; color=:red)
            end
        end
    end
    if all_passed
        if toplevel_state.check
            printstyled("PASS: $(expr.head.name) $(elapsed_ms)ms ($(toplevel_state.current_file))\n"; color=:green)
        else
            printstyled("  PASS: $(expr.head.name) ($(length(expected)) assertions)\n"; color=:green)
        end
    end
    return results
end
