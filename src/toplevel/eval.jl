export load_pluck_file, eval_forms, sample_output, run_toplevel

mutable struct ToplevelEvalState
    defs::Dict{Symbol, Definition}
    parser::ParseState
    silent::Bool
end

# Load and process definitions from a file
function load_pluck_file(filename::String; kwargs...)
    s = read(filename, String)
    run_toplevel(s; filename, kwargs...)
end

function run_toplevel(s::String; filename="<unknown>", defs=DEFINITIONS, silent=false)
    tokens = tokenize(s)
    parser = ParseState(defs, [], dirname(abspath(filename)), s, filename)
    toplevel_state = ToplevelEvalState(defs, parser, silent)

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
    load_pluck_file(expr.head.path; defs=toplevel_state.defs, silent=toplevel_state.silent)
end



function sample_output(expr::String; kwargs...)
    process_query("(PosteriorSamples $expr true 1)"; silent=true, kwargs...)[1]
end

# Add this helper function to process queries
function eval_toplevel(expr::PExpr{QueryOp}, toplevel_state)
    state = LazyKCState()
    body = deterministic_world(toplevel_compile(expr.head.query; state))
    results = eval_query(body, state)
    if !toplevel_state.silent
        print_query_results_by_type(body, results, expr.head.name)
    end
    free_state(state)
    return results
end
