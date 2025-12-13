export load_pluck_file, eval_forms, sample_output

mutable struct ToplevelEvalState
    defs::Dict{Symbol, Definition}
    parser::ParseState
    silent::Bool
end

# Load and process definitions from a file
function load_pluck_file(filename::String; defs=DEFINITIONS, silent=false)
    content = read(filename, String)
    tokens = tokenize(content)
    parser = ParseState(defs, [], dirname(abspath(filename)), content, filename)
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

function traced_compile_deterministic(expr::PExpr, env::Env, state::LazyKCState, strict_order_index::Int)
    res, _ = traced_compile_inner(expr, env, state.manager.BDD_TRUE, state, strict_order_index)
    @assert length(res) == 1 "Expected deterministic compilation to return a single value, got $(res)"
    @assert RSDD.bdd_is_true(res[1][2]) "Expected deterministic compilation to return a value with probability 1, got $(res[1][2])"
    return res[1][1]
end

# Add this helper function to process queries
function eval_toplevel(expr::PExpr{QueryOp}, toplevel_state)
    state = LazyKCState()
    body = traced_compile_deterministic(expr.head.query, EMPTY_ENV, state, 0)
    results = eval_query(body, state)
    if !toplevel_state.silent
        print_query_results_by_type(body, results, expr.head.name)
    end
    return results
end
