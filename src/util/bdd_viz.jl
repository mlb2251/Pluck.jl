mutable struct BDDJSONLogger
    root::Union{Dict, Nothing}
    children::Vector{Dict}
    state::LazyKCState
end
function JSON.lower(viz::BDDJSONLogger)
    @show viz_size(viz.root)
    return Dict(
        "root" => viz.root,
    )
end

function viz_size(node::Dict)
    return 1 + sum(viz_size(child) for child in node["children"]; init = 0)
end

BDDJSONLogger(state::LazyKCState) = BDDJSONLogger(nothing, [], state)

function record_forward!(viz::BDDJSONLogger, expr, env, path_condition, strict_order_index)
    frame = Dict(
        "type" => "forward",

        # args to the call
        "expr" => viz_lower(expr, viz),
        "env" => viz_lower(env, viz; expr = expr),
        "path_condition" => viz_lower(path_condition, viz),
        "strict_order_index" => strict_order_index,

        # extra info
        "prestate" => viz_lower(viz.state, viz),
        "poststate" => nothing,
        "expr_type" => string(typeof(expr)),
        "shortname" => shortname(expr), "children" => [],
    )
    push!(viz.children, frame)
end

function record_result!(viz::BDDJSONLogger, worlds, used_information)
    finished_frame = pop!(viz.children)
    # @show viz_size(finished_frame)
    # add frame as child of parent in every case except when finishing the root frame
    if !isempty(viz.children)
        parent_frame = viz.children[end]
        push!(parent_frame["children"], finished_frame)
    else
        viz.root = finished_frame
    end
    finished_frame["result"] = Dict(
        "worlds" => [
            viz_lower_world(v, guard, viz)
            for (v, guard) in worlds],
        "used_information" => viz_lower(used_information, viz),
    )
    finished_frame["poststate"] = viz_lower(viz.state, viz)
end

function viz_lower(e::PExpr, ::BDDJSONLogger)
    return string(e)
end
function viz_lower(s::String, ::BDDJSONLogger)
    return s
end

function viz_lower(env::Vector{Any}, viz::BDDJSONLogger; expr = nothing, shift = 0)
    return [isnothing(expr) || var_is_free(expr, i + shift) ? viz_lower(v, viz) : "unused" for (i, v) in enumerate(env)]
end

function viz_lower(bdd::BDD, viz::BDDJSONLogger)
    return Dict(
        "size" => RSDD.bdd_size(bdd),
        "bdd_is_true" => Bool(RSDD.bdd_is_true(bdd)),
        "bdd_is_false" => Bool(RSDD.bdd_is_false(bdd)),
        "weight" => RSDD.bdd_wmc(bdd, viz.state.weights),
        "str" => string(bdd),
        "bdd_json" => make_bdd_json(viz.state, bdd),
    )
end

function viz_lower(val::Value, viz::BDDJSONLogger)
    return Dict(
        "type" => "Value",
        "constructor" => val.constructor,
        "args" => [viz_lower(arg, viz) for arg in val.args],
    )
end

# value + guard = world
function viz_lower_world(value, guard::BDD, viz::BDDJSONLogger)
    return Dict(
        "value" => viz_lower(value, viz),
        "guard" => viz_lower(guard, viz),
    )
end

function viz_lower(thunk::LazyKCThunk, viz::BDDJSONLogger)
    return Dict(
        "type" => "Thunk",
        "expr" => viz_lower(thunk.expr, viz),
        "env" => viz_lower(thunk.env, viz; expr = thunk.expr),
        "callstack" => copy(thunk.callstack),
        "strict_order_index" => thunk.strict_order_index,
    )
end

function viz_lower(union::LazyKCThunkUnion, viz::BDDJSONLogger)
    return Dict(
        "type" => "ThunkUnion",
        "worlds" => [
            viz_lower_world(thunk, guard, viz)
            for (thunk, guard) in union.thunks],
    )
end

function viz_lower(closure::Closure, viz::BDDJSONLogger)
    if !isempty(closure.env) && closure.env[1] === closure
        env = vcat(["[recursive ref to this closure]"], closure.env[2:end])
    else
        env = closure.env
    end
    return Dict(
        "type" => "Closure",
        "expr" => viz_lower(closure.expr, viz),
        "env" => viz_lower(env, viz; expr = closure.expr, shift = 1),
    )
end

function viz_lower(float::Float64, viz::BDDJSONLogger)
    return string(float)
end

function viz_lower(state::LazyKCState, viz::BDDJSONLogger)
    return Dict(
        "callstack" => copy(state.callstack),
        "num_forward_calls" => state.stats.num_forward_calls,
        "depth" => state.depth,
    )
end


function make_bdd_json(state::BDDStrictEvalState, bdd)
    json = JSON.parse(bdd_json(bdd))

    biggest_var = RSDD.bdd_new_var(state.manager, true)
    biggest_var_index = Int(RSDD.bdd_topvar(biggest_var))
    callstack_of_label = Dict{Int, Vector{Symbol}}(i => [Symbol("$(i)")] for i = 1:biggest_var_index)

    json["callstack_of_label"] = callstack_of_label
    json["callsite_of_label"] = Dict{Int, Any}()
    return json
end

function make_bdd_json(state, bdd)
    json = JSON.parse(bdd_json(bdd))

    callstack_of_label = Dict{Int, Vector{Symbol}}()

    if state.cfg.use_strict_order
        nodes = deepcopy(json["nodes"])
        for (new_label, (old_label, callstack)) in enumerate(zip(state.sorted_var_labels, state.sorted_callstacks))
            # Wherever the old_label appears in json["nodes"], in nodes replace it with the new label.
            # Recall that nodes is a list of lists, and the label is the first element of the inner list.
            for (i, node) in enumerate(json["nodes"])
                if node[1] == old_label
                    nodes[i][1] = new_label
                end
            end
            callstack, p = callstack
            callstack_of_label[new_label] = [[Symbol(j) for j in callstack]..., Symbol(p)] #[[Symbol(i) for i in callstack[1]]..., Symbol("$(callstack[2])")]
        end
        json["nodes"] = nodes
    else
        for (k, v) in state.var_of_callstack
            callstack_of_label[Int(RSDD.bdd_topvar(v))] = [[Symbol(i) for i in k[1]]..., Symbol("$(k[2])")]
        end
    end

    json["callstack_of_label"] = callstack_of_label
    # attach callsite metadata if available, remapping labels under strict order
    json["callsite_of_label"] = Dict{Int, Any}()
    if hasproperty(state, :callsite_of_var) && !isempty(state.callsite_of_var)
        if state.cfg.use_strict_order && !isempty(state.sorted_var_labels)
            for (new_label, old_label) in enumerate(state.sorted_var_labels)
                if haskey(state.callsite_of_var, old_label)
                    json["callsite_of_label"][new_label] = state.callsite_of_var[old_label]
                end
            end
        else
            for (label, meta) in state.callsite_of_var
                json["callsite_of_label"][label] = meta
            end
        end

        # include sources for any loc/span we emit
        files = Set{String}()
        for meta in values(state.callsite_of_var)
            # stacktrace locs
            stack = get(meta, "stacktrace", [])
            for frame in stack
                loc = get(frame, "loc", nothing)
                loc === nothing || push!(files, loc["file"])
            end
            # call frames and strict call frames locs/spans
            for frames_key in ("call_frames", "strict_call_frames")
                frames = get(meta, frames_key, [])
                for frame in frames
                    loc = get(frame, "loc", nothing)
                    loc === nothing || push!(files, loc["file"])
                    span = get(frame, "span", nothing)
                    if span !== nothing && haskey(span, "file")
                        push!(files, span["file"])
                    end
                    cspan = get(frame, "called_from_span", nothing)
                    if cspan !== nothing && haskey(cspan, "file")
                        push!(files, cspan["file"])
                    end
                end
            end
            # origin
            origin_loc = get(meta, "origin_loc", nothing)
            origin_loc === nothing || push!(files, origin_loc["file"])
            origin_span = get(meta, "origin_span", nothing)
            if origin_span !== nothing && haskey(origin_span, "file")
                push!(files, origin_span["file"])
            end
        end
        if !isempty(files)
            sources = Dict{String, String}()
            for f in files
                try
                    sources[f] = read(f, String)
                catch
                    # ignore unreadable
                end
            end
            json["sources"] = sources
        end
    end
    return json
end

function record_bdd(state, bdd)
    json = make_bdd_json(state, bdd)
    out = joinpath(timestamp_dir(; base = "out/bdds/"), "bdd.json")
    write_out(json, out)
    # println(webaddress("html/bdd.html", out, false))
end
