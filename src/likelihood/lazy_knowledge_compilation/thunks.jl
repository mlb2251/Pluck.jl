struct LazyKCThunk
    expr::PExpr
    env::Env
    cache::Vector{GuardedWorlds}
    callstack::Callstack
    name::Symbol
    strict_order_index::Int

    function LazyKCThunk(expr::PExpr, env::Env, callstack::Callstack, name::Symbol, strict_order_index::Int, state)
        
        if expr isa Var && env[expr.idx] isa LazyKCThunk
            return env[expr.idx]
        end

        key = (expr, env, callstack)
        if state.cfg.use_thunk_cache && state !== nothing && haskey(state.thunk_cache, key)
            return state.thunk_cache[key]
        else
            # cache miss or not using cache
            cache = [([], state.manager.BDD_FALSE)] # esp for singleton cache case
            thunk = new(expr, env, cache, copy(callstack), name, strict_order_index)
            if state.cfg.use_thunk_cache && state !== nothing
                state.thunk_cache[(expr, copy(env), copy(callstack))] = thunk
            end
            return thunk
        end
    end
end

function Base.show(io::IO, x::LazyKCThunk)
    print(io, "LazyKCThunk(", x.expr, ")")
end

struct LazyKCThunkUnion
    thunks::Vector{Tuple{LazyKCThunk,BDD}}
    function LazyKCThunkUnion(worlds::Vector{Tuple{T,BDD}}, state) where T

        # collapse identical worlds
        uniq_worlds = Vector{LazyKCThunk}()
        uniq_guards = Vector{BDD}()
        uniq_world_indices = Dict{LazyKCThunk,Int}()

        for (world, outer_bdd) in worlds

            if world isa LazyKCThunkUnion
                # remove a layer of indirection
                for (world, bdd) in world.thunks
                    if haskey(uniq_world_indices, world)
                        uniq_guards[uniq_world_indices[world]] = uniq_guards[uniq_world_indices[world]] | (outer_bdd & bdd)
                    else
                        push!(uniq_worlds, world)
                        push!(uniq_guards, outer_bdd & bdd)
                        uniq_world_indices[world] = length(uniq_worlds)
                    end
                end

            elseif haskey(uniq_world_indices, world)
                uniq_guards[uniq_world_indices[world]] = uniq_guards[uniq_world_indices[world]] | outer_bdd
            else
                push!(uniq_worlds, world)
                push!(uniq_guards, outer_bdd)
                uniq_world_indices[world] = length(uniq_worlds)
            end
        end

        worlds = Tuple{LazyKCThunk,BDD}[(world, bdd) for (world, bdd) in zip(uniq_worlds, uniq_guards)]
        return new(worlds)
    end
end

function Base.show(io::IO, x::LazyKCThunkUnion)
    print(io, "LazyKCThunkUnion{", length(x.thunks), "}(")
    for (i, (world, bdd)) in enumerate(x.thunks)
        print(io, world)
        if i < length(x.thunks)
            print(io, " | ")
        end
    end
    print(io, ")")
end

function evaluate(thunk::LazyKCThunkUnion, path_condition::BDD, state::LazyKCState)
    # evaluate() has the same type as the continuation bind takes, and needs to do all the same things.
    bind_monad(evaluate, (thunk.thunks, state.manager.BDD_TRUE), path_condition, state)
end

function evaluate_no_cache(thunk::LazyKCThunk, path_condition::BDD, state::LazyKCState)
    old_callstack = state.callstack
    state.callstack = thunk.callstack
    result = traced_compile_inner(thunk.expr, thunk.env, path_condition, state, thunk.strict_order_index)
    state.callstack = old_callstack
    return result
end

function evaluate(thunk::LazyKCThunk, path_condition::BDD, state::LazyKCState)
    # non-singleton cache case
    if !state.cfg.singleton_cache
        for (results, guard) in thunk.cache
            if bdd_is_true(bdd_implies(path_condition, guard))
                return results, guard
            end
        end
        res = evaluate_no_cache(thunk, path_condition, state)
        push!(thunk.cache, res)
        return res
    end

    cached_worlds, cache_guard = thunk.cache[1]

    # We want to run the code: (if cache_guard then cached_worlds else evaluated_worlds)
    # Using the path condition: path_condition | cache_guard
    # OR-ing in the cache guard ensures that we don't lose any of the information we had previously stored in the cache.

    hit_cache_worlds = if_then_else_monad(true, false, cache_guard, state)
    path_condition |= cache_guard
    thunk.cache[1] = bind_monad(hit_cache_worlds, path_condition, state) do hit_cache, path_condition, state
        hit_cache ? (cached_worlds, state.manager.BDD_TRUE) : evaluate_no_cache(thunk, path_condition, state)
    end

    """
    The above part of the above code that generates new_cache_worlds can alternatively be written
    out without bind_monad like so:

    inner_path_condition = path_condition & !cache_guard
    result, used_information = evaluate_no_cache(thunk, inner_path_condition, state)
    cached_worlds = condition_worlds(cached_worlds, cache_guard)
    added_worlds = condition_worlds(result, !cache_guard)
    new_worlds = join_worlds([cached_worlds, added_worlds], state)
    new_cache_guard = bdd_implies(!cache_guard, used_information)
    """

    return thunk.cache[1]
end

"""
Process thunks into fully resolved values.
"""
function infer_full_distribution(initial_results, state)
    # Queue of (value, bdd) pairs to process
    queue = initial_results
    # Final set of fully resolved (value, bdd) pairs
    resolved = Vector{Tuple{Value,BDD}}()

    while !isempty(queue)
        (current_val, current_bdd) = pop!(queue)
        # Find first unresolved thunk in the value tree
        thunk_path = find_first_thunk(current_val)

        if isnothing(thunk_path)
            # No more thunks - this value is fully resolved
            push!(resolved, (current_val, current_bdd))
            continue
        end

        # Get the thunk at the path
        thunk = get_value_at_path(current_val, thunk_path)

        # Evaluate the thunk
        sub_results, _ = evaluate(thunk, current_bdd, state)

        # For each possible result of the thunk evaluation
        for (sub_val, sub_bdd) in sub_results
            # Create a copy of the value with this thunk replaced
            new_val = replace_at_path(current_val, thunk_path, sub_val)
            # Add to queue with conjunction of bdds
            push!(queue, (new_val, current_bdd & sub_bdd))
        end
    end

    return reverse(resolved)
end

# Helper function to find first thunk in a value tree using DFS
function find_first_thunk(val::Value, path::Vector{Int}=Int[])
    # Check direct arguments first
    for (i, arg) in enumerate(val.args)
        if arg isa LazyKCThunk || arg isa LazyKCThunkUnion
            push!(path, i)
            return path
        elseif arg isa Value
            # Recursively check this argument
            sub_path = find_first_thunk(arg, copy(path))
            if !isnothing(sub_path)
                pushfirst!(sub_path, i)
                return sub_path
            end
        end
    end
    return nothing
end

# Helper to get value at a path in the value tree
function get_value_at_path(val::Value, path::Vector{Int})
    current = val
    for i in path[1:end-1]
        current = current.args[i]
    end
    return current.args[path[end]]
end

# Helper to create a copy of a value with replacement at path
function replace_at_path(val::Value, path::Vector{Int}, new_val)
    if isempty(path)
        return new_val
    end

    # Create copy of value
    new_args = copy(val.args)

    if length(path) == 1
        # Direct replacement
        new_args[path[1]] = new_val
    else
        # Recursive replacement
        new_args[path[1]] = replace_at_path(val.args[path[1]], path[2:end], new_val)
    end

    return Value(val.constructor, new_args)
end