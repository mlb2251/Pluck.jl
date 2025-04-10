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
        if state !== nothing && state.cfg.use_thunk_cache && haskey(state.thunk_cache, key)
            return state.thunk_cache[key]
        else
            thunk = new(expr, env, [], copy(callstack), name, strict_order_index)
            if state !== nothing && state.cfg.use_thunk_cache
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
    thunks::Vector{Tuple{LazyKCThunk, BDD}}
    function LazyKCThunkUnion(worlds::Vector{Tuple{T, BDD}}, state) where T

        # collapse identical worlds
        uniq_worlds = Vector{LazyKCThunk}()
        uniq_guards = Vector{BDD}()
        uniq_world_indices = Dict{LazyKCThunk, Int}()

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

        worlds = Tuple{LazyKCThunk, BDD}[(world, bdd) for (world, bdd) in zip(uniq_worlds, uniq_guards)]
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

function evaluate(thunk::LazyKCThunkUnion, available_information::BDD, state::LazyKCState)
    intermediate_results = []
    for (result, guard) in thunk.thunks
        new_guard = available_information & guard
        push!(intermediate_results, (evaluate(result, new_guard, state), guard))
    end

    return join_monad(intermediate_results, state.manager.BDD_TRUE, available_information, state)
end

function evaluate(thunk::LazyKCThunk, available_information::BDD, state::LazyKCState)
    if !state.cfg.disable_used_information && bdd_is_false(available_information)
        return [], state.manager.BDD_FALSE
    end

    # Check the cache
    for (results, bdd) in thunk.cache
        if bdd_is_true(bdd_implies(available_information, bdd))
            return (results, bdd)
        end
    end

    # Otherwise we have to evaluate the thunk. Set the callstack to the thunk's callstack.
    old_callstack = state.callstack
    state.callstack = thunk.callstack
    # We have replaced available_information with BDD_TRUE.
    if state.cfg.singleton_cache && length(thunk.cache) == 1
        (worlds, bdd) = thunk.cache[1]
        result, used_information = traced_compile_inner(thunk.expr, thunk.env, available_information & !bdd, state, thunk.strict_order_index)
    else
        result, used_information = traced_compile_inner(thunk.expr, thunk.env, available_information, state, thunk.strict_order_index)
    end
    state.callstack = old_callstack
    # Cache the result
    if state.cfg.singleton_cache && length(thunk.cache) == 1
        (worlds, used) = thunk.cache[1]
        # The code we're imagining is (if thunk.cache[1][1] then e else e)
        res, overall_used = join_monad([((worlds, used), used), ((result, used_information), !used)], state.manager.BDD_TRUE, available_information, state)
        thunk.cache[1] = (res, overall_used)
        return (res, overall_used)
    else
        push!(thunk.cache, (result, used_information))
    end

    return result, used_information
end

"""
Process thunks into fully resolved values.
"""
function infer_full_distribution(initial_results, state)
    # Queue of (value, bdd) pairs to process
    queue = initial_results
    # Final set of fully resolved (value, bdd) pairs
    resolved = Vector{Tuple{Value, BDD}}()

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
function find_first_thunk(val::Value, path::Vector{Int} = Int[])
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