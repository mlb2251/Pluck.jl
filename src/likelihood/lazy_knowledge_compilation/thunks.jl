
struct LazyKCThunk <: Thunk
    expr::Union{PExpr, Thunk}
    env::Env
    cache::Vector{GuardedWorlds}
    callstack::Callstack
    strict_order_index::Int

    function LazyKCThunk(expr, env::Env, strict_order_index::Int, state)
        if expr isa PExpr{Var} && env[expr.head.idx] isa LazyKCThunk
            return env[expr.head.idx]
        end

        # key = (expr, env, state.callstack)
        # if state.cfg.use_thunk_cache && haskey(state.thunk_cache, key)
        #     return state.thunk_cache[key]
        # else
        thunk = new(expr, env, [], copy(state.callstack), strict_order_index)
        # if state.cfg.use_thunk_cache
        #     state.thunk_cache[(expr, copy(env), copy(state.callstack))] = thunk
        # end
        return thunk
        # end
    end
end

function Base.show(io::IO, x::LazyKCThunk)
    print(io, "LazyKCThunk(", x.expr, ")")
end

function make_thunk(expr, env, strict_order_index, state::LazyKCState)
    thunk = LazyKCThunk(expr, env, strict_order_index, state)
    print_make_thunk(thunk, state)
    return thunk
end

"""
this thunk returns a NativeValue{PExpr} so say it might look like (quote ...)
though of course it might also return more than one expression.
We'd like to effectively make a thunk that goes (eval (quote ...))

(eval #1)

"""
# function make_thunk(thunk::Thunk, env, strict_order_index, state::LazyKCState)
#     bind_evaluate(thunk, env, path_condition, state) do e, path_condition
#         @assert e isa NativeValue && e.value isa PExpr "Thunk must be evaluated to a NativeValue{PExpr}, got $(e) :: $(typeof(e))"
#         return make_thunk(e.value, env, strict_order_index, state)
#     end
# end

struct LazyKCThunkUnion <: Thunk
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

function evaluate(thunk::LazyKCThunkUnion, path_condition::BDD, state::LazyKCState)
    if !state.cfg.disable_used_information && bdd_is_false(path_condition)
        return false_path_condition_worlds(state)
    end
    nested_worlds = (thunk.thunks, state.manager.BDD_TRUE)
    # thunk union evaluate is really just a bind with the continuation being the single-union evaluate function
    return bind_monad(evaluate, nested_worlds, path_condition, state; cont_state=true)
end

function evaluate_no_cache(thunk::LazyKCThunk, path_condition, state)
    print_thunk_enter(thunk, state)
    old_callstack = state.callstack
    state.callstack = thunk.callstack

    expr = thunk.expr
    if expr isa LazyKCThunk
        # if the .expr is a Thunk, we need to evaluate it first to get a PExprValue
        return bind_evaluate(expr, thunk.env, path_condition, state) do e, path_condition
            # @assert e isa PExprValue "LazyKCThunk must be evaluated to a PExprValue, got $(e) :: $(typeof(e))"
            @assert e isa NativeValue && e.value isa PExpr "LazyKCThunk must be evaluated to a NativeValue{PExpr{T}}, got $(e) :: $(typeof(e))"
            result = traced_compile_inner(e.value, thunk.env, path_condition, state, thunk.strict_order_index)
            state.callstack = old_callstack
            print_thunk_exit(thunk, result, state)
            return result
        end
    end
    result = traced_compile_inner(expr, thunk.env, path_condition, state, thunk.strict_order_index)

    state.callstack = old_callstack
    print_thunk_exit(thunk, result, state)
    return result
end

function evaluate(thunk::LazyKCThunk, path_condition, state::LazyKCState)
    if !state.cfg.disable_used_information && bdd_is_false(path_condition)
        return false_path_condition_worlds(state)
    end

    # Check the cache
    for (worlds, used_info) in thunk.cache
        if bdd_is_true(bdd_implies(path_condition, used_info))
            return (worlds, used_info)
        end
    end

    # handle deprecated version of the cache system
    if !state.cfg.singleton_cache
        res = evaluate_no_cache(thunk, path_condition, state)
        push!(thunk.cache, res)
        return res
    end

    # nothing in cache
    if isempty(thunk.cache)
        worlds = evaluate_no_cache(thunk, path_condition, state)
        push!(thunk.cache, worlds)
        return worlds
    end

    @assert length(thunk.cache) == 1
    cached_worlds, cache_guard = thunk.cache[1]

    """
    We want to run the code: (if cache_guard then cached_worlds else evaluated_worlds)
    Using the path condition: path_condition | cache_guard
    OR-ing in the cache guard ensures that we don't lose any of the information we had previously stored in the cache.

    We can do this through a bind():
    """

    hit_cache_worlds = if_then_else_monad(true, false, cache_guard, path_condition, state)
    path_condition |= cache_guard
    worlds = bind_monad(hit_cache_worlds, path_condition, state; cont_state=true) do hit_cache, path_condition, state
        hit_cache ? (cached_worlds, state.manager.BDD_TRUE) : evaluate_no_cache(thunk, path_condition, state)
    end
    thunk.cache[1] = worlds

    """
    Note an equivalent (but same speed) way to do this without bind is:
    ```
    inner_path_condition = path_condition & !cache_guard
    cache_miss_worlds, cache_miss_used = evaluate_no_cache(thunk, inner_path_condition, state)
    cache_miss_worlds = ((cache_miss_worlds, cache_miss_used), !cache_guard)
    cache_hit_worlds = ((cached_worlds, cache_guard), cache_guard)
    nested_worlds = [cache_hit_worlds, cache_miss_worlds], state.manager.BDD_TRUE
    worlds = join_monad(nested_worlds, state)
    thunk.cache[1] = worlds
    ```
    """

    return worlds
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

function pretty_thunk(thunk::LazyKCThunk)
    return "Thunk $(thunk.expr)"
end

function print_thunk_enter(thunk::LazyKCThunk, state)
    get_verbose() || return
    cs = pretty_callstack(state.callstack)
    thunk_cs = pretty_callstack(thunk.callstack, thunk.strict_order_index)
    printstyled("$cs $(pretty_thunk(thunk)) ", color=:yellow)
    printstyled("@ $thunk_cs\n", color=:magenta)
end

function print_thunk_exit(thunk::LazyKCThunk, result, state)
    get_verbose() || return
    cs = pretty_callstack(state.callstack)
    thunk_cs = pretty_callstack(thunk.callstack, thunk.strict_order_index)
    printstyled("$thunk_cs $(pretty_thunk(thunk)) ", color=:green)
    printstyled("-> $result ", color=:blue)
    printstyled("@ $cs\n", color=:magenta)
end

function print_make_thunk(thunk::LazyKCThunk, state)
    get_verbose() || return
    cs = pretty_callstack(thunk.callstack, thunk.strict_order_index)
    printstyled("$cs Make $(pretty_thunk(thunk))\n", color=:cyan)
end