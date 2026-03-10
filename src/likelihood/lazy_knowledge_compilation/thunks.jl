
struct LazyKCThunk <: Thunk
    expr::PExpr
    env::Env
    cache::Vector{GuardedWorlds}
    callstack::Callstack
    strict_order_index::Int
    stacktrace::Vector{Union{PExpr, Nothing}}

    function LazyKCThunk(expr, env::Env, strict_order_index::Int, state)
        if expr isa PExpr{Var} && getenv(env, expr.head.name) isa LazyKCThunk
            return getenv(env, expr.head.name)
        end
        thunk = new(expr, env, [], copy(state.callstack), strict_order_index, copy(state.stacktrace))
        return thunk
    end
end

function Base.show(io::IO, x::LazyKCThunk)
    print(io, "LazyKCThunk(", x.expr, ")")
end

function make_thunk(expr, env, strict_order_index, state::LazyKCState)
    thunk = LazyKCThunk(expr, env, strict_order_index, state)
    if ENABLE_LOGGING
        print_make_thunk(thunk, state)
    end
    return thunk
end

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
    if ENABLE_LOGGING
        print_thunk_enter(thunk, state)
    end
    old_callstack = state.callstack
    state.callstack = thunk.callstack
    old_stacktrace = state.stacktrace
    state.stacktrace = thunk.stacktrace

    result = traced_compile_inner(thunk.expr, thunk.env, path_condition, state, thunk.strict_order_index)

    state.callstack = old_callstack
    state.stacktrace = old_stacktrace
    if ENABLE_LOGGING
        print_thunk_exit(thunk, result, state)
    end
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