
function evaluate(thunk::LazyKCThunk, null, state::SampleValueState)
    # we use a cache in the state instead of thunk because the same thunk gets
    # used for multiple posterior samples
    get!(state.cache, thunk) do 
        evaluate_no_cache(thunk, null, state)
    end
    # if isempty(thunk.cache)
    #     res = evaluate_no_cache(thunk, null, state)
    #     push!(thunk.cache, res)
    # end
    # @assert length(thunk.cache) == 1
    # return thunk.cache[1]

    # from other:
    # mgr = state.manager
    # # Attempt cache hit
    # if mgr !== nothing && !isempty(thunk.cache)
    #     worlds, guard = thunk.cache[1]
    #     if !bdd_is_false(guard)
    #         return worlds[1][1]
    #     end
    # end

    # res = evaluate_no_cache(thunk, null, state)

    # if mgr !== nothing
    #     guarded = (Vector{World}([(res, mgr.BDD_TRUE)]), mgr.BDD_TRUE)
    #     empty!(thunk.cache)
    #     push!(thunk.cache, guarded)
    # end
    # return res
end

function make_thunk(expr, env, strict_order_index, state::SampleValueState)
    # since posterior sampling just produces one result, we dont need to worry about binding in the strict case
    !state.lazy && return traced_compile_inner(expr, env, nothing, state, strict_order_index)
    thunk = LazyKCThunk(expr, env, strict_order_index, state)
    if thunk ∉ state.thunks
        push!(state.thunks, thunk)
    end
    print_make_thunk(thunk, state)
    return thunk
end