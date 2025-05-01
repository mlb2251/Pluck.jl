mutable struct LazyEnumeratorThunk
    expr::PExpr
    env::Vector{Any}
    callstack::Vector{Symbol}
    name::Symbol
    id::Int

    function LazyEnumeratorThunk(expr::PExpr, env::Vector{Any}, state::LazyEnumeratorEvalState, name::Symbol)
        @assert !state.strict
        if expr isa Var && env[expr.idx] isa LazyEnumeratorThunk
            return env[expr.idx]
        end
        id = state.next_thunk_id
        state.next_thunk_id += 1
        new(expr, env, copy(state.callstack), name, id)
    end
end

function evaluate(thunk::LazyEnumeratorThunk, trace::Trace, state::LazyEnumeratorEvalState)
    if state.hit_limit
        return []
    end

    # Check the cache
    cached = get_cache(trace, thunk.id, state)
    if cached !== nothing
        # println("hitting cache containing:", cached)
        return [(cached, trace)]
    end

    # Otherwise we have to evaluate the thunk. Set the callstack to the thunk's callstack.
    old_callstack = state.callstack
    state.callstack = thunk.callstack
    result = traced_lazy_enumerate(thunk.expr, thunk.env, trace, state, thunk.name)
    state.callstack = old_callstack
    # Cache the result
    result = map(result) do (val, trace)
        (val, set_cache(trace, thunk.id, val, state))
    end
    return result
end