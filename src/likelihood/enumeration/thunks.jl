mutable struct LazyEnumeratorThunk <: Thunk
    expr::PExpr
    env::Vector{Any}
    callstack::Vector{Int}
    strict_order_index::Int
    id::Int

    function LazyEnumeratorThunk(expr::PExpr, env::Vector{Any}, state::LazyEnumeratorEvalState, strict_order_index::Int)
        @assert !state.cfg.strict
        if expr isa Var && env[expr.idx] isa LazyEnumeratorThunk
            return env[expr.idx]
        end
        id = state.next_thunk_id
        state.next_thunk_id += 1
        new(expr, env, copy(state.callstack), strict_order_index, id)
    end
end

function make_thunk(expr, env, strict_order_index, state::LazyEnumeratorEvalState)
    return LazyEnumeratorThunk(expr, env, state, strict_order_index)
end

function evaluate(thunk::LazyEnumeratorThunk, trace::Trace, state::LazyEnumeratorEvalState)
    if state.hit_limit
        return inference_error_worlds(state)
    end

    # Check the cache
    cached = get_cache(trace, thunk.id, state)
    if cached !== nothing
        # println("hitting cache containing:", cached)
        return pure_monad(cached, trace, state)
    end

    # Otherwise we have to evaluate the thunk. Set the callstack to the thunk's callstack.
    old_callstack = state.callstack
    state.callstack = thunk.callstack
    result = traced_compile_inner(thunk.expr, thunk.env, trace, state, thunk.strict_order_index)
    state.callstack = old_callstack
    # Cache the result
    result = map(result) do (val, trace)
        (val, set_cache(trace, thunk.id, val, state))
    end
    return result
end