

function pure_monad(val, trace, state::LazyEnumeratorEvalState)
    return [(val, trace)]
end


function if_then_else_monad(val_if_true, val_if_false, addr_p::Tuple{Int, Float64}, trace, state::LazyEnumeratorEvalState)
    addr, p = addr_p
    trace_true = extend_trace(trace, Choice(addr, true, log(p)), state)
    trace_false = extend_trace(trace, Choice(addr, false, log1p(-p)), state)
    return [(val_if_true, trace_true), (val_if_false, trace_false)]
end

function bind_monad(cont::F, first_stage_results, trace, state::LazyEnumeratorEvalState) where F <: Function
    if check_time_limit(state)
        state.hit_limit = true
        return []
    end
    results = []
    for (result, trace) in first_stage_results
        state.hit_limit && return []
        second_stage_worlds = cont(result, trace)
        state.hit_limit && return []
        for (final_result, final_trace) in second_stage_worlds
            push!(results, (final_result, final_trace))
        end
    end
    return results
end