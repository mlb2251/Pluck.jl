"""
force_thunk is like force_thunks but when you have a SampleValueState so there's no path condition
to thread through and you know you'll only get one result.
"""
function force_thunk(v::Thunk, state::SampleValueState)
    return force_thunk(evaluate(v, nothing, state), state)
end

function force_thunk(v::Value, state::SampleValueState)
    v.args = [force_thunk(arg, state) for arg in v.args]
    return v
end

force_thunk(v, state::SampleValueState) = v
