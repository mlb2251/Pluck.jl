"""
force_value is like infer_full_distribution but when you have a SampleValueState so there's no path condition
to thread through and you know you'll only get one result.
"""
function force_value(v::Thunk, env, state::SampleValueState)
    return force_value(evaluate(v, nothing, state), env, state)
end

function force_value(v::Value, env, state::SampleValueState)
    v.args = [force_value(arg, env, state) for arg in v.args]
    return v
end

force_value(v, env, state::SampleValueState) = v
