function pure_monad(val, null, state::SampleValueState)
    return val
end

program_error_worlds(state::SampleValueState) = nothing
inference_error_worlds(state::SampleValueState) = nothing
false_path_condition_worlds(state::SampleValueState) = nothing

function bind_monad(cont::F, val, null, state::SampleValueState) where F <: Function
    isnothing(val) && return nothing
    return cont(val, null)
end
