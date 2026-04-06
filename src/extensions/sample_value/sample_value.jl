mutable struct SampleValueState
    constraint::Union{BDD, Nothing}
    callstack::Vector{Int}
    stacktrace::Vector{Union{PExpr, Nothing}}
    trace::Dict{Tuple{Vector{Int}, Float64}, Bool}
    var_of_callstack::Union{Dict{Tuple{Callstack, Float64}, BDD}, Nothing}
    manager::Union{RSDD.Manager, Nothing}
    lazy::Bool
    cache::IdDict{LazyKCThunk, Any}
    thunks::IdDict{LazyKCThunk, Nothing}

    function SampleValueState(;constraint=nothing, callstack=Int[], var_of_callstack=nothing, lazy=false, manager=nothing, thunks=nothing)
        thunks_dict = isnothing(thunks) ? IdDict{LazyKCThunk, Nothing}() : thunks
        state = new(
            constraint,
            callstack,
            [],
            Dict{Tuple{Vector{Int}, Float64}, Bool}(),
            var_of_callstack,
            manager,
            lazy,
            IdDict{LazyKCThunk, Any}(),
            thunks_dict,
        )
        return state
    end
end

function traced_compile_inner(expr, env, null, state::SampleValueState, strict_order_index::Int)
    push!(state.callstack, strict_order_index)
    print_enter(expr, env, state)
    result = compile_inner(expr, env, null, state)
    print_exit(expr, result, env, state)
    pop!(state.callstack)
    return result
end


function mutate_values(f::F, value, state::SampleValueState) where F <: Function
    f(value)
    return value
end