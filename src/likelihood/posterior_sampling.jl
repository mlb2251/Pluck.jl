export posterior_sample, adaptive_rejection_sampling, SampleValueState

function posterior_sample(val, state)
    @assert val.constructor == :PosteriorSamples && length(val.args) == 3 "expected (PosteriorSamples query evidence num-samples)"
    # First evaluate the evidence thunk to get true/false BDDs
    evidence_results, _ = evaluate(val.args[2], state.manager.BDD_TRUE, state)
    n, concrete = from_value(evaluate(val.args[3], nothing, SampleValueState(nothing, [], nothing, false)))
    samples = []
    for i in 1:n
        # Find the BDD where evidence is true
        evidence_bdd = nothing
        for (result, bdd) in evidence_results
            if result == Pluck.TRUE_VALUE || (result isa Value && result.constructor == :True)
                evidence_bdd, _ = RSDD.weighted_sample(bdd, state.manager.weights)
                break
            end
        end
    
        if isnothing(evidence_bdd) || RSDD.bdd_is_false(evidence_bdd)
            @warn "Evidence has zero probability; cannot take posterior sample."
            return []
        end
    
        # Create a sampling state that uses the evidence BDD as a constraint
        # We need to preserve the callstack from the query thunk
        query_thunk = val.args[1]
        sample_state = SampleValueState(
            evidence_bdd,
            [],
            state.var_of_callstack,
            true
        )
    
        # Sample from the query under the evidence constraint
        sampled_value = evaluate(query_thunk, nothing, sample_state)
        forced = force_value(sampled_value, query_thunk.env, sample_state)
        push!(samples, forced)
    end
    return samples
end

# How to handle that some choices are irrelevant?
function adaptive_rejection_sampling(val, state)

    constraint = state.manager.BDD_TRUE
    sorted_callstacks = state.sorted_callstacks
    sorted_var_labels = state.sorted_var_labels

    sample_state = SampleValueState(constraint, [], state.var_of_callstack, true)
    
    while true
        sampled_constraint, _ = RSDD.weighted_sample(constraint, state.manager.weights)
        sample_state.constraint = sampled_constraint
        sampled_pred = evaluate(val.args[2], nothing, sample_state)
        
        if sampled_pred == Pluck.TRUE_VALUE
            sample_state.lazy = false
            return evaluate(val.args[1], nothing, sample_state)
        end

        # Construct a BDD using the sampled trace.
        trace = sample_state.trace
        trace_as_bdd = sample_state.constraint
        for (callstack, result) in trace
            # Check if callstack already has a variable in the BDD.
            if !haskey(sample_state.var_of_callstack, callstack)
                # Add a new variable to the BDD.
                i = searchsortedfirst(sorted_callstacks, callstack; by = x -> x[1])
                # Insert the callstack in the sorted list.
                addr = RSDD.bdd_new_var_at_position(state.manager, i - 1, true) # Rust uses 0-indexing
                insert!(sorted_callstacks, i, callstack)
                insert!(sorted_var_labels, i, Int(bdd_topvar(addr)))
                sample_state.var_of_callstack[callstack] = addr
                RSDD.wmc_param_f64_set_weight(state.manager.weights, bdd_topvar(addr), 1.0 - callstack[2], callstack[2])
            end
            addr = sample_state.var_of_callstack[callstack]
            if result
                trace_as_bdd = RSDD.bdd_and(trace_as_bdd, addr)
            else
                trace_as_bdd = RSDD.bdd_and(trace_as_bdd, !(addr))
            end
        end

        constraint = RSDD.bdd_and(constraint, !trace_as_bdd)

        sample_state.lazy = false
        println(evaluate(val.args[1], nothing, sample_state))
        sample_state.lazy = true
        sample_state.trace = Dict{Tuple{Vector{Int}, Float64}, Bool}()
        @assert !RSDD.bdd_is_false(constraint) "Constraint is false..."
        println("Rejected trace. Total mass remaining: $(RSDD.bdd_wmc(constraint))")
    end

end

mutable struct SampleValueState
    constraint::Union{BDD, Nothing}
    callstack::Vector{Int}
    trace::Dict{Tuple{Vector{Int}, Float64}, Bool}
    var_of_callstack::Union{Dict{Tuple{Callstack, Float64}, BDD}, Nothing}
    lazy::Bool

    function SampleValueState(constraint=nothing, callstack=Int[], var_of_callstack=nothing, lazy=false)
        state = new(
            constraint,
            callstack,
            Dict{Tuple{Vector{Int}, Float64}, Bool}(),
            var_of_callstack,
            lazy
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



function pure_monad(val, null, state::SampleValueState)
    return val
end

function program_error_worlds(state::SampleValueState)
    return nothing
end

function bind_monad(cont::F, val, null, state::SampleValueState) where F <: Function
    isnothing(val) && return nothing
    return cont(val, null)
end

function evaluate(thunk::LazyKCThunk, null, state::SampleValueState)
    # no cache for posterior sampling – but we can reuse the cacheless version from lazy KC
    res = evaluate_no_cache(thunk, null, state)
    return res
end



function compile_inner(expr::PExpr{FlipOp}, env::Env, null::Nothing, state::SampleValueState)
    p = traced_compile_inner(expr.args[1], env, null, state, 0)
    p = p.value
    isapprox(p, 0.0) && return Pluck.FALSE_VALUE
    isapprox(p, 1.0) && return Pluck.TRUE_VALUE

    callstack_to_check = ([state.callstack..., 1], p)

    if haskey(state.trace, callstack_to_check)
        return state.trace[callstack_to_check] ? Pluck.TRUE_VALUE : Pluck.FALSE_VALUE
    end

    if state.constraint === nothing || !haskey(state.var_of_callstack, callstack_to_check)
        # Freely sample a value. 
        result = rand() < p
        state.trace[callstack_to_check] = result
        return result ? Pluck.TRUE_VALUE : Pluck.FALSE_VALUE
    end


    var = state.var_of_callstack[callstack_to_check]
    bdd_is_true(bdd_implies(state.constraint, var)) && return Pluck.TRUE_VALUE
    bdd_is_true(bdd_implies(state.constraint, !var)) && return Pluck.FALSE_VALUE
    result = rand() < p
    state.trace[callstack_to_check] = result
    return result ? Pluck.TRUE_VALUE : Pluck.FALSE_VALUE
end


function make_thunk(expr, env, strict_order_index, state::SampleValueState)
    # since posterior sampling just produces one result, we dont need to worry about binding in the strict case
    !state.lazy && return traced_compile_inner(expr, env, nothing, state, strict_order_index)
    thunk = LazyKCThunk(expr, env, strict_order_index, state)
    print_make_thunk(thunk, state)
    return thunk
end

function traced_force_value(v, env, state)
    return force_value(v, env, state)
end

"""
thunks get evaluated, and their results are forced as well
"""
function force_value(v::Thunk, env, state::SampleValueState)
    return traced_force_value(evaluate(v, nothing, state), env, state)
end

"""
values get forced by forcing their args recursively
"""
function force_value(v::Value, env, state::SampleValueState)
    v.args = [traced_force_value(arg, env, state) for arg in v.args]
    return v
end

function force_value(v::PExpr, env, state::SampleValueState)
    v.args = [traced_force_value(arg, env, state) for arg in v.args]
    return v
end

function force_value(v::NativeValue{PExpr{T}}, env, state::SampleValueState) where T <: Head
    return traced_force_value(v.value, env, state)
end


"""
Force is a no-op for all other values
"""
force_value(v, env, state::SampleValueState) = v







