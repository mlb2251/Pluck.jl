export posterior_sample
function posterior_sample(val, state)    
    # First evaluate the evidence thunk to get true/false BDDs
    evidence_results, _ = evaluate(val.args[2], state.BDD_TRUE, state)
    n = from_value(sample_thunk(val.args[3], SampleValueState(nothing, [], nothing, false)))
    samples = []
    for i in 1:n
        # Find the BDD where evidence is true
        evidence_bdd = nothing
        for (result, bdd) in evidence_results
            if result == Pluck.TRUE_VALUE || (result isa Value && result.constructor == :True)
                evidence_bdd, _ = RSDD.weighted_sample(bdd, state.weights)
                break
            end
        end
    
        if isnothing(evidence_bdd) || RSDD.bdd_is_false(evidence_bdd)
            @warn "Evidence has zero probability; cannot take posterior sample."
            return []
        end
    
        # Create a sampling state that uses the evidence BDD as a constraint
        # We need to preserve the callstack from the query thunk
        # println("Evidence BDD: $evidence_bdd")
        # println("Callstack: $(sort(collect(keys(state.var_of_callstack))))")
        query_thunk = val.args[1]
        sample_state = SampleValueState(
            evidence_bdd,
            [],
            state.var_of_callstack,
            true
        )
    
        # Sample from the query under the evidence constraint
        # println("Query thunk env: $(query_thunk.env)")
        # println("Evidence thunk env: $(val.args[2].expr)")
        # println("Query thunk callstack: $(query_thunk.callstack)")
        # sampled_value = sample_value_forward(query_thunk.expr, query_thunk.env, sample_state)
        sampled_value = sample_thunk(query_thunk, sample_state)
        push!(samples, force_value(sampled_value, sample_state))
    end
    return samples
end

# How to handle that some choices are irrelevant?
function adaptive_rejection_sampling(val, state)

    constraint = state.BDD_TRUE
    sorted_callstacks = state.sorted_callstacks
    sorted_var_labels = state.sorted_var_labels

    sample_state = SampleValueState(constraint, [], state.var_of_callstack, true)
    
    while true
        sampled_constraint, _ = RSDD.weighted_sample(constraint, state.weights)
        sample_state.constraint = sampled_constraint
        sampled_pred = sample_thunk(val.args[2], sample_state)
        
        if sampled_pred == Pluck.TRUE_VALUE
            sample_state.lazy = false
            return sample_thunk(val.args[1], sample_state)
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
                RSDD.wmc_param_f64_set_weight(state.weights, bdd_topvar(addr), 1.0 - callstack[2], callstack[2])
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
        println(sample_thunk(val.args[1], sample_state))
        sample_state.lazy = true
        sample_state.trace = Dict{Tuple{Vector{Int}, Float64}, Bool}()
        @assert !RSDD.bdd_is_false(constraint) "Constraint is false..."
        println("Rejected trace. Total mass remaining: $(RSDD.bdd_wmc(constraint, state.weights))")
    end

end