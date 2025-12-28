export posterior_sample, adaptive_rejection_sampling, SampleValueState

function posterior_sample(val, state)
    @assert val.constructor == :PosteriorSamples && length(val.args) == 3 "expected (PosteriorSamples query evidence num-samples)"
    # First evaluate the evidence thunk to get true/false BDDs
    evidence_results, _ = evaluate(val.args[2], state.manager.BDD_TRUE, state)
    shared_thunks = LazyKCThunk[]
    n, concrete = from_value(evaluate(val.args[3], nothing, SampleValueState(nothing, [], nothing, false, state.manager, shared_thunks)))
    samples = []
    for i in 1:n
        # clear any cached results from previous sample
        for t in shared_thunks
            empty!(t.cache)
        end
        empty!(shared_thunks)
        if val.args[1] isa LazyKCThunk || val.args[1] isa LazyKCThunkUnion
            clear_thunk_cache!(val.args[1])
        end
        # Find the BDD where evidence is true
        evidence_bdd = nothing
        for (result, bdd) in evidence_results
            if result == Pluck.TRUE_VALUE || (result isa Value && result.constructor == :True)
                evidence_bdd, _ = RSDD.weighted_sample(bdd)
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
            true,
            state.manager,
            shared_thunks,
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

    shared_thunks = LazyKCThunk[]
    sample_state = SampleValueState(constraint, [], state.var_of_callstack, true, state.manager, shared_thunks)
    # clear caches on predicate/result thunks before sampling loop
    if val.args[1] isa LazyKCThunk || val.args[1] isa LazyKCThunkUnion
        clear_thunk_cache!(val.args[1])
    end
    if val.args[2] isa LazyKCThunk || val.args[2] isa LazyKCThunkUnion
        clear_thunk_cache!(val.args[2])
    end
    
    while true
        sampled_constraint, _ = RSDD.weighted_sample(constraint)
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
                RSDD.set_weight(state.manager, bdd_topvar(addr), 1.0 - callstack[2], callstack[2])
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
        for t in shared_thunks
            empty!(t.cache)
        end
        empty!(shared_thunks)
        @assert !RSDD.bdd_is_false(constraint) "Constraint is false..."
        println("Rejected trace. Total mass remaining: $(RSDD.bdd_wmc(constraint))")
    end

end