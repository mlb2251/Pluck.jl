export posterior_sample, adaptive_rejection_sampling, SampleValueState

function posterior_sample(val, state::LazyKCState)
    @assert val.constructor == :PosteriorSamples && length(val.args) == 3 "expected (PosteriorSamples query evidence num-samples)"
    query_thunk = val.args[1]
    evidence_thunk = val.args[2]
    num_samples_thunk = val.args[3]

    # First evaluate the evidence thunk to get true/false BDDs
    evidence_results = toplevel_evaluate(evidence_thunk, state)
    evidence_bdd = true_bdd(evidence_results)

    if bdd_is_false(evidence_bdd)
        @warn "Evidence has zero probability; cannot take posterior sample."
        return []
    end
    
    # should be safe to use the same state because we're forced to be deterministic here anyways
    n, = from_value(deterministic_world(force_thunks(toplevel_evaluate(num_samples_thunk, state))))

    samples = []
    shared_thunks = LazyKCThunk[]
    for i in 1:n
        # clear any cached results from previous sample
        for t in shared_thunks
            empty!(t.cache)
        end
        empty!(shared_thunks)
        clear_thunk_cache!(query_thunk)

        # Sample a BDD where evidence is true
        sampled_evidence_bdd, _ = bdd_weighted_sample(evidence_bdd)
    
        # Create a sampling state that uses the evidence BDD as a constraint
        # We need to preserve the callstack from the query thunk
        sample_state = SampleValueState(
            constraint=sampled_evidence_bdd, # constraint
            var_of_callstack=state.var_of_callstack, # var_of_callstack
            lazy=true, # lazy
            manager=state.manager, # manager
            thunks=shared_thunks, # thunks
        )
    
        # Sample from the query under the evidence constraint
        sampled_value = force_thunk(query_thunk, sample_state)
        push!(samples, sampled_value)
    end
    return samples
end

# How to handle that some choices are irrelevant?
function adaptive_rejection_sampling(val, state::LazyKCState)

    result_thunk = val.args[1]
    predicate_thunk = val.args[2]

    constraint = state.manager.BDD_TRUE
    sorted_callstacks = state.sorted_callstacks
    sorted_var_labels = state.sorted_var_labels

    shared_thunks = LazyKCThunk[]
    sample_state = SampleValueState(;constraint, var_of_callstack=state.var_of_callstack, lazy=true, manager=state.manager, thunks=shared_thunks)
    # clear caches on predicate/result thunks before sampling loop
    
    while true
        # clear all caches
        clear_thunk_cache!(result_thunk)
        clear_thunk_cache!(predicate_thunk)
        for t in shared_thunks
            empty!(t.cache)
        end
        empty!(shared_thunks)

        sampled_constraint, _ = bdd_weighted_sample(constraint)
        sample_state.constraint = sampled_constraint
        sampled_pred = force_thunk(predicate_thunk, sample_state)

        @assert sampled_pred isa Value && (sampled_pred.constructor == :True || sampled_pred.constructor == :False) "Expected True or False, got $(sampled_pred.constructor)"
        
        if sampled_pred isa Value && sampled_pred.constructor == :True
            sample_state.lazy = false
            return evaluate(result_thunk, nothing, sample_state)
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
        println(evaluate(result_thunk, nothing, sample_state))
        sample_state.lazy = true
        sample_state.trace = Dict{Tuple{Vector{Int}, Float64}, Bool}()
        @assert !RSDD.bdd_is_false(constraint) "Constraint is false..."
        println("Rejected trace. Total mass remaining: $(bdd_wmc(constraint))")
    end

end