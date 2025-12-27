export bdd_forward_with_suspension, bdd_forward_with_suspension_top_k, subproblem_monte_carlo

# A few approaches to sampling.
# 1) We could sample actual traces from the posterior given "suspended".
#    Then, in the next call to evaluate (on the thunk or thunk union inside "suspended"),
#    we encode the sampled trace or traces as path_condition.
#    One question is whether this necessarily samples every variable present in the 
#    guard BDD of the suspension. I think it would not need to: we essentially begin
#    by doing a bottom up model count of the BDD, and then sample downward, replacing
#    the unchosen branches with False. Depending on the path we choose, this may or may not
#    sample every variable.


# 2) We could try to "flatten" the suspension, recursively replacing thunks with lists of 
#    thunks that have single-thunk environments. Then a separate step could re-merge?
#    One question is the extent to which the nested thunk-union structure is useful,
#    and points to a cleaner way.
#    For example, one step of sampling would just replace the env of the top-level BDD
#    with all non-union thunks, and not worry yet about the sub-thunk-unions.
#    But then what is the next step of sampling? 


function bdd_forward_with_suspension(expr; kwargs...)
    s = LazyKCState(; kwargs..., free_manager=false)

    if expr isa String
        expr = parse_expr(expr)
    end

    ret, used_info = compile_inner(expr, EMPTY_ENV, s.manager.BDD_TRUE, s)

    true_probability = 0.0
    false_probability = 0.0
    path_condition = s.manager.BDD_TRUE
    multiplier = 1.0
    i = 0
    more_to_do = true
    while more_to_do
        i += 1
        more_to_do = false
        # Now, the ret will contain a list of pairs (sb, bdd).
        for (sb, guard) in ret
            if sb.constructor == :FinallyTrue
                true_probability += multiplier * RSDD.bdd_wmc(path_condition & guard)
            elseif sb.constructor == :FinallyFalse
                false_probability += multiplier * RSDD.bdd_wmc(path_condition & guard)
            elseif sb.constructor == :Suspend
                @assert !more_to_do # we should only have one :Suspend.
                more_to_do = true
                posterior_sample, posterior_probability = RSDD.weighted_sample(path_condition & guard)
                path_condition = path_condition & posterior_sample
                multiplier *= (1 / posterior_probability) # (total_guard / RSDD.bdd_wmc(path_condition))
                ret, used_info = Pluck.evaluate(sb.args[1], path_condition, s)
            else
                error("Expected a suspended boolean, got $(sb).")
            end
        end
        #println("Iteration $i: true => $(true_probability), false => $(false_probability)")
    end

    RSDD.free_bdd_manager(s.manager)
    RSDD.free_wmc_params(s.manager.weights)

    return (true => true_probability, false => false_probability)
end

function bdd_forward_with_suspension_top_k(expr::String, k::Integer; kwargs...)
    s = LazyKCState(; kwargs..., free_manager=false)

    ret, used_info = compile_inner(expr, Pluck.EMPTY_ENV, s.manager.BDD_TRUE, s)

    true_probability = 0.0
    false_probability = 0.0
    path_condition = s.manager.BDD_TRUE
    multiplier = 1.0
    i = 0
    more_to_do = true
    while more_to_do
        i += 1
        more_to_do = false
        # Now, the ret will contain a list of pairs (sb, bdd).
        for (sb, guard) in ret
            if sb.constructor == :FinallyTrue
                true_probability += multiplier * RSDD.bdd_wmc(path_condition & guard)
            elseif sb.constructor == :FinallyFalse
                false_probability += multiplier * RSDD.bdd_wmc(path_condition & guard)
            elseif sb.constructor == :Suspend
                @assert !more_to_do # we should only have one :Suspend.
                more_to_do = true

                # Create a "sum-and-sample" BDD.
                path_condition = path_condition & guard
                top_k_bdd = RSDD.bdd_top_k_paths(path_condition, k)
                posterior_guard = path_condition & !top_k_bdd
                if RSDD.bdd_is_false(posterior_guard)
                    # The top K paths contained all the available information. We can just recurse.
                    ret, used_info = Pluck.evaluate(sb.args[1], path_condition, s)
                    continue
                end

                (sampled_bdd, sampled_probability) = RSDD.weighted_sample(posterior_guard)

                # Likely unnecessary...
                sampled_bdd = posterior_guard & sampled_bdd

                # Figure out total weight (for multiplier) as well as
                # relative weights of the sample to the top-k. 
                # Use a new Boolean variable to switch between sampled and top-k.
                # (question: where in the variable order should this new variable go?)
                # What we want:
                #  wmc(total) = wmc(top-k) + 1/q(sampled) wmc(sampled)
                #  if we add a coin flip with probability (1/(1+1/q(sampled))) of heads, and 
                #  choose the top-k if heads, otherwise choose sampled, then the expected value (wmc)
                #  will be (1/(1+1/q(sampled))) wmc(top-k) + ((1/q(sampled))/(1+1/q(sampled))) wmc(sampled)
                #  = 1/(1+1/q(sampled)) (wmc(top-k) + 1/q(sampled) wmc(sampled)).
                # So if multiply 1+1/q(sampled) into the multiplier, the thing will cancel and we will get what we want.
                mult_increment = 1 + (1 / sampled_probability)
                multiplier *= mult_increment
                # Now, if we were to just OR the sampled and top-k BDDs, we should get a model count that is the sum of the other model counts.
                # println("wmc for sampled OR top-k: $(RSDD.bdd_wmc(sampled_bdd | top_k_bdd, s.weights))")
                # But, we are actually going to take a weighted average of the two, instead of a sum. 
                new_variable = RSDD.bdd_new_var(s.manager, true) # this adds at *end* of variable order -- that might be bad?
                new_bdd = RSDD.bdd_ite(new_variable, sampled_bdd, top_k_bdd)
                new_variable_weight = 1 / mult_increment
                RSDD.set_weight(s.manager, RSDD.bdd_topvar(new_variable), new_variable_weight, 1.0 - new_variable_weight)
                path_condition = path_condition & new_bdd
                ret, used_info = Pluck.evaluate(sb.args[1], path_condition, s)
            else
                error("Expected a suspended boolean, got $(sb).")
            end
        end
        #println("Iteration $i: true => $(true_probability), false => $(false_probability)")
    end

    RSDD.free_bdd_manager(s.manager)
    RSDD.free_wmc_params(s.manager.weights)

    return (true => true_probability, false => false_probability)
end



# Forget "Suspendible Booleans" -- consider a "suspendible" type that has (Suspend ...) and (Return ...)
# as its two constructors. We incrementally build up a BDD that represents an unbiased estimate of the 
# marginal distribution on `Return`. Then a single additional bdd_forward on the thunk inside the Return
# gives the distribution (but it will in general need to be normalized).
function subproblem_monte_carlo(ret, k::Integer, state::LazyKCState)
    return_thunk_union = LazyKCThunkUnion(Tuple{LazyKCThunk, BDD}[], state)
    available_information = state.manager.BDD_TRUE

    return_bdd_normalizer = 1.0
    multiplier = 1.0
    i = 0
    more_to_do = true

    while more_to_do
        i += 1
        more_to_do = false
        return_guard = nothing
        return_value = nothing
        for (sb, guard) in ret
            if sb.constructor == :Return
                return_guard = guard
                return_value = sb.args[1]
            end
        end
        if !isnothing(return_guard)
            # How do you do "existing BDD + multiplier * new BDD" in BDD logic?
            # Make a new variable that chooses between the existing BDD and the new one.
            # The relative probability of new vs. existing is multiplier/(1+multiplier).
            # The normalizer gets multiplied by (1 + multiplier).
            # new_variable = RSDD.bdd_new_var(state.manager, true) # this adds at *end* of variable order -- that might be bad?
            # new_guard = !new_variable & return_guard & available_information
            # old_guard = new_variable
            # return_thunk_union = BDDThunkUnion([(return_value, new_guard), (return_thunk_union, old_guard)], state)
            # # return_bdd = RSDD.bdd_ite(new_variable, return_guard, return_bdd)
            # new_variable_weight = multiplier / (1 + multiplier)
            # RSDD.wmc_param_f64_set_weight(state.weights, RSDD.bdd_topvar(new_variable), new_variable_weight, 1.0 - new_variable_weight)
            # return_bdd_normalizer *= (1 + multiplier)

            # Alternative approach
            # TODO: is this always correct? 
            # issue is if somehow multiple guards get combined, and we end up with something like `new_variable | !new_variable`, 
            # which could lead to `new_variable` not being in the BDD, so that WMCs don't get the (1 + multiplier) term.
            # Seems like this could happen if we have expressions like "Return x" in multiple branches; the x will be the same
            # exact thunk and we will try to merge. So the long-term solution is probably to either make a version of BDDThunkUnion 
            # that trakcs weights on the thunks, or switch to log space and do the renormalization trick as above.
            new_variable = RSDD.bdd_new_var(state.manager, true) # this adds at *end* of variable order -- that might be bad?
            new_guard = new_variable & return_guard & available_information
            old_guard = !new_variable
            return_thunk_union = LazyKCThunkUnion([(return_value, new_guard), (return_thunk_union, old_guard)], state)
            # new_variable_weight = multiplier
            RSDD.set_weight(state.manager, RSDD.bdd_topvar(new_variable), 1.0, multiplier)
            # return_bdd_normalizer *= (1 + multiplier)
        end

        suspend_guard = nothing
        suspend_value = nothing
        for (sb, guard) in ret
            if sb.constructor == :Suspend
                suspend_guard = guard
                suspend_value = sb.args[1]
            end
        end
        if !isnothing(suspend_guard)
            more_to_do = true
            available_information = available_information & suspend_guard
            top_k_bdd = RSDD.bdd_top_k_paths(available_information, k)

            posterior_guard = available_information & !top_k_bdd
            if RSDD.bdd_is_false(posterior_guard)
                # The top K paths contained all the available information. We can just recurse.
                ret, used_info = Pluck.evaluate(suspend_value, available_information, state)
                continue
            end

            (sampled_bdd, sampled_probability) = RSDD.weighted_sample(posterior_guard) # , state.weights)
            # Likely unnecessary...
            sampled_bdd = posterior_guard & sampled_bdd

            # Figure out total weight (for multiplier) as well as
            # relative weights of the sample to the top-k. 
            # Use a new Boolean variable to switch between sampled and top-k.
            # (question: where in the variable order should this new variable go?)
            # What we want:
            #  wmc(total) = wmc(top-k) + 1/q(sampled) wmc(sampled)

            # So if multiply 1+1/q(sampled) into the multiplier, the thing will cancel and we will get what we want.
            mult_increment = 1 + (1 / sampled_probability)
            multiplier *= mult_increment
            # Now, if we were to just OR the sampled and top-k BDDs, we should get a model count that is the sum of the other model counts.
            # println("wmc for sampled OR top-k: $(RSDD.bdd_wmc(sampled_bdd | top_k_bdd, s.weights))")
            # But, we are actually going to take a weighted average of the two, instead of a sum.
            new_variable = RSDD.bdd_new_var(state.manager, true) # this adds at *end* of variable order -- that might be bad?
            new_bdd = RSDD.bdd_ite(new_variable, sampled_bdd, top_k_bdd)
            new_variable_weight = 1 / mult_increment
            RSDD.set_weight(state.manager, RSDD.bdd_topvar(new_variable), new_variable_weight, 1.0 - new_variable_weight)
            available_information = available_information & new_bdd
            
            ret, used_info = Pluck.evaluate(suspend_value, available_information, state)
        end
    end
    
    return return_thunk_union, return_bdd_normalizer
end