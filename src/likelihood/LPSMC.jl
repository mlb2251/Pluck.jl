export bdd_forward_with_suspension, bdd_forward_with_suspension_top_k

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
                posterior_sample, posterior_probability = RSDD.weighted_sample(path_condition & guard, s.manager.weights)
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

                (sampled_bdd, sampled_probability) = RSDD.weighted_sample(posterior_guard, s.manager.weights)

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

    return (true => true_probability, false => false_probability)
end
