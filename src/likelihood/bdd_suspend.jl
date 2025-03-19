export bdd_forward_with_suspension, bdd_forward_with_suspension_top_k

# Suppose we have a type `SuspendableBool := FinallyTrue | FinallyFalse | Suspend SuspendableBool`.
suspended_bool_type = define_type!(:SuspendableBool, Dict(:FinallyTrue => Symbol[], :FinallyFalse => Symbol[], :Suspend => [:SuspendableBool]))

# We can define a version of, e.g., list equality, that returns a `SuspendableBool`.
@define "suspended_list_eq" """
(λ elems_equal -> 
(Y (λ suspended_list_eq xs ys -> 
  (case xs of 
    Nil        => (case ys of Nil => (FinallyTrue) | Cons _ _ => (FinallyFalse))
    Cons x xs_ => (case ys of 
      Nil        => (FinallyFalse)
      Cons y ys_ => (case (elems_equal x y) of 
        True  => (Suspend (suspended_list_eq xs_ ys_))
        False => (FinallyFalse)
      )
    )
  )
))
)
"""

# A few approaches to sampling.
# 1) We could sample actual traces from the posterior given "suspended".
#    Then, in the next call to evaluate (on the thunk or thunk union inside "suspended"),
#    we encode the sampled trace or traces as available_information.
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


function bdd_forward_with_suspension(expr::String; env=Pluck.EMPTY_ENV, return_state=false, cfg=nothing, kwargs...)
    @assert isempty(kwargs) || isnothing(cfg)
    cfg = isnothing(cfg) ? BDDEvalStateConfig(;kwargs...) : cfg
    state = Pluck.BDDEvalState(cfg)
    state.dirty && reset_state!(state)
    state.dirty = true
    state.start_time = time()
    state.manager.start_time = state.start_time
    state.manager.time_limit = state.time_limit
    start_time_limit(state.manager, state.time_limit)

    try
        ret, used_info = try
            traced_bdd_forward(parse_expr(expr), env, state.BDD_TRUE, state, 0)
        catch e
            if e isa StackOverflowError
                state.hit_limit = true
                return_state && return (true => 0., false => 0.), state
                return (true => 0., false => 0.)
            else
                rethrow(e)
            end
        end

        
        true_probability = 0.0
        false_probability = 0.0
        available_information = state.BDD_TRUE
        multiplier = 1.0
        i = 0
        more_to_do = true
        while more_to_do
            i += 1
            more_to_do = false
            # Now, the ret will contain a list of pairs (sb, bdd).
            for (sb, guard) in ret
                if sb.constructor == :FinallyTrue || sb.constructor == :True
                    true_probability += multiplier * RSDD.bdd_wmc(available_information & guard, state.weights)
                elseif sb.constructor == :FinallyFalse || sb.constructor == :False
                    false_probability += multiplier * RSDD.bdd_wmc(available_information & guard, state.weights)
                elseif sb.constructor == :Suspend
                    @assert !more_to_do # we should only have one :Suspend.
                    more_to_do = true
                    sample_input = available_information & guard

                    if RSDD.time_limit_exceeded(state.manager)
                        stop_time_limit(state.manager)
                        state.stats.time = time() - state.start_time
                        state.stats.hit_limit = true
                        return_state && return (true => 0., false => 0.), state
                        return (true => 0., false => 0.)
                    end
                    posterior_sample, posterior_probability = RSDD.weighted_sample(sample_input, state.weights)
                    available_information = available_information & posterior_sample
                    multiplier *= (1 / posterior_probability) # (total_guard / RSDD.bdd_wmc(available_information, state.weights))

                    try
                        ret, used_info = Pluck.evaluate(sb.args[1], available_information, state)
                    catch e
                        if e isa StackOverflowError
                            state.hit_limit = true
                            return_state && return (true => 0., false => 0.), state
                            return (true => 0., false => 0.)
                        else
                            rethrow(e)
                        end
                    end
                else
                    error("Expected a suspended boolean, got $(sb).")
                end
            end
            # println("Iteration $i: true => $(true_probability), false => $(false_probability)")
        end


        if RSDD.time_limit_exceeded(state.manager)
            stop_time_limit(state.manager)
            state.stats.time = time() - state.start_time
            state.stats.hit_limit = true
            return_state && return (true => 0., false => 0.), state
            return (true => 0., false => 0.)
        end

        # RSDD.free_bdd_manager(s.manager)
        # RSDD.free_wmc_params(s.weights)
        state.stats.time = time() - state.start_time
        state.stats.hit_limit = state.hit_limit
        stop_time_limit(state.manager)

        res = (true => true_probability, false => false_probability)

        return_state && return res, state
        # @show true_probability
        return res
    finally
        free_state!(state)
    end
end

function bdd_forward_with_suspension_top_k(expr::String, k::Integer; state = Pluck.BDDEvalState())
    state.dirty && reset_state!(state)
    state.dirty = true
    state.start_time = time()
    state.manager.start_time = state.start_time
    state.manager.time_limit = state.time_limit
    start_time_limit(state.manager, state.time_limit)
    ret, used_info = Pluck.bdd_forward(parse_expr(expr), Pluck.EMPTY_ENV, state.BDD_TRUE, state)

    try


        true_probability = 0.0
        false_probability = 0.0
        available_information = state.BDD_TRUE
        multiplier = 1.0
        i = 0
        more_to_do = true
        while more_to_do
            i += 1
            more_to_do = false
            # Now, the ret will contain a list of pairs (sb, bdd).
            for (sb, guard) in ret
                if sb.constructor == :FinallyTrue
                    true_probability += multiplier * RSDD.bdd_wmc(available_information & guard, state.weights)
                elseif sb.constructor == :FinallyFalse
                    false_probability += multiplier * RSDD.bdd_wmc(available_information & guard, state.weights)
                elseif sb.constructor == :Suspend
                    @assert !more_to_do # we should only have one :Suspend.
                    more_to_do = true

                    # Create a "sum-and-sample" BDD.
                    available_information = available_information & guard
                    top_k_bdd = RSDD.bdd_top_k_paths(available_information, k, state.weights)
                    posterior_guard = available_information & !top_k_bdd
                    if RSDD.bdd_is_false(posterior_guard)
                        # The top K paths contained all the available information. We can just recurse.
                        ret, used_info = Pluck.evaluate(sb.args[1], available_information, state)
                        continue
                    end

                    if RSDD.time_limit_exceeded(state.manager)
                        stop_time_limit(state.manager)
                        state.stats.time = time() - state.start_time
                        state.stats.hit_limit = true
                        return (true => 0., false => 0.)
                    end
                    (sampled_bdd, sampled_probability) = RSDD.weighted_sample(posterior_guard, state.weights)

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
                    new_variable = RSDD.bdd_new_var(state.manager, true) # this adds at *end* of variable order -- that might be bad?
                    new_bdd = RSDD.bdd_ite(new_variable, sampled_bdd, top_k_bdd)
                    new_variable_weight = 1 / mult_increment
                    RSDD.wmc_param_f64_set_weight(state.weights, RSDD.bdd_topvar(new_variable), new_variable_weight, 1.0 - new_variable_weight)
                    available_information = available_information & new_bdd
                    ret, used_info = Pluck.evaluate(sb.args[1], available_information, state)
                else
                    error("Expected a suspended boolean, got $(sb).")
                end
            end
            #println("Iteration $i: true => $(true_probability), false => $(false_probability)")
        end

        if RSDD.time_limit_exceeded(state.manager) || check_time_limit(state)
            stop_time_limit(state.manager)
            state.stats.time = time() - state.start_time
            state.stats.hit_limit = true
            return (true => 0., false => 0.)
        end

        state.stats.time = time() - state.start_time
        state.stats.hit_limit = state.hit_limit
        stop_time_limit(state.manager)
        # RSDD.free_bdd_manager(s.manager)
        # RSDD.free_wmc_params(s.weights)

        return (true => true_probability, false => false_probability)
    finally
        free_state!(state)
    end
end
