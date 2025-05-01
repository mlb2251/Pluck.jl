export posterior_sample, adaptive_rejection_sampling, sample_value, SampleValueState

function posterior_sample(val, state)    
    # First evaluate the evidence thunk to get true/false BDDs
    evidence_results, _ = evaluate(val.args[2], state.manager.BDD_TRUE, state)
    n, concrete = from_value(sample_thunk(val.args[3], SampleValueState(nothing, [], nothing, false)))
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
        sampled_value = sample_thunk(query_thunk, sample_state)
        push!(samples, force_value(sampled_value, sample_state))
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
        println(sample_thunk(val.args[1], sample_state))
        sample_state.lazy = true
        sample_state.trace = Dict{Tuple{Vector{Int}, Float64}, Bool}()
        @assert !RSDD.bdd_is_false(constraint) "Constraint is false..."
        println("Rejected trace. Total mass remaining: $(RSDD.bdd_wmc(constraint))")
    end

end

# Representations of values:
# - Closure: a list of guarded Closure objects, which each store a body and an environment.
# - Float64: floats and BDDs.
# - Value: a list of possible constructors, each guarded by a BDD, and each with a list of arguments, themselves values.

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

function traced_sample_value(expr::PExpr, env::Env, state::SampleValueState, strict_order_index::Int)
    push!(state.callstack, strict_order_index)
    result = sample_value_forward(expr, env, state)
    pop!(state.callstack)
    return result
end

function sample_value_forward(expr::PExpr, env::Env, state::SampleValueState)
    error("sample_value_forward not implemented for $(typeof(expr))")
end

function sample_value_forward(expr::PExpr{ConstNative}, env::Env, state::SampleValueState)
    return expr.args[1]
end


function sample_value_forward(expr::PExpr{App}, env::Env, state::SampleValueState)
    f = traced_sample_value(expr.args[1], env, state, 0)
    arg = state.lazy ? make_thunk(expr.args[2], env, 1, state) : traced_sample_value(expr.args[2], env, state, 1)

    new_env = copy(f.env)
    pushfirst!(new_env, arg)
    return traced_sample_value(f.expr, new_env, state, 2)
end

function sample_value_forward(expr::PExpr{Abs}, env::Env, state::SampleValueState)
    # A lambda term deterministically evaluates to a closure.
    return Closure(expr.args[1], env)
end

function sample_value_forward(expr::PExpr{Construct}, env::Env, state::SampleValueState)
    # Evaluate each argument.
    evaluated_arguments = [(state.lazy ? make_thunk(arg, env, i, state) : traced_sample_value(arg, env, state, i)) for (i, arg) in enumerate(expr.args[2])]
    # Return the constructor and its arguments.
    return Value(expr.args[1], evaluated_arguments)
end

function sample_value_forward(expr::PExpr{CaseOf}, env::Env, state::SampleValueState)
    scrutinee_value = traced_sample_value(expr.args[1], env, state, 0)

    idx = findfirst(c -> c[1] == scrutinee_value.constructor, expr.args[2])

    if isnothing(idx)
        @warn "Constructor $(scrutinee_value.constructor) not found in cases of expression $(expr)."
        return nothing
    end

    case_expr = expr.args[2][idx][2]
    num_args = length(args_of_constructor[scrutinee_value.constructor])
    if num_args == 0
        return traced_sample_value(case_expr, env, state, idx)
    else
        for _ = 1:num_args
            case_expr = case_expr.args[1]
        end
        new_env = copy(env)
        for (arg) in scrutinee_value.args
            pushfirst!(new_env, arg)
        end
        return traced_sample_value(case_expr, new_env, state, idx)
    end
end

function sample_value_forward(expr::PExpr{Y}, env::Env, state::SampleValueState)
    @assert expr.args[1] isa PExpr{Abs} && expr.args[1].args[1] isa PExpr{Abs} "y-combinator must be applied to a double-lambda"

    closure = Pluck.make_self_loop(expr.args[1].args[1].args[1], env)

    # set up a closure with a circular reference
    return closure
end


function sample_value_forward(expr::PExpr{MkIntOp}, env::Env, state::SampleValueState)
    return expr.args[2]
end


function sample_value_forward(expr::PExpr{IntDistEqOp}, env::Env, state::SampleValueState)
    arg1 = traced_sample_value(expr.args[1], env, state, 0)
    arg2 = traced_sample_value(expr.args[2], env, state, 1)
    return arg1 == arg2 ? Pluck.TRUE_VALUE : Pluck.FALSE_VALUE
end

function sample_value_forward(expr::PExpr{FlipOp}, env::Env, state::SampleValueState)
    p = traced_sample_value(expr.args[1], env, state, 0)
    if isapprox(p, 0.0)
        return Pluck.FALSE_VALUE
    elseif isapprox(p, 1.0)
        return Pluck.TRUE_VALUE
    end

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
    if bdd_is_true(bdd_implies(state.constraint, var))
        return Pluck.TRUE_VALUE
    elseif bdd_is_true(bdd_implies(state.constraint, !var))
        return Pluck.FALSE_VALUE
    else
        # @warn "Flip with a variable that appears in constraint but is not constrained."
        result = rand() < p
        state.trace[callstack_to_check] = result
        return result ? Pluck.TRUE_VALUE : Pluck.FALSE_VALUE
    end
end

function sample_value_forward(expr::PExpr{NativeEqOp}, env::Env, state::SampleValueState)
    # Evaluate both arguments.
    first_arg_result = traced_sample_value(expr.args[1], env, state, 0)
    second_arg_result = traced_sample_value(expr.args[2], env, state, 1)
    if first_arg_result.value == second_arg_result.value
        return Pluck.TRUE_VALUE
    else
        return Pluck.FALSE_VALUE
    end
end

function sample_value_forward(expr::PExpr{GetArgsOp}, env::Env, state::SampleValueState)
    val = traced_sample_value(expr.args[1], env, state, 0)
    @assert val isa Value
    res = Value(:Nil)
    for arg in reverse(val.args)
        res = Value(:Cons, [arg, res])
    end
    return res
end


function make_thunk(expr::PExpr, env, strict_order_index, state::SampleValueState)
    return LazyKCThunk(expr, env, strict_order_index, state)
end

function sample_thunk(t::LazyKCThunk, state::SampleValueState)
    # Remember old callstack
    old_callstack = state.callstack
    state.callstack = copy(t.callstack)
    result = traced_sample_value(t.expr, t.env, state, t.strict_order_index)
    state.callstack = old_callstack
    return result
end

function sample_thunk(t::LazyKCThunkUnion, state::SampleValueState)
    error("LazyKCThunkUnion found while posterior sampling; this should not happen unless a PosteriorSample query was *randomly* generated.")
end

function sample_value_forward(expr::PExpr{Var}, env::Env, state::SampleValueState)
    # Look up the variable in the environment.
    if expr.args[1] > length(env)
        @warn "Variable $expr not found in environment."
        return nothing
    end

    if env[expr.args[1]] isa LazyKCThunk || env[expr.args[1]] isa LazyKCThunkUnion
        return sample_thunk(env[expr.args[1]], state)
    else
        return env[expr.args[1]]
    end
end

function sample_value_forward(expr::PExpr{Defined}, env::Env, state::SampleValueState)
    # Execute Defined with a blanked out environment.
    return traced_sample_value(Pluck.lookup(expr.args[1]).expr, Pluck.EMPTY_ENV, state, 0)
end

function sample_value(expr::PExpr, env::Env, state::SampleValueState)
    return traced_sample_value(expr, env, state, 0)
end

function force_value(v::Value, state::SampleValueState)
    for i in 1:length(v.args)
        if v.args[i] isa LazyKCThunk
            v.args[i] = force_value(sample_thunk(v.args[i], state), state)
        end
    end
    return v
end

function force_value(v::Closure, state::SampleValueState)
    return v
end