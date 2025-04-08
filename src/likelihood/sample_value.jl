using .RSDD

export sample_value, SampleValueState

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

function sample_value_forward(expr::App, env::Env, state::SampleValueState)
    f = traced_sample_value(expr.f, env, state, 0)
    arg = state.lazy ? BDDThunk(expr.x, env, state.callstack, :lazy_arg, 1, nothing) : traced_sample_value(expr.x, env, state, 1)

    new_env = copy(f.env)
    pushfirst!(new_env, arg)
    return traced_sample_value(f.expr, new_env, state, 2)
end

function sample_value_forward(expr::Abs, env::Env, state::SampleValueState)
    # A lambda term deterministically evaluates to a closure.
    return Closure(expr.body, env)
end

function sample_value_forward(expr::Construct, env::Env, state::SampleValueState)
    # Look up type of this constructor.
    spt = Pluck.spt_of_constructor[expr.constructor]
    # Evaluate each argument.
    evaluated_arguments = [(state.lazy ? BDDThunk(arg, env, state.callstack, Symbol("lazy_arg$(i)"), i, nothing) : traced_sample_value(arg, env, state, i)) for (i, arg) in enumerate(expr.args)]
    # Return the constructor and its arguments.
    return Value(spt, expr.constructor, evaluated_arguments)
end

function sample_value_forward(expr::CaseOf, env::Env, state::SampleValueState)
    scrutinee_value = traced_sample_value(expr.scrutinee, env, state, 0)
    constructor_indices = Dict{Symbol, Int}()
    for (i, constructor) in enumerate(expr.constructors) # sort? reverse?
        constructor_indices[constructor] = i
    end

    if !(scrutinee_value.constructor in keys(expr.cases))
        @warn "Constructor $(scrutinee_value.constructor) not found in cases of expression $(expr)."
        return nothing
    end

    case_expr = expr.cases[scrutinee_value.constructor]
    num_args = length(args_of_constructor(scrutinee_value.constructor))
    if num_args == 0
        return traced_sample_value(case_expr, env, state, constructor_indices[scrutinee_value.constructor])
    else
        for _ = 1:num_args
            case_expr = case_expr.body
        end
        new_env = copy(env)
        for (arg) in scrutinee_value.args
            pushfirst!(new_env, arg)
        end
        return traced_sample_value(case_expr, new_env, state, constructor_indices[scrutinee_value.constructor])
    end
end

function sample_value_forward(expr::Y, env::Env, state::SampleValueState)
    @assert expr.f isa Abs && expr.f.body isa Abs "y-combinator must be applied to a double-lambda"

    closure = Pluck.make_self_loop(expr.f.body.body, env)

    # set up a closure with a circular reference
    return closure
end

function sample_value_forward(expr::PrimOp, env::Env, state::SampleValueState)
    sample_value_prim_forward(expr.op, expr.args, env, state)
end


function sample_value_prim_forward(op::MkIntOp, args, env::Env, state::SampleValueState)
    return args[2]
end


function sample_value_prim_forward(op::IntDistEqOp, args, env::Env, state::SampleValueState)
    arg1 = traced_sample_value(args[1], env, state, 0)
    arg2 = traced_sample_value(args[2], env, state, 1)
    return arg1 == arg2 ? Pluck.TRUE_VALUE : Pluck.FALSE_VALUE
end

function sample_value_prim_forward(op::FlipOp, args, env::Env, state::SampleValueState)
    p = traced_sample_value(args[1], env, state, 0)
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

function sample_value_prim_forward(op::ConstructorEqOp, args, env::Env, state::SampleValueState)
    # Evaluate both arguments.
    first_arg_result = traced_sample_value(args[1], env, state, 0)
    second_arg_result = traced_sample_value(args[2], env, state, 1)
    if first_arg_result.constructor == second_arg_result.constructor
        return Pluck.TRUE_VALUE
    else
        return Pluck.FALSE_VALUE
    end
end

function sample_thunk(t::BDDThunk, state::SampleValueState)
    # Remember old callstack
    old_callstack = state.callstack
    state.callstack = copy(t.callstack)
    result = traced_sample_value(t.expr, t.env, state, t.strict_order_index)
    state.callstack = old_callstack
    return result
end

function sample_thunk(t::BDDThunkUnion, state::SampleValueState)
    error("BDDThunkUnion found while posterior sampling; this should not happen unless a PosteriorSample query was *randomly* generated.")
end

function sample_value_forward(expr::Var, env::Env, state::SampleValueState)
    # Look up the variable in the environment.
    if expr.idx > length(env)
        @warn "Variable $expr not found in environment."
        return nothing
    end

    if env[expr.idx] isa BDDThunk || env[expr.idx] isa BDDThunkUnion
        return sample_thunk(env[expr.idx], state)
    else
        return env[expr.idx]
    end
end

function sample_value_forward(expr::Defined, env::Env, state::SampleValueState)
    # Execute Defined with a blanked out environment.
    return traced_sample_value(Pluck.lookup(expr.name).expr, Pluck.EMPTY_ENV, state, 0)
end

function sample_value_forward(expr::Root, env::Env, state::SampleValueState)
    return traced_sample_value(expr.body, env, state, 0)
end

function sample_value_forward(expr::ConstReal, env::Env, state::SampleValueState)
    return expr.val
end

function sample_value(expr::PExpr, env::Env, state::SampleValueState)
    return traced_sample_value(expr, env, state, 0)
end

function force_value(v::Value, state::SampleValueState)
    for i in 1:length(v.args)
        if v.args[i] isa BDDThunk
            v.args[i] = force_value(sample_thunk(v.args[i], state), state)
        end
    end
    return v
end

function force_value(v::Closure, state::SampleValueState)
    return v
end