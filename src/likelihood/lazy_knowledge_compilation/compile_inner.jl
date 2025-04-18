#################################
#### COMPILE IMPLEMENTATIONS ####
#################################


struct CompileFrame{E <: Expr}
    expr::E
    env::Env
    strict_order_index::Int
end

struct ContinuationFrame{F <: Function, T, E}
    continuation::F
    data::T
    parent::CompileFrame{E}
end

struct BindFrame{F <: Function, T, E}
    pre_frame::CompileFrame
    post_frame::ContinuationFrame{F, T, E}

    function BindFrame(continuation::F, pre_frame::CompileFrame, data::T, parent::CompileFrame{E}) where {F <: Function, T, E}
        post_frame = ContinuationFrame(continuation, data, parent)
        new{F, T, E}(pre_frame, post_frame)
    end
end

struct PureFrame
    worlds::GuardedWorlds
end

function compile_inner(frame::CompileFrame{App}, state::LazyKCState)
    fs = CompileFrame(frame.expr.f, frame.env, 0)
    thunked_argument = LazyKCThunk(frame.expr.x, frame.env, state.callstack, :app_x, 1, state)

    return BindFrame(fs, thunked_argument, frame) do f, state, thunked_argument, frame
        new_env = copy(f.env)
        pushfirst!(new_env, thunked_argument)
        return CompileFrame(f.expr, new_env, 2)
    end
end

function compile_inner(frame::CompileFrame{Abs}, state::LazyKCState)
    # A lambda term deterministically evaluates to a closure.
    return PureFrame(pure_monad(Closure(frame.expr.body, frame.env), state))
end

function compile_inner(frame::CompileFrame{Construct}, state::LazyKCState)
    # Constructors deterministically evaluate to a WHNF value, with their arguments thunked.
    # Create a thunk for each argument.
    thunked_arguments = [LazyKCThunk(arg, env, state.callstack, Symbol("$(expr.constructor).arg$i"), i, state) for (i, arg) in enumerate(expr.args)] # TODO: use global args_syms to avoid runtime cost of Symbol?
    # Return the constructor and its arguments.
    return PureFrame(pure_monad(Value(frame.expr.constructor, thunked_arguments), state))
end

function compile_inner(frame::CompileFrame{CaseOf}, state::LazyKCState)
    scrutinee_worlds = CompileFrame(frame.expr.scrutinee, frame.env, 0)
    constructor_indices = Dict{Symbol, Int}()
    for (i, constructor) in enumerate(keys(frame.expr.cases)) # sort? reverse?
        constructor_indices[constructor] = i
    end
    # caseof_type = type_of_constructor[first(keys(expr.cases))]
    BindFrame(scrutinee_worlds, state, constructor_indices) do scrutinee, state, constructor_indices, frame
        # value_type = type_of_constructor[scrutinee.constructor]
        # if !isempty(expr.cases) && !(value_type == caseof_type)
            # @warn "TypeError: Scrutinee constructor $(scrutinee.constructor) of type $value_type is not the same as the case statement type $caseof_type"
        # end
        
        if !(scrutinee.constructor in keys(frame.expr.cases))
            # println("Scrutinee not in case expression, shaving off probability: $(scrutinee) in $(expr)")
            # todo should this be true or false for used info?
            return shave_probabilty(state)
        end

        case_expr = frame.expr.cases[scrutinee.constructor]
        num_args = length(args_of_constructor[scrutinee.constructor])

        for _ = 1:num_args
            @assert case_expr isa Abs "case expression branch for constructor $(scrutinee.constructor) must have as many lambdas as the constructor has arguments ($(num_args) arguments)"
            case_expr = case_expr.body
        end
        # In each of the scrutinee arguments, filter out options that contradict the available information.
        new_env = num_args == 0 ? frame.env : copy(frame.env)
        @assert length(scrutinee.args) == num_args
        for arg in scrutinee.args
            pushfirst!(new_env, arg)
        end
        return CompileFrame(case_expr, new_env, constructor_indices[scrutinee.constructor])
    end
end

function compile_inner(frame::CompileFrame{Y}, state::LazyKCState)
    @assert frame.expr.f isa Abs && frame.expr.f.body isa Abs "y-combinator must be applied to a double-lambda"
    closure = Pluck.make_self_loop(frame.expr.f.body.body, frame.env)
    return PureFrame(pure_monad(closure, state))
end

function compile_inner(frame::CompileFrame{Var}, state::LazyKCState)
    # Look up the variable in the environment.
    @assert frame.expr.idx <= length(frame.env) "Variable $(frame.expr) not found in environment"

    v = frame.env[frame.expr.idx]
    if v isa LazyKCThunk || v isa LazyKCThunkUnion
        return evaluate(v, path_condition, state)
    end

    # Does this case ever arise? One example is that for recursive calls,
    # we create a closure (not a thunk) and store it in the environment.
    return pure_monad(v, state)
end

function compile_inner(frame::CompileFrame{Defined}, state::LazyKCState)
    # Execute Defined with a blanked out environment.
    return traced_compile_inner(Pluck.lookup(frame.expr.name).expr, Pluck.EMPTY_ENV, path_condition, state, 0)
end

function compile_inner(frame::CompileFrame{ConstReal}, state::LazyKCState)
    return pure_monad(FloatValue(frame.expr.val), state)
end

function compile_inner(frame::CompileFrame{PrimOp}, state::LazyKCState)
    compile_prim(frame.expr.op, frame.expr.args, frame.env, path_condition, state)
end

################################
#### PRIMOP IMPLEMENTATIONS ####
################################

function compile_prim(op::FlipOp, args, env::Env, path_condition::BDD, state::LazyKCState)

    ps = CompileFrame(args[1], env, 0)
    BindFrame(ps, state) do p, state, _, frame
        p = p.value
        if isapprox(p, 0.0)
            return PureFrame(pure_monad(Pluck.FALSE_VALUE, state))
        elseif isapprox(p, 1.0)
            return PureFrame(pure_monad(Pluck.TRUE_VALUE, state))
        else
            # If we are past the max depth, AND we are sampling after the max depth, AND 
            # this flip is new (not previously instantiated), THEN sample a value.
            if state.cfg.max_depth !== nothing && state.depth > state.cfg.max_depth && state.cfg.sample_after_max_depth && !haskey(state.var_of_callstack, (state.callstack, p))
                sampled_value = rand() < p ? Pluck.TRUE_VALUE : Pluck.FALSE_VALUE
                return PureFrame(pure_monad(sampled_value, state))
            end

            # Otherwise, we perform the usual logic.
            # BDDs do not represent quantitative probabilities. Therefore, for each 
            # different probability `p`, we need to create a new variable in the BDD.
            push!(state.callstack, 1)
            addr = current_bdd_address(state, p)
            RSDD.set_weight(state.manager, bdd_topvar(addr), 1.0 - p, p)
            pop!(state.callstack)
            return PureFrame(if_then_else_monad(Pluck.TRUE_VALUE, Pluck.FALSE_VALUE, addr, state))
        end
    end
end

function compile_prim(op::ConstructorEqOp, args, env::Env, path_condition::BDD, state::LazyKCState)
    # Evaluate both arguments.
    first_arg_results = CompileFrame(args[1], env, 0)
    BindFrame(first_arg_results, state) do arg1, state, _, frame
        second_arg_results = CompileFrame(args[2], env, 1)
        BindFrame(second_arg_results, state) do arg2, state, _, frame
            val = arg1.constructor == arg2.constructor ? Pluck.TRUE_VALUE : Pluck.FALSE_VALUE
            return PureFrame(pure_monad(val, state))
        end
    end
end

function compile_prim(op::MkIntOp, args, env::Env, path_condition::BDD, state::LazyKCState)
    bitwidth = args[1]::RawInt
    val = args[2]::RawInt
    bools = digits(Bool, val.val, base = 2, pad = bitwidth.val)
    bits = map(b -> b ? state.manager.BDD_TRUE : state.manager.BDD_FALSE, bools)

    return PureFrame(pure_monad(IntDist(bits), state))
end

function compile_prim(op::IntDistEqOp, args, env::Env, path_condition::BDD, state::LazyKCState)
    first_int_dist = CompileFrame(args[1], env, 0)
    BindFrame(first_int_dist, state) do first_int_dist, state, _, frame
        second_int_dist = CompileFrame(args[2], env, 1)
        BindFrame(second_int_dist, state) do second_int_dist, state, _, frame
            bdd = int_dist_eq(first_int_dist, second_int_dist, state)
            return PureFrame(if_then_else_monad(Pluck.TRUE_VALUE, Pluck.FALSE_VALUE, bdd, state))
        end
    end
end
