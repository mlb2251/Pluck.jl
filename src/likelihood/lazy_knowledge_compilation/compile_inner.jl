#################################
#### COMPILE IMPLEMENTATIONS ####
#################################

function compile_inner(expr::App, env::Env, path_condition::BDD, state::LazyKCState)
    fs = traced_compile_inner(expr.f, env, path_condition, state, 0)
    thunked_argument = LazyKCThunk(expr.x, env, state.callstack, :app_x, 1, state)

    return bind_monad(fs, path_condition, state) do f, path_condition
        new_env = copy(f.env)
        x = thunked_argument
        pushfirst!(new_env, x)
        return traced_compile_inner(f.expr, new_env, path_condition, state, 2)
    end
end

function compile_inner(expr::Abs, env::Env, path_condition::BDD, state::LazyKCState)
    # A lambda term deterministically evaluates to a closure.
    return pure_monad(Closure(expr.body, env), state)
end

function compile_inner(expr::Construct, env::Env, path_condition::BDD, state::LazyKCState)
    # Constructors deterministically evaluate to a WHNF value, with their arguments thunked.
    # Create a thunk for each argument.
    thunked_arguments = [LazyKCThunk(arg, env, state.callstack, Symbol("$(expr.constructor).arg$i"), i, state) for (i, arg) in enumerate(expr.args)] # TODO: use global args_syms to avoid runtime cost of Symbol?
    # Return the constructor and its arguments.
    return pure_monad(Value(expr.constructor, thunked_arguments), state)
end

function compile_inner(expr::CaseOf, env::Env, path_condition::BDD, state::LazyKCState)
    scrutinee_values = traced_compile_inner(expr.scrutinee, env, path_condition, state, 0)
    constructor_indices = Dict{Symbol, Int}()
    for (i, constructor) in enumerate(keys(expr.cases)) # sort? reverse?
        constructor_indices[constructor] = i
    end
    # caseof_type = type_of_constructor[first(keys(expr.cases))]
    bind_monad(scrutinee_values, path_condition, state) do scrutinee, path_condition
        # value_type = type_of_constructor[scrutinee.constructor]
        # if !isempty(expr.cases) && !(value_type == caseof_type)
            # @warn "TypeError: Scrutinee constructor $(scrutinee.constructor) of type $value_type is not the same as the case statement type $caseof_type"
        # end
        
        if !(scrutinee.constructor in keys(expr.cases))
            # println("Scrutinee not in case expression: $(scrutinee) in $(expr)")
            return program_error_worlds(state)
        end

        case_expr = expr.cases[scrutinee.constructor]
        num_args = length(args_of_constructor[scrutinee.constructor])
        @assert length(scrutinee.args) == num_args

        for _ = 1:num_args
            @assert case_expr isa Abs "case expression branch for constructor $(scrutinee.constructor) must have as many lambdas as the constructor has arguments ($(num_args) arguments)"
            case_expr = case_expr.body
        end
        # In each of the scrutinee arguments, filter out options that contradict the available information.
        new_env = num_args == 0 ? env : copy(env)
        for arg in scrutinee.args
            pushfirst!(new_env, arg)
        end
        return traced_compile_inner(case_expr, new_env, path_condition, state, constructor_indices[scrutinee.constructor])
    end
end

function compile_inner(expr::Y, env::Env, path_condition::BDD, state::LazyKCState)
    @assert expr.f isa Abs && expr.f.body isa Abs "y-combinator must be applied to a double-lambda"
    closure = Pluck.make_self_loop(expr.f.body.body, env)
    return pure_monad(closure, state)
end

function compile_inner(expr::Var, env::Env, path_condition::BDD, state::LazyKCState)

    v = env[expr.idx]
    if v isa LazyKCThunk || v isa LazyKCThunkUnion
        return evaluate(v, path_condition, state)
    end

    return pure_monad(v, state)
end

function compile_inner(expr::DiffVar, env::Env, path_condition::BDD, state::LazyKCState)
    return pure_monad(UIntValue(expr.idx), state)
end

function compile_inner(expr::Defined, env::Env, path_condition::BDD, state::LazyKCState)
    # Execute Defined with a blanked out environment.
    return traced_compile_inner(Pluck.lookup(expr.name).expr, Pluck.EMPTY_ENV, path_condition, state, 0)
end

function compile_inner(expr::ConstReal, env::Env, path_condition::BDD, state::LazyKCState)
    return pure_monad(FloatValue(expr.val), state)
end


function compile_inner(expr::PrimOp, env::Env, path_condition::BDD, state::LazyKCState)
    compile_prim(expr.op, expr.args, env, path_condition, state)
end


################################
#### PRIMOP IMPLEMENTATIONS ####
################################

function compile_prim(op::FlipOp, args, env::Env, path_condition::BDD, state::LazyKCState)

    ps = traced_compile_inner(args[1], env, path_condition, state, 0)
    bind_monad(ps, path_condition, state) do p, path_condition
        p = p.value
        if isapprox(p, 0.0)
            return pure_monad(Pluck.FALSE_VALUE, state)
        elseif isapprox(p, 1.0)
            return pure_monad(Pluck.TRUE_VALUE, state)
        else
            # If we are past the max depth, AND we are sampling after the max depth, AND 
            # this flip is new (not previously instantiated), THEN sample a value.
            if state.cfg.max_depth !== nothing && state.depth > state.cfg.max_depth && state.cfg.sample_after_max_depth && !haskey(state.var_of_callstack, (state.callstack, p))
                sampled_value = rand() < p ? Pluck.TRUE_VALUE : Pluck.FALSE_VALUE
                return pure_monad(sampled_value, state)
            end

            # Otherwise, we perform the usual logic.
            # BDDs do not represent quantitative probabilities. Therefore, for each 
            # different probability `p`, we need to create a new variable in the BDD.
            push!(state.callstack, 1)
            addr = current_bdd_address(state, p)
            RSDD.set_weight(state.manager, bdd_topvar(addr), 1.0 - p, p)
            pop!(state.callstack)
            return if_then_else_monad(Pluck.TRUE_VALUE, Pluck.FALSE_VALUE, addr, state)
        end
    end
end

function compile_prim(op::FlipOpDual, args, env::Env, path_condition::BDD, state::LazyKCState)
    npartials = state.manager.vector_size

    metaparams = traced_compile_inner(args[1], env, path_condition, state, 0)
    p_init = 0.5
    # All we want to do is update a dictionary in BDDEvalState saying that bdd_topvar(addr) is associated with args[1].metaparam
    bind_monad(metaparams, path_condition, state) do metaparam, path_condition
        metaparam = metaparam.value
        if state.cfg.max_depth !== nothing && state.depth > state.cfg.max_depth && state.cfg.sample_after_max_depth && !haskey(state.var_of_callstack, (state.callstack, p))
            sampled_value = rand() < p ? Pluck.TRUE_VALUE : Pluck.FALSE_VALUE
            return [(sampled_value, state.manager.BDD_TRUE)], state.manager.BDD_TRUE
        end
        push!(state.callstack, 1)
        addr = current_bdd_address(state, p_init)
        topvar = bdd_topvar(addr)
        state.param2metaparam[topvar] = metaparam
        partials_hi = zeros(Float64, npartials)
        partials_hi[metaparam+1] = 1.0
        partials_lo = zeros(Float64, npartials)
        partials_lo[metaparam+1] = -1.0
        set_weight_deriv(state.manager.weights, topvar, p_init, partials_lo, p_init, partials_hi)
        pop!(state.callstack)
        return [(Pluck.TRUE_VALUE, addr), (Pluck.FALSE_VALUE, !addr)], state.manager.BDD_TRUE
    end
end

function compile_prim(op::ConstructorEqOp, args, env::Env, path_condition::BDD, state::LazyKCState)
    # Evaluate both arguments.
    first_arg_results = traced_compile_inner(args[1], env, path_condition, state, 0)
    bind_monad(first_arg_results, path_condition, state) do arg1, path_condition
        second_arg_results = traced_compile_inner(args[2], env, path_condition, state, 1)
        bind_monad(second_arg_results, path_condition, state) do arg2, path_condition
            val =  arg1.constructor == arg2.constructor ? Pluck.TRUE_VALUE : Pluck.FALSE_VALUE
            return pure_monad(val, state)
        end
    end
end

"""
Given a Value, returns a Cons-list of its arguments.
"""
function compile_prim(op::GetArgsOp, args, env::Env, path_condition::BDD, state::LazyKCState)
    vals = traced_compile_inner(args[1], env, path_condition, state, 0)
    bind_monad(vals, path_condition, state) do val, path_condition
        res = Value(:Nil)
        for arg in reverse(val.args)
            res = Value(:Cons, [arg, res])
        end
        return pure_monad(res, state)
    end
end

function compile_prim(op::GetConstructorOp, args, env::Env, path_condition::BDD, state::LazyKCState)
    val = traced_compile_inner(args[1], env, path_condition, state, 0)
    bind_monad(val, path_condition, state) do val, path_condition
        return pure_monad(HostValue(val.constructor), state)
    end
end

function compile_prim(op::MkIntOp, args, env::Env, path_condition::BDD, state::LazyKCState)
    bitwidth = args[1]::RawInt
    val = args[2]::RawInt
    bools = digits(Bool, val.val, base = 2, pad = bitwidth.val)
    bits = map(b -> b ? state.manager.BDD_TRUE : state.manager.BDD_FALSE, bools)

    return pure_monad(IntDist(bits), state)
end

function compile_prim(op::IntDistEqOp, args, env::Env, path_condition::BDD, state::LazyKCState)
    first_int_dist = traced_compile_inner(args[1], env, path_condition, state, 0)
    bind_monad(first_int_dist, path_condition, state) do first_int_dist, path_condition
        second_int_dist = traced_compile_inner(args[2], env, path_condition, state, 1)
        bind_monad(second_int_dist, path_condition, state) do second_int_dist, path_condition
            bdd = int_dist_eq(first_int_dist, second_int_dist, state)
            return if_then_else_monad(Pluck.TRUE_VALUE, Pluck.FALSE_VALUE, bdd, state)
        end
    end
end

function compile_prim(op::PBoolOp, args, env::Env, path_condition::BDD, state::LazyKCState)
    cond = traced_compile_inner(args[1], env, path_condition, state, 0)

    p_true = -Inf
    p_false = -Inf

    @assert length(cond[1]) <= 2 "should only be true or false, at most one of each"
    for (world, guard) in cond[1]
        if world.constructor == :True
            p_true = logaddexp(p_true, log(RSDD.bdd_wmc(guard)))
        elseif world.constructor == :False
            p_false = logaddexp(p_false, log(RSDD.bdd_wmc(guard)))
        else
            error("PBoolOp: condition must be a boolean, got $(world)")
        end
    end

    logtotal = logaddexp(p_true, p_false)

    p_true_thunk = LazyKCThunk(ConstReal(exp(p_true - logtotal)), Pluck.EMPTY_ENV, state.callstack, :p_true, 1, state)
    true_thunk = LazyKCThunk(Construct(:True, Symbol[]), Pluck.EMPTY_ENV, state.callstack, :true_thunk, 3, state)
    false_thunk = LazyKCThunk(Construct(:False, Symbol[]), Pluck.EMPTY_ENV, state.callstack, :false_thunk, 4, state)
    bind_monad(cond, path_condition, state) do cond, path_condition
        if cond.constructor == :True
            return pure_monad(Value(:PBool, p_true_thunk, true_thunk), state)
        elseif cond.constructor == :False
            return pure_monad(Value(:PBool, p_true_thunk, false_thunk), state)
        else
            error("PBoolOp: condition must be a boolean, got $(cond)")
        end
    end
end
