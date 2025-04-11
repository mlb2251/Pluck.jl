#################################
#### COMPILE IMPLEMENTATIONS ####
#################################

function compile_inner(expr::App, env::Env, available_information::BDD, state::LazyKCState)
    fs, used_information = traced_compile_inner(expr.f, env, available_information, state, 0)
    thunked_argument = LazyKCThunk(expr.x, env, state.callstack, :app_x, 1, state)

    return bind_monad(fs, available_information, used_information, state) do f, f_guard
        new_env = copy(f.env)
        x = thunked_argument
        pushfirst!(new_env, x)
        results, used_info = traced_compile_inner(f.expr, new_env, available_information & f_guard, state, 2)
        return results, used_information & used_info
    end
end

function compile_inner(expr::Abs, env::Env, available_information::BDD, state::LazyKCState)
    # A lambda term deterministically evaluates to a closure.
    return [(Closure(expr.body, env), state.manager.BDD_TRUE)], state.manager.BDD_TRUE
end

function compile_inner(expr::Construct, env::Env, available_information::BDD, state::LazyKCState)
    # Constructors deterministically evaluate to a WHNF value, with their arguments thunked.
    # Create a thunk for each argument.
    thunked_arguments = [LazyKCThunk(arg, env, state.callstack, Symbol("$(expr.constructor).arg$i"), i, state) for (i, arg) in enumerate(expr.args)] # TODO: use global args_syms to avoid runtime cost of Symbol?
    # Return the constructor and its arguments.
    return [(Value(expr.constructor, thunked_arguments), state.manager.BDD_TRUE)], state.manager.BDD_TRUE
end

function compile_inner(expr::CaseOf, env::Env, available_information::BDD, state::LazyKCState)
    scrutinee_values, scrutinee_used_information = traced_compile_inner(expr.scrutinee, env, available_information, state, 0)
    constructor_indices = Dict{Symbol, Int}()
    for (i, constructor) in enumerate(keys(expr.cases)) # sort? reverse?
        constructor_indices[constructor] = i
    end
    caseof_type = type_of_constructor[first(keys(expr.cases))]
    bind_monad(scrutinee_values, available_information, scrutinee_used_information, state) do scrutinee, scrutinee_guard
        value_type = type_of_constructor[scrutinee.constructor]
        if !isempty(expr.cases) && !(value_type == caseof_type)
            # @warn "TypeError: Scrutinee constructor $(scrutinee.constructor) of type $value_type is not the same as the case statement type $caseof_type"
        end
        
        if !(scrutinee.constructor in keys(expr.cases))
            # println("Scrutinee not in case expression: $(scrutinee) in $(expr)")
            return [], state.manager.BDD_TRUE
        end

        case_expr = expr.cases[scrutinee.constructor]
        num_args = length(args_of_constructor[scrutinee.constructor])
        path_condition = scrutinee_guard & available_information

        if num_args == 0
            return traced_compile_inner(case_expr, env, path_condition, state, constructor_indices[scrutinee.constructor])
        end

        for _ = 1:num_args
            @assert case_expr isa Abs "case expression branch for constructor $(scrutinee.constructor) must have as many lambdas as the constructor has arguments ($(num_args) arguments)"
            case_expr = case_expr.body
        end
        # In each of the scrutinee arguments, filter out options that contradict the available information.
        new_env = copy(env)
        used_information = state.manager.BDD_TRUE
        for arg in scrutinee.args
            pushfirst!(new_env, arg)
        end
        results, used_info = traced_compile_inner(case_expr, new_env, path_condition, state, constructor_indices[scrutinee.constructor])
        return results, used_information & used_info
    end
end

function compile_inner(expr::Y, env::Env, available_information::BDD, state::LazyKCState)
    @assert expr.f isa Abs && expr.f.body isa Abs "y-combinator must be applied to a double-lambda"
    closure = Pluck.make_self_loop(expr.f.body.body, env)
    return [(closure, state.manager.BDD_TRUE)], state.manager.BDD_TRUE
end

function compile_inner(expr::Var, env::Env, available_information::BDD, state::LazyKCState)
    # Look up the variable in the environment.
    if expr.idx > length(env)
        @warn "Variable $expr not found in environment; shaving off probability."
        return [], state.manager.BDD_TRUE
    end

    v = env[expr.idx]
    if v isa LazyKCThunk || v isa LazyKCThunkUnion
        return evaluate(v, available_information, state)
    else
        # Does this case ever arise? One example is that for recursive calls,
        # we create a closure (not a thunk) and store it in the environment.
        return [(v, state.manager.BDD_TRUE)], state.manager.BDD_TRUE
    end
end

function compile_inner(expr::Defined, env::Env, available_information::BDD, state::LazyKCState)
    # Execute Defined with a blanked out environment.
    return traced_compile_inner(Pluck.lookup(expr.name).expr, Pluck.EMPTY_ENV, available_information, state, 0)
end

function compile_inner(expr::ConstReal, env::Env, available_information::BDD, state::LazyKCState)
    return [(FloatValue(expr.val), state.manager.BDD_TRUE)], state.manager.BDD_TRUE
end


function compile_inner(expr::PrimOp, env::Env, available_information::BDD, state::LazyKCState)
    compile_prim(expr.op, expr.args, env, available_information, state)
end


################################
#### PRIMOP IMPLEMENTATIONS ####
################################

function compile_prim(op::FlipOp, args, env::Env, available_information::BDD, state::LazyKCState)

    ps, used_information = traced_compile_inner(args[1], env, available_information, state, 0)
    bind_monad(ps, available_information, used_information, state) do p, p_guard
        p = p.value
        if isapprox(p, 0.0)
            return [(Pluck.FALSE_VALUE, p_guard)], state.manager.BDD_TRUE
        elseif isapprox(p, 1.0)
            return [(Pluck.TRUE_VALUE, p_guard)], state.manager.BDD_TRUE
        else
            # If we are past the max depth, AND we are sampling after the max depth, AND 
            # this flip is new (not previously instantiated), THEN sample a value.
            if state.cfg.max_depth !== nothing && state.depth > state.cfg.max_depth && state.cfg.sample_after_max_depth && !haskey(state.var_of_callstack, (state.callstack, p))
                sampled_value = rand() < p ? Pluck.TRUE_VALUE : Pluck.FALSE_VALUE
                return [(sampled_value, state.manager.BDD_TRUE)], state.manager.BDD_TRUE
            end

            # Otherwise, we perform the usual logic.
            # BDDs do not represent quantitative probabilities. Therefore, for each 
            # different probability `p`, we need to create a new variable in the BDD.
            push!(state.callstack, 1)
            addr = current_bdd_address(state, p, available_information)
            RSDD.set_weight(state.manager, bdd_topvar(addr), 1.0 - p, p)
            pop!(state.callstack)
            return [(Pluck.TRUE_VALUE, addr), (Pluck.FALSE_VALUE, !addr)], state.manager.BDD_TRUE
        end
    end
end

function compile_prim(op::ConstructorEqOp, args, env::Env, available_information::BDD, state::LazyKCState)
    # Evaluate both arguments.
    first_arg_results, first_arg_used_information = traced_compile_inner(args[1], env, available_information, state, 0)
    bind_monad(first_arg_results, available_information, first_arg_used_information, state) do arg1, arg1_guard
        second_arg_results, second_arg_used_information = traced_compile_inner(args[2], env, arg1_guard & available_information, state, 1)
        bind_monad(second_arg_results, available_information, second_arg_used_information, state) do arg2, arg2_guard
            if arg1.constructor == arg2.constructor
                return [(Pluck.TRUE_VALUE, state.manager.BDD_TRUE)], state.manager.BDD_TRUE
            else
                return [(Pluck.FALSE_VALUE, state.manager.BDD_TRUE)], state.manager.BDD_TRUE
            end
        end
    end
end

function compile_prim(op::MkIntOp, args, env::Env, available_information::BDD, state::LazyKCState)
    bitwidth = args[1]::RawInt
    val = args[2]::RawInt
    bools = digits(Bool, val.val, base = 2, pad = bitwidth.val)
    bits = map(b -> b ? state.manager.BDD_TRUE : state.manager.BDD_FALSE, bools)

    return [(IntDist(bits), state.manager.BDD_TRUE)], state.manager.BDD_TRUE
end

function compile_prim(op::IntDistEqOp, args, env::Env, available_information::BDD, state::LazyKCState)
    first_int_dist, first_used_information = traced_compile_inner(args[1], env, available_information, state, 0)
    bind_monad(first_int_dist, available_information, first_used_information, state) do first_int_dist, first_int_dist_guard
        second_int_dist, second_used_information = traced_compile_inner(args[2], env, first_int_dist_guard & available_information, state, 1)
        bind_monad(second_int_dist, available_information, second_used_information, state) do second_int_dist, second_int_dist_guard
            bdd = int_dist_eq(first_int_dist, second_int_dist, state)
            # do we put second_int_dist_guard anywhere?
            return [(Pluck.TRUE_VALUE, bdd), (Pluck.FALSE_VALUE, !bdd)], state.manager.BDD_TRUE
        end
    end
end
