#################################
#### COMPILE IMPLEMENTATIONS ####
#################################

function compile_inner(expr::PExpr{App}, env, path_condition, state)
    # println("compile_inner App: $expr with args $(expr.args[2])")
    thunked_argument = make_thunk(expr.args[2], env, 1, state)

    return bind_compile(expr.args[1], env, path_condition, state, 0) do f, path_condition
        f isa Closure || pluck_error(state, "App must be applied to a Closure, got $(f) :: $(typeof(f)) at $(expr)")
        new_env = EnvCons(f.name, thunked_argument, f.env)
        return traced_compile_inner(f.expr, new_env, path_condition, state, 2)
    end
end

function compile_inner(expr::PExpr{Abs}, env, path_condition, state)
    # A lambda term deterministically evaluates to a closure.
    return pure_monad(Closure(expr.args[1], env, expr.head.var), path_condition, state)
end

function compile_inner(expr::PExpr{Construct}, env, path_condition, state)
    # Constructors deterministically evaluate to a WHNF value, with their arguments thunked.
    # Create a thunk for each argument.
    # println("compile_inner Construct: $expr with args $(expr.args[2])")
    thunked_arguments = [make_thunk(arg, env, i, state) for (i, arg) in enumerate(expr.args)]
    # Return the constructor and its arguments.
    return pure_monad(Value(expr.head.constructor, thunked_arguments), path_condition, state)
end

function pluck_error(state, msg)
    printstyled("Pluck Error: ", color=:red)
    println(msg)
    println("\nDuring execution of $(state.query)\n")

    if state.cfg.stacktrace
        print_stacktrace(state)
    else
        println("Run with stacktrace=true to see the full Pluck stacktrace")
    end

    println()
    throw(ErrorException("Pluck Error"))
end

function print_stacktrace(state)
    println("Stacktrace:")
    for (i, e) in enumerate(reverse(state.stacktrace))
        ty = typeof(e).parameters[1]
        println("  [$i] $e :: $ty")
    end
end


function compile_inner(expr::PExpr{CaseOf}, env, path_condition, state)
    # caseof_type = type_of_constructor[first(keys(expr.cases))]
    bind_compile(getscrutinee(expr), env, path_condition, state, 0) do scrutinee, path_condition
        # value_type = type_of_constructor[scrutinee.constructor]
        # if !isempty(expr.cases) && !(value_type == caseof_type)
            # @warn "TypeError: Scrutinee constructor $(scrutinee.constructor) of type $value_type is not the same as the case statement type $caseof_type"
        # end

        scrutinee isa Value || pluck_error(state, "caseof must be applied to a Value, not: $scrutinee :: $(typeof(scrutinee)) in $expr")

        idx = findfirst(g -> g.constructor == scrutinee.constructor, expr.head.branches)
        
        if isnothing(idx)
            # println("Scrutinee not in case expression: $(scrutinee) in $(expr)")
            return program_error_worlds(state)
        end

        case_expr = getbranch(expr, idx)
        @assert length(scrutinee.args) == length(getguard(expr, idx).args)

        # In each of the scrutinee arguments, filter out options that contradict the available information.
        for (arg, name) in zip(scrutinee.args, getguard(expr, idx).args)
            env = EnvCons(name, arg, env)
        end
        return traced_compile_inner(case_expr, env, path_condition, state, idx)
    end
end

function compile_inner(expr::PExpr{Y}, env, path_condition, state)
    rec_lambda = expr.args[1] :: PExpr{Abs}
    arg_lambda = rec_lambda.args[1] :: PExpr{Abs}
    closure = make_self_loop(arg_lambda.args[1], env, rec_lambda.head.var, arg_lambda.head.var)

    return pure_monad(closure, path_condition, state)
end

function compile_inner(expr::PExpr{Var}, env, path_condition, state)

    v = getenv(env, expr.head.name)
    if v isa Thunk
        return evaluate(v, path_condition, state)
    end

    return pure_monad(v, path_condition, state)
end

function compile_inner(expr::PExpr{Defined}, env, path_condition, state)
    # Execute Defined with a blanked out environment.
    # if state.cfg.stacktrace
    #     push!(state.stacktrace, expr)
    # end
    res = traced_compile_inner(Pluck.lookup(expr.head.name).expr, Pluck.EMPTY_ENV, path_condition, state, 0)
    # if state.cfg.stacktrace
    #     pop!(state.stacktrace)
    # end
    return res
end


################################
#### PRIMOP IMPLEMENTATIONS ####
################################

function compile_inner(expr::PExpr{FlipOp}, env, path_condition, state)
    npartials = state.manager.vector_size

    bind_compile(expr.args[1], env, path_condition, state, 0) do p, path_condition
        p = p.value

        if p isa Int
            @assert state.cfg.dual "FlipOp must be applied to a Float unless in dual mode. Got $(p) :: $(typeof(p)) in $expr"
            metaparam = p
            p = 0.5 # default value used in dual mode, can swap out for another later

            push!(state.callstack, 1)
            addr = current_address(state, p)    
            topvar = bdd_topvar(addr)
            state.var2metaparam[topvar] = metaparam
            partials_hi = zeros(Float64, npartials)
            partials_hi[metaparam+1] = 1.0
            partials_lo = zeros(Float64, npartials)
            partials_lo[metaparam+1] = -1.0
            set_weight_deriv(state.manager.weights, topvar, 1 - p, partials_lo, p, partials_hi)
            pop!(state.callstack)
            return if_then_else_monad(Pluck.TRUE_VALUE, Pluck.FALSE_VALUE, addr, path_condition, state)
        end

        isapprox(p, 0.0) && return pure_monad(Pluck.FALSE_VALUE, path_condition, state)
        isapprox(p, 1.0) && return pure_monad(Pluck.TRUE_VALUE, path_condition, state)

        # If we are past the max depth, AND we are sampling after the max depth, AND 
        # this flip is new (not previously instantiated), THEN sample a value.
        if state.cfg.max_depth !== nothing && state.depth > state.cfg.max_depth && state.cfg.sample_after_max_depth && !haskey(state.var_of_callstack, (state.callstack, p))
            sampled_value = rand() < p ? Pluck.TRUE_VALUE : Pluck.FALSE_VALUE
            return pure_monad(sampled_value, path_condition, state)
        end

        # Otherwise, we perform the usual logic.
        # BDDs do not represent quantitative probabilities. Therefore, for each 
        # different probability `p`, we need to create a new variable in the BDD.
        push!(state.callstack, 1)
        addr = current_address(state, p)

        RSDD.set_weight(state.manager, bdd_topvar(addr), 1.0 - p, p)
        pop!(state.callstack)
        return if_then_else_monad(Pluck.TRUE_VALUE, Pluck.FALSE_VALUE, addr, path_condition, state)
    end
end

"""
Compile a unary native operation.
"""
function compile_native_unop(f::F, expr::PExpr{T}, env, path_condition, state) where {T <: Head, F <: Function}
    bind_compile(expr.args[1], env, path_condition, state, 0) do arg1, path_condition
        val = f(arg1.value)
        return pure_monad(NativeValue(val), path_condition, state)
    end
end

"""
Compile a binary native operation.
"""
function compile_native_binop(f::F, expr::PExpr{T}, env, path_condition, state) where {T <: Head, F <: Function}
    bind_compile(expr.args[1], env, path_condition, state, 0) do arg1, path_condition
        bind_compile(expr.args[2], env, path_condition, state, 1) do arg2, path_condition
            val = f(arg1.value, arg2.value)
            return pure_monad(NativeValue(val), path_condition, state)
        end
    end
end

function compile_inner(expr::PExpr{NativeEqOp}, env, path_condition, state)
    bind_compile(expr.args[1], env, path_condition, state, 0) do arg1, path_condition
        bind_compile(expr.args[2], env, path_condition, state, 1) do arg2, path_condition
            return pure_monad(arg1.value == arg2.value ? Pluck.TRUE_VALUE : Pluck.FALSE_VALUE, path_condition, state)
        end
    end
end

function compile_inner(expr::PExpr{FDivOp}, env, path_condition, state)
    compile_native_binop(/, expr, env, path_condition, state)
end

function compile_inner(expr::PExpr{FMulOp}, env, path_condition, state)
    compile_native_binop(*, expr, env, path_condition, state)
end

function compile_inner(expr::PExpr{FAddOp}, env, path_condition, state)
    compile_native_binop(+, expr, env, path_condition, state)
end

function compile_inner(expr::PExpr{FSubOp}, env, path_condition, state)
    compile_native_binop(-, expr, env, path_condition, state)
end

function compile_inner(expr::PExpr{ErrorOp}, env, path_condition, state)
    error("ErrorOp: $expr")
end




"""
Given a Value, returns a Cons-list of its arguments.
"""
function compile_inner(expr::PExpr{GetArgsOp}, env, path_condition, state)
    bind_compile(expr.args[1], env, path_condition, state, 0) do val, path_condition
        res = Value(:Nil)
        for arg in reverse(val.args)
            res = Value(:Cons, [arg, res])
        end
        return pure_monad(res, path_condition, state)
    end
end

function compile_inner(expr::PExpr{GetConstructorOp}, env, path_condition, state)
    bind_compile(expr.args[1], env, path_condition, state, 0) do val, path_condition
        @assert val isa Value "getconstructor must be applied to a Value, not: $val :: $(typeof(val)) in $expr during execution of $(state.query)"
        return pure_monad(NativeValue(val.constructor), path_condition, state)
    end
end

function compile_inner(expr::PExpr{ConstNative}, env, path_condition, state)
    return pure_monad(NativeValue(expr.head.val), path_condition, state)
end

function compile_inner(expr::PExpr{MkIntOp}, env, path_condition, state)
    bitwidth = expr.args[1]::ConstNative
    val = expr.args[2]::ConstNative
    bools = digits(Bool, val.value, base = 2, pad = bitwidth.value)
    bits = map(b -> b ? state.manager.BDD_TRUE : state.manager.BDD_FALSE, bools)

    return pure_monad(IntDist(bits), path_condition, state)
end

function compile_inner(expr::PExpr{IntDistEqOp}, env, path_condition, state)
    bind_compile(expr.args[1], env, path_condition, state, 0) do first_int_dist, path_condition
        bind_compile(expr.args[2], env, path_condition, state, 1) do second_int_dist, path_condition
            bdd = int_dist_eq(first_int_dist, second_int_dist, state)
            return if_then_else_monad(Pluck.TRUE_VALUE, Pluck.FALSE_VALUE, bdd, path_condition, state)
        end
    end
end

function compile_inner(expr::PExpr{PBoolOp}, env, path_condition, state)
    cond = traced_compile_inner(expr.args[1], env, path_condition, state, 0)

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

    p_true_thunk = make_thunk(ConstNative(exp(p_true - logtotal))(), Pluck.EMPTY_ENV, 1, state)
    true_thunk = make_thunk(Construct(:True)(), Pluck.EMPTY_ENV, 2, state)
    false_thunk = make_thunk(Construct(:False)(), Pluck.EMPTY_ENV, 3, state)
    bind_monad(cond, path_condition, state) do cond, path_condition
        if cond.constructor == :True
            return pure_monad(Value(:PBool, Any[p_true_thunk, true_thunk]), path_condition, state)
        elseif cond.constructor == :False
            return pure_monad(Value(:PBool, Any[p_true_thunk, false_thunk]), path_condition, state)
        else
            error("PBoolOp: condition must be a boolean, got $(cond)")
        end
    end
end

function compile_inner(expr::PExpr{PrintOp}, env, path_condition, state)
    return traced_compile_inner(expr.args[1], env, path_condition, state, 0)
end

function compile_inner(expr::PExpr{Unquote}, env, path_condition, state)
    error("Unquote not inside a Quote: $expr")
end

"""
compile_inner on a Quote always produces a PExprValue
compile_inner(Quote(e)) -> PExprValue(e.head, thunk_quote(e.args)) where any args that are PExprs get replaced with thunks of quoted PExprs.
compile_inner(Quote(e)) -> PExprValue(e.head, thunk_quote(e.args)) where any args that are PExprs get replaced with thunks of quoted PExprs.
compile_inner(Quote(Unquote(e))) -> compile_inner(e) :: NativeValue{PExpr}
"""
function compile_inner(expr::PExpr{Quote}, env, path_condition, state)
    quoted_expr = expr.args[1]::PExpr

    # forcing a quote of an unquote causes the contents of the unquote to evaluate
    if quoted_expr isa PExpr{Unquote}
        quoted_unquoted_expr = quoted_expr.args[1]
        return bind_compile(quoted_unquoted_expr, env, path_condition, state, 0) do e, path_condition
            # this bind is unnecessary, I'm just doing it to check the type during debugging
            # @assert e isa PExprValue
            @assert e isa NativeValue && e.value isa PExpr
            return pure_monad(e, path_condition, state)
        end
    end

    # forcing a quote of a non-unquote just returns the underlying PExpr with all the args quoted (and thunked)
    quoted_args = Any[]
    for (i, arg) in enumerate(quoted_expr.args)
        push!(quoted_args, make_thunk(Quote()(arg), env, i, state))
    end

    return pure_monad(NativeValue(PExpr(quoted_expr.head, quoted_args)), path_condition, state)
    # return pure_monad(PExprValue(quoted_expr.head, quoted_args), path_condition, state)
end



function compile_inner(expr::PExpr{EvalOp}, env, path_condition, state)
    bind_compile(expr.args[1], env, path_condition, state, 0) do e, path_condition
        @assert e isa NativeValue && e.value isa PExpr "EvalOp must be applied to a PExpr, got $(e) :: $(typeof(e))"
        return traced_compile_inner(e.value, env, path_condition, state, 1)
    end
end
