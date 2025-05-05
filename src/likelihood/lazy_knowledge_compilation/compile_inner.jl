#################################
#### COMPILE IMPLEMENTATIONS ####
#################################

function compile_inner(expr::PExpr{App}, env, path_condition, state)
    # println("compile_inner App: $expr with args $(expr.args[2])")
    thunked_argument = make_thunk(expr.args[2], env, 1, state)

    return bind_compile(expr.args[1], env, path_condition, state, 0) do f, path_condition
        @assert f isa Closure "App must be applied to a Closure, got $(f) :: $(typeof(f)) at $(expr)"
        new_env = copy(f.env)
        pushfirst!(new_env, thunked_argument)
        return traced_compile_inner(f.expr, new_env, path_condition, state, 2)
    end
end

function compile_inner(expr::PExpr{Abs}, env, path_condition, state)
    # A lambda term deterministically evaluates to a closure.
    return pure_monad(Closure(expr.args[1], env), path_condition, state)
end

function compile_inner(expr::PExpr{Construct}, env, path_condition, state)
    # Constructors deterministically evaluate to a WHNF value, with their arguments thunked.
    # Create a thunk for each argument.
    # println("compile_inner Construct: $expr with args $(expr.args[2])")
    thunked_arguments = [make_thunk(arg, env, i, state) for (i, arg) in enumerate(expr.args)]
    # Return the constructor and its arguments.
    return pure_monad(Value(expr.head.constructor, thunked_arguments), path_condition, state)
end

function compile_inner(expr::PExpr{CaseOf}, env, path_condition, state)
    # caseof_type = type_of_constructor[first(keys(expr.cases))]
    bind_compile(getscrutinee(expr), env, path_condition, state, 0) do scrutinee, path_condition
        # value_type = type_of_constructor[scrutinee.constructor]
        # if !isempty(expr.cases) && !(value_type == caseof_type)
            # @warn "TypeError: Scrutinee constructor $(scrutinee.constructor) of type $value_type is not the same as the case statement type $caseof_type"
        # end

        @assert scrutinee isa Value "caseof must be applied to a Value, not: $scrutinee :: $(typeof(scrutinee)) in $expr"

        idx = findfirst(g -> g.constructor == scrutinee.constructor, expr.head.branches)
        
        if isnothing(idx)
            # println("Scrutinee not in case expression: $(scrutinee) in $(expr)")
            return program_error_worlds(state)
        end

        case_expr = getbranch(expr, idx)
        @assert length(scrutinee.args) == length(getguard(expr, idx).args)

        # In each of the scrutinee arguments, filter out options that contradict the available information.
        new_env = isempty(scrutinee.args) ? env : copy(env)
        for arg in scrutinee.args
            pushfirst!(new_env, arg)
        end
        return traced_compile_inner(case_expr, new_env, path_condition, state, idx)
    end
end

function compile_inner(expr::PExpr{Y}, env, path_condition, state)
    @assert expr.args[1] isa PExpr{Abs} && expr.args[1].args[1] isa PExpr{Abs} "y-combinator must be applied to a double-lambda"
    closure = Pluck.make_self_loop(expr.args[1].args[1].args[1], env)
    return pure_monad(closure, path_condition, state)
end

function compile_inner(expr::PExpr{Var}, env, path_condition, state)

    v = env[expr.head.idx]
    if v isa Thunk
        return evaluate(v, path_condition, state)
    end

    return pure_monad(v, path_condition, state)
end

function compile_inner(expr::PExpr{Defined}, env, path_condition, state)
    # Execute Defined with a blanked out environment.
    return traced_compile_inner(Pluck.lookup(expr.head.name).expr, Pluck.EMPTY_ENV, path_condition, state, 0)
end


################################
#### PRIMOP IMPLEMENTATIONS ####
################################

function compile_inner(expr::PExpr{FlipOp}, env, path_condition, state)

    bind_compile(expr.args[1], env, path_condition, state, 0) do p, path_condition
        p = p.value
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

function compile_inner(expr::PExpr{FlipOpDual}, env, path_condition, state)
    npartials = state.manager.vector_size

    p_init = 0.5
    # All we want to do is update a dictionary in BDDEvalState saying that bdd_topvar(addr) is associated with args[1].metaparam
    bind_compile(expr.args[1], env, path_condition, state, 0) do metaparam, path_condition
        metaparam = metaparam.value
        if state.cfg.max_depth !== nothing && state.depth > state.cfg.max_depth && state.cfg.sample_after_max_depth && !haskey(state.var_of_callstack, (state.callstack, p))
            sampled_value = rand() < p ? Pluck.TRUE_VALUE : Pluck.FALSE_VALUE
            return [(sampled_value, state.manager.BDD_TRUE)], state.manager.BDD_TRUE
        end
        push!(state.callstack, 1)
        addr = current_address(state, p_init)
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

function compile_inner(expr::PExpr{NativeEqOp}, env, path_condition, state)
    # Evaluate both arguments.
    bind_compile(expr.args[1], env, path_condition, state, 0) do arg1, path_condition
        bind_compile(expr.args[2], env, path_condition, state, 1) do arg2, path_condition
            val = arg1.value == arg2.value ? Pluck.TRUE_VALUE : Pluck.FALSE_VALUE
            return pure_monad(val, path_condition, state)
        end
    end
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
            return pure_monad(Value(:PBool, p_true_thunk, true_thunk), path_condition, state)
        elseif cond.constructor == :False
            return pure_monad(Value(:PBool, p_true_thunk, false_thunk), path_condition, state)
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



"""
compile_inner on an EvalOp always takes a NativeValue{PExpr} and runs it.



Remember that NativeValue{PExpr} have arguments that are themselves NativeValue{PExpr}s
because of how Quote creates thunked Quotes for each argument and quotes always produces
NativeValue{PExpr}s.
"""
function compile_inner(expr::PExpr{EvalOp}, env, path_condition, state)
    bind_compile(expr.args[1], env, path_condition, state, 0) do e, path_condition
        @assert e isa NativeValue && e.value isa PExpr "EvalOp must be applied to a PExpr, got $(e) :: $(typeof(e))"
        return traced_compile_inner(e.value, env, path_condition, state, 1)
    end
end

# function thunk_eval(e::PExpr, env, i::Int, state)
#     return make_thunk(EvalOp(e), env, i, state), i + 1
# end

# function thunk_eval(xs::Vector, env, i::Int, state)
#     res = Any[] # cant be a map bc of `i` scoping
#     for x in xs
#         x, i = thunk_eval(x, env, i, state)
#         push!(res, x)
#     end
#     return res, i
# end

# function thunk_eval(xs::Tuple, env, i::Int, state)
#     xs, i = thunk_eval(collect(xs), env, i, state)
#     return Tuple(xs), i
# end

# function thunk_eval(x, env, i::Int, state)
#     return x, i
# end



# function compile_inner(expr::PExpr{Quote}, env, path_condition, state)
#     # quoting makes a thunk because internal unquotes need to be evaluated in the future
#     return NativeValue(make_thunk(ConstNative(expr.args[1]), env, 0, state))
# end


# function compile_inner(expr::PExpr{EvalOp}, env, path_condition, state)
#     # force the expr to a Value, then compile the result
#     bind_compile(expr.args[1], env, path_condition, state, 0) do e, path_condition
#         return traced_compile_inner(e, env, path_condition, state, 1)
#     end
# end

# """
# Compiling a thunk means forcing the thunk, then compiling the result
# """
# function compile_inner(thunk::T, env, path_condition, state) where T <: Thunk
#     bind_evaluate(thunk, env, path_condition, state) do expr_val, path_condition
#         return compile_inner(expr_val, env, path_condition, state)
#     end
# end

# """
# Compiling a Value means it must be a Value(:Expr, ...) so we'll build a PExpr then compile that
# """
# function compile_inner(e::Value, env, path_condition, state)
#     @assert e isa Value && e.constructor == :Expr
#     head = e.args[1]
#     args = e.args[2]
#     # force the head
#     println("head: $head")
#     bind_evaluate(head, env, path_condition, state) do head, path_condition
#         println("inside head: $head")
#         @assert head isa NativeValue{Symbol}
#         # force the Cons-list part of the args, but not the elements
#         bind_evaluate_uncons(args, env, path_condition, state) do args, path_condition
#             if head.value == :Construct
#                 bind_evaluate_uncons(args[2], env, path_condition, state) do args_2, path_condition
#                     args = [args[1], args_2]
#                     @show args
#                     new_expr = primop_of_sym[head.value](args...)
#                     return traced_compile_inner(new_expr, env, path_condition, state, 1)    
#                 end
#             end

#             # build a native PExpr object and run it
#             new_expr = primop_of_sym[head.value](args...)
#             return traced_compile_inner(new_expr, env, path_condition, state, 1)
#         end
#     end
# end

# """
# Forces a Cons list to be a native list but doesnt force any elements.
# """
# function bind_evaluate_uncons(cont::F, list_value, env, path_condition, state) where F <: Function
#     bind_evaluate(list_value, env, path_condition, state) do list_value, path_condition
#         list_value.constructor == :Nil && return cont(Any[], path_condition)
#         @assert list_value.constructor == :Cons
#         head = list_value.args[1]
#         tail = list_value.args[2]
#         bind_evaluate_uncons(tail, env, path_condition, state) do tail_list, path_condition
#             return cont(Any[head; tail_list], path_condition)
#         end
#     end
# end

# function uncons(list_value::Value)
#     list_value.constructor == :Nil && return Any[]
#     @assert list_value.constructor == :Cons
#     return [list_value.args[1]; uncons(list_value.args[2])]
# end
