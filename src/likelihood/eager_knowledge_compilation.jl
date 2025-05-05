
export bdd_forward_strict, BDDStrictEvalState

# Representations of values:
# - Closure: a list of guarded Closure objects, which each store a body and an environment.
# - Float64: floats and BDDs.
# - Value: a list of possible constructors, each guarded by a BDD, and each with a list of arguments, themselves values.

mutable struct BDDStrictEvalState
    manager::RSDD.Manager
    depth::Int
    max_depth::Union{Int, Nothing}
    sample_after_max_depth::Bool
    num_forward_calls::Int
    function BDDStrictEvalState(;
        max_depth::Union{Int, Nothing} = nothing,
        sample_after_max_depth::Bool = false,
    )
        manager = RSDD.Manager()
        state = new(
            manager,
            0,
            max_depth,
            sample_after_max_depth,
            0,
        )
        return state
    end
end


function traced_bdd_forward(expr::PExpr, env::Env, state::BDDStrictEvalState)
    if state.max_depth !== nothing && state.depth > state.max_depth && !state.sample_after_max_depth
        return []
    end
    state.depth += 1
    result = bdd_forward(expr, env, state)
    state.num_forward_calls += 1
    state.depth -= 1
    return result
end


# What if, everywhere that we currently use (value, guard) tuples, we instead use 
# (which, options)? These could still end up slightly nested: (which_constructor, [Nil, Cons (which_car_thunk, car_thunks) (which_cdr_thunk, cdr_thunks)]).
# Now, ite(guard, val1, val2) creates a new value... oh, but the thunks are annoying because they don't have a fixed number or order, like the constructors do.
# We could do a little + circuit where you + on the length of the options... but not really b/c some options might be in common in a merge.

function merge_values(values::Vector{Tuple{Value, BDD}})
    length(values) == 0 && return []
    length(values) == 1 && return values

    results_for_constructor = Dict{Symbol, Vector{Tuple{Value, BDD}}}()
    for (value, guard) in values
        if !haskey(results_for_constructor, value.constructor)
            results_for_constructor[value.constructor] = [(value, guard)]
        else
            push!(results_for_constructor[value.constructor], (value, guard))
        end
    end
    final_results = Vector{Tuple{Value, BDD}}()
    for (constructor, results) in pairs(results_for_constructor)
        length(results) == 1 && begin
            push!(final_results, results[1])
            continue
        end
        #println("BDD sizes: $([(Int(RSDD.bdd_size(bdd))) for (_, bdd) in results])")
        overall_guard = reduce(|, [bdd for (_, bdd) in results])
        #println("BDDs: $([repr(bdd) for (_, bdd) in results])")
        args_to_merge = Vector{Tuple{Value, BDD}}[]
        for arg = 1:length(args_of_constructor[constructor])
            push!(args_to_merge, Tuple{Value, BDD}[])
            for (result, outer_guard) in results
                for (concrete_result, concrete_guard) in result.args[arg]
                    push!(args_to_merge[end], (concrete_result, outer_guard & concrete_guard))
                end
            end
        end
        overall_args = [merge_values(args_to_merge[i]) for i = 1:length(args_of_constructor[constructor])]
        overall_value = Value(constructor, overall_args)
        push!(final_results, (overall_value, overall_guard))
    end
    return final_results
end


function combine_results(result_sets, state::BDDStrictEvalState)
    join_results = Vector{World}()
    index_of_result = Dict{Union{Value, Closure, Float64}, Int}()
    results_to_merge = Tuple{Value, BDD}[]
    results_to_merge_int_dist = Tuple{IntDist, BDD}[]

    for (results, outer_guard) in result_sets
        for (result, inner_guard) in results
            inner_and_outer = inner_guard & outer_guard
            if result isa Closure || result isa Float64
                result_index = Base.get!(index_of_result, result, length(join_results) + 1)
                if result_index > length(join_results)
                    push!(join_results, (result, inner_and_outer))
                else
                    new_guard = join_results[result_index][2] | (inner_and_outer)
                    join_results[result_index] = (join_results[result_index][1], new_guard)
                end
            elseif result isa Value
                push!(results_to_merge, (result, inner_and_outer))
            elseif result isa IntDist
                push!(results_to_merge_int_dist, (result, inner_and_outer))
            else
                @assert false "combine_results found a result that is not a Value, Closure, or Float64: $result"
            end
        end
    end
    push!(join_results, merge_values(results_to_merge)...)
    push!(join_results, merge_int_dists(results_to_merge_int_dist, state)...)
    return join_results
end

function merge_int_dists(results_to_merge_int_dist::Vector{Tuple{IntDist, BDD}}, state::BDDStrictEvalState)
    if length(results_to_merge_int_dist) == 0
        return []
    end
    width = length(results_to_merge_int_dist[1][1].bits)
    result = IntDist(fill(state.manager.BDD_FALSE, width))
    overall_guard = state.manager.BDD_FALSE
    for (int_dist, guard) in results_to_merge_int_dist
        overall_guard = overall_guard | guard
        @assert width == length(int_dist.bits)
        for i = 1:width
            @inbounds new_bit = int_dist.bits[i] & guard
            @inbounds result.bits[i] = result.bits[i] | new_bit
        end
    end
    return [(result, overall_guard)]
end


function bdd_forward(expr::PExpr, env::Env, state::BDDStrictEvalState)
    error("bdd_forward not implemented for $(typeof(expr))")
end

function bdd_bind(cont, first_stage_results, state::BDDStrictEvalState)
    return combine_results([(cont(result, result_guard), result_guard)
                            for (result, result_guard) in first_stage_results], state)
end

function bdd_forward(expr::PExpr{App}, env::Env, state::BDDStrictEvalState)
    fs = traced_bdd_forward(expr.args[1], env, state)
    arg = traced_bdd_forward(expr.args[2], env, state)

    return bdd_bind(fs, state) do f, f_guard
        new_env = copy(f.env)
        pushfirst!(new_env, arg)
        return traced_bdd_forward(f.expr, new_env, state)
    end
end

function bdd_forward(expr::PExpr{Abs}, env::Env, state::BDDStrictEvalState)
    # A lambda term deterministically evaluates to a closure.
    return [(Closure(expr.args[1], env), state.manager.BDD_TRUE)]
end

function bdd_forward(expr::PExpr{Construct}, env::Env, state::BDDStrictEvalState)
    # Evaluate each argument.
    evaluated_arguments = [traced_bdd_forward(arg, env, state) for arg in expr.args[1]]
    # Return the constructor and its arguments.
    return [(Value(expr.constructor, evaluated_arguments), state.manager.BDD_TRUE)]
end

function bdd_forward(expr::PExpr{CaseOf}, env::Env, state::BDDStrictEvalState)

    scrutinee_values = traced_bdd_forward(expr.args[1], env, state)

    bdd_bind(scrutinee_values, state) do scrutinee, scrutinee_guard
        idx = findfirst(c -> c[1] == scrutinee.constructor, expr.args[2])
        if !isnothing(idx)
            case_expr = expr.args[2][idx][2]
            num_args = length(args_of_constructor[scrutinee.constructor])
            if num_args == 0
                return traced_bdd_forward(case_expr, env, state)
            else
                for _ = 1:num_args
                    @assert case_expr isa PExpr{Abs} "case expression branch for constructor $(scrutinee.constructor) must have as many lambdas as the constructor has arguments ($(num_args) arguments)"
                    case_expr = case_expr.args[1]
                end
                # In each of the scrutinee arguments, filter out options that contradict the available information.
                new_env = copy(env)
                for (arg) in scrutinee.args
                    pushfirst!(new_env, arg)
                end
                return traced_bdd_forward(case_expr, new_env, state)
            end
        else
            return []
        end
    end
end

function bdd_forward(expr::PExpr{Y}, env::Env, state::BDDStrictEvalState)
    rec_lambda = expr.args[1] :: PExpr{Abs}
    arg_lambda = rec_lambda.args[1] :: PExpr{Abs}

    closure = make_self_loop(arg_lambda.args[1], env, rec_lambda.head.name, arg_lambda.head.name)

    # set up a closure with a circular reference
    return [(closure, state.manager.BDD_TRUE)]
end


function bdd_prim_forward(expr::PExpr{MkIntOp}, env::Env, state::BDDStrictEvalState)
    bitwidth = expr.args[1]::ConstNative
    val = expr.args[2]::ConstNative
    bools = digits(Bool, val.value, base = 2, pad = bitwidth.value)
    bits = map(b -> b ? state.manager.BDD_TRUE : state.manager.BDD_FALSE, bools)

    return [(IntDist(bits), state.manager.BDD_TRUE)]
end


function bdd_prim_forward(expr::PExpr{IntDistEqOp}, env::Env, state::BDDStrictEvalState)
    first_int_dist = traced_bdd_forward(expr.args[1], env, state)
    bdd_bind(first_int_dist, state) do first_int_dist, first_int_dist_guard
        second_int_dist = traced_bdd_forward(expr.args[2], env, state)
        bdd_bind(second_int_dist, state) do second_int_dist, second_int_dist_guard
            bdd = int_dist_eq(first_int_dist, second_int_dist, state.manager)
            # do we put second_int_dist_guard anywhere?
            return [(Pluck.TRUE_VALUE, bdd), (Pluck.FALSE_VALUE, !bdd)]
        end
    end
end

function bdd_prim_forward(expr::PExpr{FlipOp}, env::Env, state::BDDStrictEvalState)
    ps = traced_bdd_forward(expr.args[1], env, state)
    bdd_bind(ps, state) do p, p_guard
        if isapprox(p, 0.0)
            return [(Pluck.FALSE_VALUE, p_guard)]
        elseif isapprox(p, 1.0)
            return [(Pluck.TRUE_VALUE, p_guard)]
        else
            # If we are past the max depth, AND we are sampling after the max depth, AND 
            # this flip is new (not previously instantiated), THEN sample a value.
            if state.max_depth !== nothing && state.depth > state.max_depth && state.sample_after_max_depth
                sampled_value = rand() < p ? Pluck.TRUE_VALUE : Pluck.FALSE_VALUE
                return [(sampled_value, state.manager.BDD_TRUE)]
            end

            # Otherwise, we perform the usual logic.
            # BDDs do not represent quantitative probabilities. Therefore, for each 
            # different probability `p`, we need to create a new variable in the BDD.
            addr = bdd_new_var(state.manager, true)
            RSDD.set_weight(state.manager, bdd_topvar(addr), 1.0 - p, p)
            return [(Pluck.TRUE_VALUE, addr), (Pluck.FALSE_VALUE, !addr)]
        end
    end
end

function bdd_prim_forward(expr::PExpr{NativeEqOp}, env::Env, state::BDDStrictEvalState)
    # Evaluate both arguments.
    first_arg_results = traced_bdd_forward(expr.args[1], env, state)
    bdd_bind(first_arg_results, state) do arg1, arg1_guard
        second_arg_results = traced_bdd_forward(expr.args[2], env, state)
        bdd_bind(second_arg_results, state) do arg2, arg2_guard
            if arg1.value == arg2.value
                return [(Pluck.TRUE_VALUE, state.manager.BDD_TRUE)]
            else
                return [(Pluck.FALSE_VALUE, state.manager.BDD_TRUE)]
            end
        end
    end
end

function bdd_forward(expr::PExpr{Var}, env::Env, state::BDDStrictEvalState)
    # Look up the variable in the environment.
    if expr.args[1] > length(env)
        @warn "Variable $expr not found in environment; shaving off probability."
        return []
    end

    if env[expr.args[1]] isa Closure
        return [(env[expr.args[1]], state.manager.BDD_TRUE)]
    end
    return env[expr.args[1]]
end

function bdd_forward(expr::PExpr{Defined}, env::Env, state::BDDStrictEvalState)
    # Execute Defined with a blanked out environment.
    return traced_bdd_forward(Pluck.lookup(expr.args[1]).expr, Pluck.EMPTY_ENV, state)
end

function bdd_forward_strict(expr; show_bdd = false, show_bdd_size = false, record_bdd_json = false, state = BDDStrictEvalState())
    if expr isa String
        expr = parse_expr(expr)
    end
    inner_ret = traced_bdd_forward(expr, Pluck.EMPTY_ENV, state)
    
    # When ret contains IntDists, enumerate the 2^n options
    ret = []
    for (val, bdd) in inner_ret
        if val isa IntDist
            append!(ret, enumerate_int_dist(val, bdd))
        else
            push!(ret, (val, bdd))
        end
    end

    if show_bdd_size
        summed_size = sum(Int(RSDD.bdd_size(bdd)) for (ret, (bdd)) in ret)
        num_vars = length(state.sorted_callstacks)
        printstyled("vars: $num_vars nodes: $summed_size\n"; color=:blue)
        println("BDD sizes: $([(ret, Int(RSDD.bdd_size(bdd))) for (ret, (bdd)) in ret])")
    end

    if record_bdd_json
        bdd = get_true_result(results, nothing)
        if isnothing(bdd)
            @warn "No true result found to record"
        else
            record_bdd(state, bdd)
        end
    end

    # Trying a model count of each possibility.
    results = [(v, RSDD.bdd_wmc(bdd)) for (v, bdd) in ret]

    free_bdd_manager(state.manager)
    return results
end
