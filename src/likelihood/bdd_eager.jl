using .RSDD

export bdd_forward_strict, BDDStrictEvalState

# Representations of values:
# - Closure: a list of guarded Closure objects, which each store a body and an environment.
# - Float64: floats and BDDs.
# - Value: a list of possible constructors, each guarded by a BDD, and each with a list of arguments, themselves values.

mutable struct BDDStrictEvalState
    weights::WmcParams
    manager::RSDD.Manager
    BDD_TRUE::BDD
    BDD_FALSE::BDD
    depth::Int
    max_depth::Union{Int, Nothing}
    sample_after_max_depth::Bool
    num_forward_calls::Int
    function BDDStrictEvalState(;
        max_depth::Union{Int, Nothing} = nothing,
        sample_after_max_depth::Bool = false,
    )
        manager = RSDD.mk_bdd_manager_default_order(0)
        BDD_TRUE = RSDD.bdd_true(manager)
        BDD_FALSE = RSDD.bdd_false(manager)
        weights = RSDD.new_wmc_params_f64()
        state = new(
            weights,
            manager,
            BDD_TRUE,
            BDD_FALSE,
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


# function merge_values(values::Vector{Tuple{Value, BDD}})
#     length(values) == 0 && return []
#     length(values) == 1 && return values

#     results_for_constructor = Dict{Symbol, Vector{Tuple{Value, BDD}}}()
#     for (value, guard) in values
#         if !haskey(results_for_constructor, value.constructor)
#             results_for_constructor[value.constructor] = [(value, guard)]
#         else
#             push!(results_for_constructor[value.constructor], (value, guard))
#         end
#     end

#     final_results = Vector{Tuple{Value, BDD}}()


# end


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
        for arg = 1:length(args_of_constructor(constructor))
            push!(args_to_merge, Tuple{Value, BDD}[])
            for (result, outer_guard) in results
                for (concrete_result, concrete_guard) in result.args[arg]
                    push!(args_to_merge[end], (concrete_result, outer_guard & concrete_guard))
                end
            end
        end
        overall_args = [merge_values(args_to_merge[i]) for i = 1:length(args_of_constructor(constructor))]
        overall_value = Value(Pluck.spt_of_constructor[constructor], constructor, overall_args)
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
    result = IntDist(fill(state.BDD_FALSE, width))
    overall_guard = state.BDD_FALSE
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

function bdd_forward(expr::App, env::Env, state::BDDStrictEvalState)
    fs = traced_bdd_forward(expr.f, env, state)
    arg = traced_bdd_forward(expr.x, env, state)

    return bdd_bind(fs, state) do f, f_guard
        new_env = copy(f.env)
        pushfirst!(new_env, arg)
        return traced_bdd_forward(f.expr, new_env, state)
    end
end

function bdd_forward(expr::Abs, env::Env, state::BDDStrictEvalState)
    # A lambda term deterministically evaluates to a closure.
    return [(Closure(expr.body, env), state.BDD_TRUE)]
end

function bdd_forward(expr::Construct, env::Env, state::BDDStrictEvalState)
    # Look up type of this constructor.
    spt = Pluck.spt_of_constructor[expr.constructor]
    # Evaluate each argument.
    evaluated_arguments = [traced_bdd_forward(arg, env, state) for arg in expr.args]
    # Return the constructor and its arguments.
    return [(Value(spt, expr.constructor, evaluated_arguments), state.BDD_TRUE)]
end

function bdd_forward(expr::CaseOf, env::Env, state::BDDStrictEvalState)

    scrutinee_values = traced_bdd_forward(expr.scrutinee, env, state)

    # if length(scrutinee_values) == 0
    #     return []
    # end
    # if length(scrutinee_values) == 1
    #     scrutinee_value, scrutinee_guard = scrutinee_values[1]
    #     if scrutinee_value.constructor in expr.constructors
    #         return traced_bdd_forward(expr.cases[scrutinee_value.constructor], env, state)
    #     else
    #         return []
    #     end
    # end
    # if length(scrutinee_values) == 2
    #     scrutinee_value_1, scrutinee_guard_1 = scrutinee_values[1]
    #     scrutinee_value_2, scrutinee_guard_2 = scrutinee_values[2]
    #     result_value_1 = traced_bdd_forward(expr.cases[scrutinee_value_1.constructor], env, state)
    #     result_value_2 = traced_bdd_forward(expr.cases[scrutinee_value_2.constructor], env, state)

    #     if scrutinee_value_1.constructor in expr.constructors
    #         return traced_bdd_forward(expr.cases[scrutinee_value_1.constructor], env, state)
    #     elseif scrutinee_value_2.constructor in expr.constructors
    #         return traced_bdd_forward(expr.cases[scrutinee_value_2.constructor], env, state)
    #     else
    #         return []
    #     end
    # end

    bdd_bind(scrutinee_values, state) do scrutinee, scrutinee_guard
        if scrutinee.constructor in expr.constructors
            case_expr = expr.cases[scrutinee.constructor]
            num_args = length(args_of_constructor(scrutinee.constructor))
            if num_args == 0
                return traced_bdd_forward(case_expr, env, state)
            else
                for _ = 1:num_args
                    @assert case_expr isa Abs "case expression branch for constructor $(scrutinee.constructor) must have as many lambdas as the constructor has arguments ($(num_args) arguments)"
                    case_expr = case_expr.body
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

function bdd_forward(expr::Y, env::Env, state::BDDStrictEvalState)
    @assert expr.f isa Abs && expr.f.body isa Abs "y-combinator must be applied to a double-lambda"

    closure = Pluck.make_self_loop(expr.f.body.body, env)

    # set up a closure with a circular reference
    return [(closure, state.BDD_TRUE)]
end

function bdd_forward(expr::PrimOp, env::Env, state::BDDStrictEvalState)
    bdd_prim_forward(expr.op, expr.args, env, state)
end


function bdd_prim_forward(op::MkIntOp, args, env::Env, state::BDDStrictEvalState)
    bitwidth = args[1]::RawInt
    val = args[2]::RawInt
    bools = digits(Bool, val.val, base = 2, pad = bitwidth.val)
    bits = map(b -> b ? state.BDD_TRUE : state.BDD_FALSE, bools)

    return [(IntDist(bits), state.BDD_TRUE)]
end


"""
Equality of two int distributions is an AND over the equality (bdd_iff) of each bit.
"""
function int_dist_eq(x::IntDist, y::IntDist, state::BDDStrictEvalState)::BDD
    width = length(x.bits)
    @assert width == length(y.bits)
    result = state.BDD_TRUE
    for i = 1:width
        @inbounds result = result & bdd_iff(x.bits[i], y.bits[i])
        if bdd_is_false(result)
            return state.BDD_FALSE
        end
    end
    return result
end


function bdd_prim_forward(op::IntDistEqOp, args, env::Env, state::BDDStrictEvalState)
    first_int_dist = traced_bdd_forward(args[1], env, state)
    bdd_bind(first_int_dist, state) do first_int_dist, first_int_dist_guard
        second_int_dist = traced_bdd_forward(args[2], env, state)
        bdd_bind(second_int_dist, state) do second_int_dist, second_int_dist_guard
            bdd = int_dist_eq(first_int_dist, second_int_dist, state)
            # do we put second_int_dist_guard anywhere?
            return [(Pluck.TRUE_VALUE, bdd), (Pluck.FALSE_VALUE, !bdd)]
        end
    end
end

function bdd_prim_forward(op::FlipOp, args, env::Env, state::BDDStrictEvalState)
    ps = traced_bdd_forward(args[1], env, state)
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
                return [(sampled_value, state.BDD_TRUE)]
            end

            # Otherwise, we perform the usual logic.
            # BDDs do not represent quantitative probabilities. Therefore, for each 
            # different probability `p`, we need to create a new variable in the BDD.
            addr = bdd_new_var(state.manager, true)
            wmc_param_f64_set_weight(state.weights, bdd_topvar(addr), 1.0 - p, p)
            return [(Pluck.TRUE_VALUE, addr), (Pluck.FALSE_VALUE, !addr)]
        end
    end
end

function bdd_prim_forward(op::ConstructorEqOp, args, env::Env, state::BDDStrictEvalState)
    # Evaluate both arguments.
    first_arg_results = traced_bdd_forward(args[1], env, state)
    bdd_bind(first_arg_results, state) do arg1, arg1_guard
        second_arg_results = traced_bdd_forward(args[2], env, state)
        bdd_bind(second_arg_results, state) do arg2, arg2_guard
            if arg1.constructor == arg2.constructor
                return [(Pluck.TRUE_VALUE, state.BDD_TRUE)]
            else
                return [(Pluck.FALSE_VALUE, state.BDD_TRUE)]
            end
        end
    end
end

function bdd_forward(expr::Var, env::Env, state::BDDStrictEvalState)
    # Look up the variable in the environment.
    if expr.idx > length(env)
        @warn "Variable $expr not found in environment; shaving off probability."
        return []
    end

    if env[expr.idx] isa Closure
        return [(env[expr.idx], state.BDD_TRUE)]
    end
    return env[expr.idx]
end

function bdd_forward(expr::Defined, env::Env, state::BDDStrictEvalState)
    # Execute Defined with a blanked out environment.
    return traced_bdd_forward(Pluck.lookup(expr.name).expr, Pluck.EMPTY_ENV, state)
end

function bdd_forward(expr::Root, env::Env, state::BDDStrictEvalState)
    return bdd_forward(expr.body, env, state)
end

function bdd_forward(expr::ConstReal, env::Env, state::BDDStrictEvalState)
    return [(expr.val, state.BDD_TRUE)]
end

function bdd_forward_strict(expr; show_bdd = false, show_bdd_size = false, record_bdd_json = false, state = BDDStrictEvalState())
    if expr isa String
        expr = parse_expr(expr)
    end
    ret = traced_bdd_forward(expr, Pluck.EMPTY_ENV, state)
    # When ret contains IntDists, enumerate the 2^n options
    enumerated_ret = []
    for (val, bdd) in ret
        if val isa IntDist
            # Enumerate all 2^n possibilities (all setting of n bits)
            for i = 0:(2^length(val.bits)-1)
                bits = digits(Bool, i, base = 2, pad = length(val.bits))
                # Get BDD for this setting of the bits
                # Start with TRUE BDD
                bit_bdd = state.BDD_TRUE

                # For each bit, AND with either the bit's BDD or its negation based on our desired value
                for (bit_idx, bit_val) in enumerate(bits)
                    bit_formula = val.bits[bit_idx]
                    if bit_val
                        bit_bdd = bit_bdd & bit_formula
                    else
                        bit_bdd = bit_bdd & RSDD.bdd_negate(bit_formula)
                    end
                end

                # AND with the original BDD and add to results
                push!(enumerated_ret, (i, bit_bdd & bdd))
            end
        else
            push!(enumerated_ret, (val, bdd))
        end
    end
    ret = enumerated_ret


    # Get bdd size
    if show_bdd_size
        println("BDD sizes: $([(ret, Int(RSDD.bdd_size(bdd))) for (ret, (bdd)) in ret])")
        @show state.num_forward_calls
    end
    # Trying a model count of each possibility.
    if show_bdd
        results = [(v, repr(bdd), RSDD.bdd_wmc(bdd, state.weights)) for (v, bdd) in ret]
    else
        results = [(v, RSDD.bdd_wmc(bdd, state.weights)) for (v, bdd) in ret]
    end

    if record_bdd_json
        println(ret[2][1])
        true_results = findall(x -> x[1] == Pluck.TRUE_VALUE || x[1].constructor == :True, ret)
        @assert length(true_results) == 1 "Expected exactly one true result, got $(length(true_results))"
        record_bdd(state, ret[true_results[1]][2])
    end
    free_bdd_manager(state.manager)
    free_wmc_params(state.weights)
    return results
end
