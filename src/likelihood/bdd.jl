export normalize, bdd_forward, BDDEvalState

# A version of `forward` that works with BDDs.
# Signature for `forward`:
#   Arguments:
#     - expression: a PExpr representing the expression to evaluate.
#     - env: a list of variables that are available in the current environment; most will be thunks.
#     - available_information: a BDD representing what is known to be true along this program path.
#   Returns:
#     - values: a list of (value, BDD) pairs where the values are in WHNF and the BDDs represent the conditions under which the expression evaluates to this value.
#     - used_information: a weaker BDD than the input `available_information`; it is safe to cache these values for reuse whenever the condition represented by `used_information` is true.

# Thunks store:
#   - a PExpr (the body of the thunk)
#   - an environment in which to evaluate the thunk
#   - a cache: pairs (BDD, values_with_bdds), where the values-result is safe to use whenever the corresponding BDD is true.
#   - a callstack: a list of symbols representing the callstack at the point where this thunk was created. Used to determine when to create new logical variables for flip results.
#   - a name: a symbol representing the name of the thunk. Used for debugging and printing.
# When we evaluate a thunk, we first check the cache to see if `available_information` implies any of the BDDs in the cache. If so, we use the cached values, and return the guard BDD as the `used_information`.

using .RSDD


const Callstack = Vector{Int}
const Env = Vector{Any}
const World = Tuple{Any, BDD}
const ForwardResult = Tuple{BDD, Vector{World}}
const EMPTY_ENV::Env = Any[]


struct IntDist
    bits::Vector{BDD}
end
Base.show(io::IO, x::IntDist) = print(io, "IntDist{$(length(x.bits))}")


struct BDDThunk
    expr::PExpr
    env::Env
    cache::Vector{ForwardResult}
    callstack::Callstack
    name::Symbol
    strict_order_index::Int

    function BDDThunk(expr::PExpr, env::Env, callstack::Callstack, name::Symbol, strict_order_index::Int, state)
        if expr isa Var && env[expr.idx] isa BDDThunk
            return env[expr.idx]
        end

        # if expr isa Var && env[expr.idx] isa BDDThunkUnion
        #     return env[expr.idx]
        # end

        key = (expr, env, callstack)
        if state !== nothing && state.use_thunk_cache && haskey(state.thunk_cache, key)
            # println("cache hit: $expr, $callstack, $name, $strict_order_index")
            return state.thunk_cache[key]
        else
            thunk = new(expr, env, [], copy(callstack), name, strict_order_index)
            if state !== nothing && state.use_thunk_cache
                state.thunk_cache[(expr, copy(env), copy(callstack))] = thunk
            end
            # if state !== nothing
            #     push!(state.thunks, thunk)
            # end
            return thunk
        end
    end
end

struct BDDThunkUnion
    thunks::Vector{Tuple{BDDThunk, BDD}}
    function BDDThunkUnion(worlds::Vector{Tuple{T, BDD}}, state) where T
        # if length(worlds) == 1
        #     return first(worlds)
        # end

        # collapse identical worlds
        uniq_worlds = Vector{BDDThunk}()
        uniq_guards = Vector{BDD}()
        uniq_world_indices = Dict{BDDThunk, Int}()

        for (world, outer_bdd) in worlds

            if world isa BDDThunkUnion
                #@warn "Removing a layer of indirection..."
                # remove a layer of indirection
                for (world, bdd) in world.thunks
                    if haskey(uniq_world_indices, world)
                        #@warn "Found duplicate world passed to BDDThunkUnion constructor: $world"
                        #Pluck.interesting_results[:thunk_union_collapse_time] += @elapsed
                        uniq_guards[uniq_world_indices[world]] = uniq_guards[uniq_world_indices[world]] | (outer_bdd & bdd)
                    else
                        #Pluck.interesting_results[:thunk_union_collapse_time] += @elapsed 
                        push!(uniq_worlds, world)
                        push!(uniq_guards, outer_bdd & bdd)
                        uniq_world_indices[world] = length(uniq_worlds)
                    end
                end

            elseif haskey(uniq_world_indices, world)
                #@warn "Found duplicate world passed to BDDThunkUnion constructor: $world"
                # Pluck.interesting_results[:thunk_union_collapse_time] += @elapsed 
                uniq_guards[uniq_world_indices[world]] = uniq_guards[uniq_world_indices[world]] | outer_bdd
            else
                # Pluck.interesting_results[:thunk_union_collapse_time] += @elapsed 
                push!(uniq_worlds, world)
                push!(uniq_guards, outer_bdd)
                uniq_world_indices[world] = length(uniq_worlds)
            end
        end

        worlds = Tuple{BDDThunk, BDD}[(world, bdd) for (world, bdd) in zip(uniq_worlds, uniq_guards)]
        return new(worlds)
    end
end


function Base.show(io::IO, x::BDDThunkUnion)
    print(io, "BDDThunkUnion{", length(x.thunks), "}(")
    for (i, (world, bdd)) in enumerate(x.thunks)
        print(io, world)
        #print(io, " [", x.wts[i], "]")
        if i < length(x.thunks)
            print(io, " | ")
        end
    end
    print(io, ")")
end

function Base.show(io::IO, x::BDDThunk)
    # print(io, "BDDThunk(", x.expr, ", ", x.callstack, ", ", x.name, ")")
    print(io, "BDDThunk(", x.expr, ")")
end




mutable struct BDDQuery
    query::Symbol
    bdd1size::Int
    bdd2size::Int
    resultsize::Int
    time::Float64
end

mutable struct BDDStats
    queries::Vector{BDDQuery}
    misc::Dict{Symbol, Any}
    function BDDStats()
        return new(BDDQuery[], Dict{Symbol, Any}())
    end
end

mutable struct BDDEvalState
    callstack::Callstack
    thunks::Vector{BDDThunk}
    disable_used_information::Bool
    disable_path_conditions::Bool
    singleton_cache::Bool
    var_of_callstack::Dict{Tuple{Callstack, Float64}, BDD}
    sorted_callstacks::Vector{Tuple{Callstack, Float64}}
    sorted_var_labels::Vector{Int}
    weights::WmcParams
    manager::RSDD.Manager
    BDD_TRUE::BDD
    BDD_FALSE::BDD
    true_thunk::BDDThunk
    false_thunk::BDDThunk
    depth::Int
    max_depth::Union{Int, Nothing}
    sample_after_max_depth::Bool
    use_strict_order::Bool
    use_experimental_order::Bool
    use_reverse_order::Bool
    use_thunk_cache::Bool
    thunk_cache::Dict{Tuple{PExpr, Env, Callstack}, BDDThunk}
    use_thunk_unions::Bool
    num_forward_calls::Int
    record_json::Bool
    bdd_stats::BDDStats
    viz::Any # Union{Nothing, BDDJSONLogger}
    function BDDEvalState(;
        max_depth::Union{Int, Nothing} = nothing,
        sample_after_max_depth::Bool = false,
        use_strict_order::Bool = true,
        use_experimental_order::Bool = false,
        use_reverse_order::Bool = false,
        use_thunk_cache::Bool = false,
        use_thunk_unions::Bool = true,
        record_json::Bool = false,
        disable_used_information::Bool = false,
        disable_path_conditions::Bool = false,
        singleton_cache::Bool = true,
    )
        manager = RSDD.mk_bdd_manager_default_order(0)
        BDD_TRUE = RSDD.bdd_true(manager)
        BDD_FALSE = RSDD.bdd_false(manager)
        true_thunk = BDDThunk(Construct(:True), Pluck.EMPTY_ENV, Callstack(), :truebr, 0, nothing)
        false_thunk = BDDThunk(Construct(:False), Pluck.EMPTY_ENV, Callstack(), :falsebr, 1, nothing)


        weights = RSDD.new_wmc_params_f64()
        state = new(
            Int[],
            BDDThunk[],
            disable_used_information,
            disable_path_conditions,
            singleton_cache,
            Dict{Tuple{Callstack, Float64}, BDD}(),
            Tuple{Callstack, Float64}[],
            Int[],
            weights,
            manager,
            BDD_TRUE,
            BDD_FALSE,
            true_thunk,
            false_thunk,
            0,
            max_depth,
            sample_after_max_depth,
            use_strict_order,
            use_experimental_order,
            use_reverse_order,
            use_thunk_cache,
            Dict{Tuple{PExpr, Env, Callstack}, BDDThunk}(),
            use_thunk_unions,
            0,
            record_json,
            BDDStats(),
            nothing,
        )


        if record_json
            state.viz = BDDJSONLogger(state)
        end
        return state
    end
end

function traced_bdd_forward(expr::PExpr, env::Env, available_information::BDD, state::BDDEvalState, strict_order_index::Int)
    # println(repeat(" ", state.depth) * "traced_bdd_forward: $expr")
    # Check whether available_information is false.
    if !state.disable_used_information && bdd_is_false(available_information)
        return [], state.BDD_FALSE
    end
    # start_time = time()
    #println(repeat(" ", state.depth) * "$expr")


    if state.max_depth !== nothing && state.depth > state.max_depth && !state.sample_after_max_depth
        return [], state.BDD_TRUE
    end

    state.depth += 1
    push!(state.callstack, strict_order_index)

    if state.record_json
        record_forward!(state.viz, expr, env, available_information, strict_order_index)
    end

    result, used_information = bdd_forward(expr, env, available_information, state)

    if state.record_json
        record_result!(state.viz, result, used_information)
    end

    pop!(state.callstack)
    state.num_forward_calls += 1
    state.depth -= 1
    # println(repeat(" ", state.depth) * "($((time() - start_time) * 1000) ms)")
    return result, used_information
end

# This is the 'join' of the monad.
# M X = Tuple{Vector{Tuple{X, BDD}}, BDD} = ([(X, Guard)], Used)
# M (M X) = ([(([(X, InnerGuard)], InnerUsed)), OuterGuard)], Used)

function combine_results(result_sets, used_information::BDD, available_information::BDD, state::BDDEvalState) #::Vector{Tuple{Tuple{Vector{Tuple{T, BDD}}, BDD}, BDD}} where T
    join_results = Vector{World}()
    index_of_result = Dict{AbstractValue, Int}()
    results_for_constructor = Dict{Symbol, Vector{Tuple{Value, BDD}}}()
    int_dist_results = Vector{Tuple{IntDist, BDD}}()

    for ((results, used_info), outer_guard) in result_sets
        if !state.disable_used_information
            used_information = used_information & outer_guard
        end
        for (result, inner_guard) in results
            inner_and_outer = inner_guard & outer_guard
            if result isa Closure || result isa FloatValue || (result isa Value && !state.use_thunk_unions)
                result_index = Base.get!(index_of_result, result, length(join_results) + 1)
                if result_index > length(join_results)
                    push!(join_results, (result, inner_and_outer))
                else
                    new_guard = join_results[result_index][2] | inner_and_outer
                    join_results[result_index] = (join_results[result_index][1], new_guard)
                end
            elseif state.use_thunk_unions && result isa Value
                constructor = result.constructor
                if !haskey(results_for_constructor, constructor)
                    results_for_constructor[constructor] = [(result, inner_and_outer)]
                else
                    push!(results_for_constructor[constructor], (result, inner_and_outer))
                end
            elseif result isa IntDist
                push!(int_dist_results, (result, inner_and_outer))
            else
                @assert false "combine_results found a result that is not a Value, Closure, or Float64: $result"
            end
        end
    end
    if state.use_thunk_unions
        for constructor in sort(collect(keys(results_for_constructor)))
            uniq_worlds = Vector{Value}()
            uniq_world_guards = Vector{BDD}()
            uniq_world_indices = Dict{Value, Int}()
            for (world, guard) in results_for_constructor[constructor]
                if !haskey(uniq_world_indices, world)
                    push!(uniq_worlds, world)
                    push!(uniq_world_guards, guard)
                    uniq_world_indices[world] = length(uniq_worlds)
                else
                    uniq_world_guards[uniq_world_indices[world]] = uniq_world_guards[uniq_world_indices[world]] | guard
                end
            end
            if length(uniq_worlds) > 1
                overall_guard = reduce((x, y) -> x | y, uniq_world_guards)
                overall_args = [(BDDThunkUnion([(world.args[i], bdd) for (world, bdd) in zip(uniq_worlds, uniq_world_guards)], state)) for i = 1:length(Pluck.args_of_constructor(constructor))]
                overall_value = Value(constructor, overall_args)
                push!(join_results, (overall_value, overall_guard))
            else
                push!(join_results, [(world, bdd) for (world, bdd) in zip(uniq_worlds, uniq_world_guards)]...)
            end
        end
    end

    if length(int_dist_results) > 0
        push!(join_results, combine_int_dists(int_dist_results, state))
    end

    return join_results, used_information
end

function combine_int_dists(int_dist_results, state)
    width = length(int_dist_results[1][1].bits)
    result = IntDist(fill(state.BDD_FALSE, width))
    overall_guard = state.BDD_FALSE
    for (int_dist, guard) in int_dist_results
        # should we compute an overall guard?
        overall_guard = overall_guard | guard
        @assert width == length(int_dist.bits)
        # For each bit, AND it with the guard then OR it into the result.
        for i = 1:width
            # I'm not sure if it should be (guard & bit) || acc
            # or if it should be (guard implies bit) iff acc
            # (both give the same result on a very simple example I did)

            @inbounds new_bit = int_dist.bits[i] & guard
            @inbounds result.bits[i] = result.bits[i] | new_bit
        end
    end
    return (result, overall_guard)
end

function evaluate(thunk::BDDThunkUnion, available_information::BDD, state::BDDEvalState)
    intermediate_results = []
    for (result, guard) in thunk.thunks
        new_guard = available_information & guard
        push!(intermediate_results, (evaluate(result, new_guard, state), guard))
    end

    return combine_results(intermediate_results, state.BDD_TRUE, available_information, state)
end

function evaluate(thunk::BDDThunk, available_information::BDD, state::BDDEvalState)
    if !state.disable_used_information && bdd_is_false(available_information)
        return [], state.BDD_FALSE
    end

    # Check the cache
    for (bdd, results) in thunk.cache
        does_cache_hit = bdd_is_true(available_information & bdd)
        if does_cache_hit
            return (results, bdd)
        end
    end

    # Otherwise we have to evaluate the thunk. Set the callstack to the thunk's callstack.
    old_callstack = state.callstack
    state.callstack = thunk.callstack
    # We have replaced available_information with BDD_TRUE.
    if state.singleton_cache && length(thunk.cache) == 1
        result, used_information = traced_bdd_forward(thunk.expr, thunk.env, available_information & !thunk.cache[1][1], state, thunk.strict_order_index)
    else
        result, used_information = traced_bdd_forward(thunk.expr, thunk.env, available_information, state, thunk.strict_order_index)
    end
    state.callstack = old_callstack
    # Cache the result
    if state.singleton_cache && length(thunk.cache) == 1
        # The code we're imagining is (if thunk.cache[1][1] then e else e)
        res, overall_used = combine_results([((thunk.cache[1][2], thunk.cache[1][1]), thunk.cache[1][1]), ((result, used_information), !thunk.cache[1][1])], state.BDD_TRUE, available_information, state)
        thunk.cache[1] = (overall_used, res)
        return (res, overall_used)
    else
        push!(thunk.cache, (used_information, result))
    end

    return result, used_information
end

function bdd_forward(expr::PExpr, env::Env, available_information::BDD, state::BDDEvalState)
    error("bdd_forward not implemented for $(typeof(expr))")
end

function bdd_bind(cont, first_stage_results, available_information, used_information, state)
    return combine_results([(cont(result, state.disable_path_conditions ? state.BDD_TRUE : result_guard), result_guard)
                            for (result, result_guard) in first_stage_results],
        used_information, available_information, state)
end

function bdd_forward(expr::App, env::Env, available_information::BDD, state::BDDEvalState)
    fs, used_information = traced_bdd_forward(expr.f, env, available_information, state, 0)
    thunked_argument = BDDThunk(expr.x, env, state.callstack, :app_x, 1, state)

    return bdd_bind(fs, available_information, used_information, state) do f, f_guard
        new_env = copy(f.env)
        x = thunked_argument
        pushfirst!(new_env, x)
        results, used_info = traced_bdd_forward(f.expr, new_env, available_information & f_guard, state, 2)
        return results, used_information & used_info
    end
end

function bdd_forward(expr::Abs, env::Env, available_information::BDD, state::BDDEvalState)
    # A lambda term deterministically evaluates to a closure.
    return [(Closure(expr.body, env), state.BDD_TRUE)], state.BDD_TRUE
end

function bdd_forward(expr::Construct, env::Env, available_information::BDD, state::BDDEvalState)
    # Constructors deterministically evaluate to a WHNF value, with their arguments thunked.
    # Create a thunk for each argument.
    thunked_arguments = [BDDThunk(arg, env, state.callstack, Symbol("$(expr.constructor).arg$i"), i, state) for (i, arg) in enumerate(expr.args)] # TODO: use global args_syms to avoid runtime cost of Symbol?
    # Return the constructor and its arguments.
    return [(Value(expr.constructor, thunked_arguments), state.BDD_TRUE)], state.BDD_TRUE
end

function bdd_forward(expr::CaseOf, env::Env, available_information::BDD, state::BDDEvalState)
    scrutinee_values, scrutinee_used_information = traced_bdd_forward(expr.scrutinee, env, available_information, state, 0)
    constructor_indices = Dict{Symbol, Int}()
    for (i, constructor) in enumerate(keys(expr.cases)) # sort? reverse?
        constructor_indices[constructor] = i
    end
    bdd_bind(scrutinee_values, available_information, scrutinee_used_information, state) do scrutinee, scrutinee_guard
        #println("Evaluated scrutinee expression $(expr.scrutinee)")
        #println("SCrutinee type: $(typeof(scrutinee))")
        #println("Scrutinee val args: $(scrutinee.args)")
        if scrutinee.constructor in keys(expr.cases)
            case_expr = expr.cases[scrutinee.constructor]
            num_args = length(args_of_constructor[scrutinee.constructor])
            updated_guard = bdd_and(scrutinee_guard, available_information)
            # println("Size of updated guard: $(RSDD.bdd_size(updated_guard))")
            # if RSDD.bdd_size(updated_guard) == 0
            #     @show scrutinee_guard
            #     @show available_information
            # end
            if num_args == 0
                return traced_bdd_forward(case_expr, env, updated_guard, state, constructor_indices[scrutinee.constructor])
            else
                for _ = 1:num_args
                    @assert case_expr isa Abs "case expression branch for constructor $(scrutinee.constructor) must have as many lambdas as the constructor has arguments ($(num_args) arguments)"
                    case_expr = case_expr.body
                end
                # In each of the scrutinee arguments, filter out options that contradict the available information.
                new_env = copy(env)
                used_information = state.BDD_TRUE
                for (i, arg) in enumerate(scrutinee.args)
                    # if arg isa BDDThunkUnion
                    #     arg, used_info = simplify_thunk_union(arg, available_information, state)
                    #     used_information = used_information & used_info
                    # end
                    pushfirst!(new_env, arg)
                end
                # new_env = vcat(reverse(scrutinee.args), env)
                results, used_info = traced_bdd_forward(case_expr, new_env, updated_guard, state, constructor_indices[scrutinee.constructor])
                return results, used_information & used_info
            end
        else
            # println("Scrutinee not in case expression: $(scrutinee) in $(expr)")
            return [], state.BDD_TRUE
        end
    end
end

# function simplify_thunk_union(thunk::BDDThunkUnion, available_information::BDD, state::BDDEvalState)
#     used_information = state.BDD_TRUE
#     returned_thunks = Tuple{BDDThunk, BDD}[]
#     for (thunk, guard) in thunk.thunks
#         if bdd_is_false(available_information & guard)
#             used_information = used_information & bdd_implies(guard, state.BDD_FALSE)
#         else
#             push!(returned_thunks, (thunk, guard))
#         end
#     end
#     return BDDThunkUnion(returned_thunks), used_information
# end

function bdd_forward(expr::Y, env::Env, available_information::BDD, state::BDDEvalState)
    @assert expr.f isa Abs && expr.f.body isa Abs "y-combinator must be applied to a double-lambda"

    closure = Pluck.make_self_loop(expr.f.body.body, env)

    # set up a closure with a circular reference
    return [(closure, state.BDD_TRUE)], state.BDD_TRUE
end

function bdd_forward(expr::PrimOp, env::Env, available_information::BDD, state::BDDEvalState)
    bdd_prim_forward(expr.op, expr.args, env, available_information, state)
end

function bdd_make_address(state::BDDEvalState, p::Float64, available_information::BDD)
    if haskey(state.var_of_callstack, (state.callstack, p))
        return state.var_of_callstack[(state.callstack, p)]
    else
        # Find position in the variable order in which to create the new variable.
        # This is based on where in state.sorted_callstacks this callstack should go.
        # We want to do a binary search over the sorted list. The order on callstacks
        # is lexicographic, so we can do this with a binary search.
        callstack = copy(state.callstack)

        if !state.use_strict_order
            # Create the new variable.
            # if state.use_reverse_order
            #     addr = RSDD.bdd_new_var_at_position(state.manager, 0, true)
            # elseif state.use_experimental_order
            #     last_var = RSDD.bdd_last_var(available_information)
            #     if last_var !== nothing
            #         last_variable_position = RSDD.bdd_var_position(state.manager, last_var)
            #         addr = RSDD.bdd_new_var_at_position(state.manager, last_variable_position + 1, true)
            #     else
            #         addr = RSDD.bdd_new_var(state.manager, true)
            #     end
            # else
            #     addr = RSDD.bdd_new_var(state.manager, true)
            # end
            addr = RSDD.bdd_new_var(state.manager, true)
            # println(repeat(" ", state.depth) * "New var: $(bdd_topvar(addr))")
            # println("New var at position 0")
            # addr = RSDD.bdd_new_var_at_position(state.manager, 0, true)
        else
            i = searchsortedfirst(state.sorted_callstacks, (state.callstack, p); by = x -> x[1], rev = state.use_reverse_order)
            # Insert the callstack in the sorted list.
            addr = RSDD.bdd_new_var_at_position(state.manager, i - 1, true) # Rust uses 0-indexing
            insert!(state.sorted_callstacks, i, (callstack, p))
            insert!(state.sorted_var_labels, i, Int(bdd_topvar(addr)))
        end
        state.var_of_callstack[(callstack, p)] = addr
        return addr
    end
end

function bdd_prim_forward(op::FlipOp, args, env::Env, available_information::BDD, state::BDDEvalState)

    ps, used_information = traced_bdd_forward(args[1], env, available_information, state, 0)
    bdd_bind(ps, available_information, used_information, state) do p, p_guard
        p = p.value
        if isapprox(p, 0.0)
            return [(Pluck.FALSE_VALUE, p_guard)], state.BDD_TRUE
        elseif isapprox(p, 1.0)
            return [(Pluck.TRUE_VALUE, p_guard)], state.BDD_TRUE
        else
            # If we are past the max depth, AND we are sampling after the max depth, AND 
            # this flip is new (not previously instantiated), THEN sample a value.
            if state.max_depth !== nothing && state.depth > state.max_depth && state.sample_after_max_depth && !haskey(state.var_of_callstack, (state.callstack, p))
                sampled_value = rand() < p ? Pluck.TRUE_VALUE : Pluck.FALSE_VALUE
                return [(sampled_value, state.BDD_TRUE)], state.BDD_TRUE
            end

            # Otherwise, we perform the usual logic.
            # BDDs do not represent quantitative probabilities. Therefore, for each 
            # different probability `p`, we need to create a new variable in the BDD.
            push!(state.callstack, 1)
            addr = bdd_make_address(state, p, available_information)
            wmc_param_f64_set_weight(state.weights, bdd_topvar(addr), 1.0 - p, p)
            pop!(state.callstack)
            return [(Pluck.TRUE_VALUE, addr), (Pluck.FALSE_VALUE, !addr)], state.BDD_TRUE
        end
    end
end

function bdd_prim_forward(op::ConstructorEqOp, args, env::Env, available_information::BDD, state::BDDEvalState)
    # Evaluate both arguments.
    first_arg_results, first_arg_used_information = traced_bdd_forward(args[1], env, available_information, state, 0)
    bdd_bind(first_arg_results, available_information, first_arg_used_information, state) do arg1, arg1_guard
        second_arg_results, second_arg_used_information = traced_bdd_forward(args[2], env, arg1_guard & available_information, state, 1)
        bdd_bind(second_arg_results, available_information, second_arg_used_information, state) do arg2, arg2_guard
            if arg1.constructor == arg2.constructor
                return [(Pluck.TRUE_VALUE, state.BDD_TRUE)], state.BDD_TRUE
            else
                return [(Pluck.FALSE_VALUE, state.BDD_TRUE)], state.BDD_TRUE
            end
        end
    end
end

const int_dist_of_bitwidth = Symbol[:Int1, :Int2, :Int3, :Int4]


function bdd_prim_forward(op::MkIntOp, args, env::Env, available_information::BDD, state::BDDEvalState)
    bitwidth = args[1]::RawInt
    val = args[2]::RawInt
    bools = digits(Bool, val.val, base = 2, pad = bitwidth.val)
    bits = map(b -> b ? state.BDD_TRUE : state.BDD_FALSE, bools)

    return [(IntDist(bits), state.BDD_TRUE)], state.BDD_TRUE
end

function bdd_prim_forward(op::IntDistEqOp, args, env::Env, available_information::BDD, state::BDDEvalState)
    first_int_dist, first_used_information = traced_bdd_forward(args[1], env, available_information, state, 0)
    bdd_bind(first_int_dist, available_information, first_used_information, state) do first_int_dist, first_int_dist_guard
        second_int_dist, second_used_information = traced_bdd_forward(args[2], env, first_int_dist_guard & available_information, state, 1)
        bdd_bind(second_int_dist, available_information, second_used_information, state) do second_int_dist, second_int_dist_guard
            bdd = int_dist_eq(first_int_dist, second_int_dist, state)
            # do we put second_int_dist_guard anywhere?
            return [(Pluck.TRUE_VALUE, bdd), (Pluck.FALSE_VALUE, !bdd)], state.BDD_TRUE
        end
    end
end


"""
Equality of two int distributions is an AND over the equality (bdd_iff) of each bit.
"""
function int_dist_eq(x::IntDist, y::IntDist, state::BDDEvalState)::BDD
    width = length(x.bits)
    @assert width == length(y.bits)
    result = state.BDD_TRUE
    for i = 1:width
        @inbounds result = bdd_and(result, bdd_iff(x.bits[i], y.bits[i]))
        if bdd_is_false(result)
            return state.BDD_FALSE
        end
    end
    return result
end


function bdd_forward(expr::Var, env::Env, available_information::BDD, state::BDDEvalState)
    # Look up the variable in the environment.
    if expr.idx > length(env)
        @warn "Variable $expr not found in environment; shaving off probability."
        return [], state.BDD_TRUE
    end

    v = env[expr.idx]
    if v isa BDDThunk || v isa BDDThunkUnion
        return evaluate(v, available_information, state)
    else
        # Does this case ever arise? One example is that for recursive calls,
        # we create a closure (not a thunk) and store it in the environment.
        return [(v, state.BDD_TRUE)], state.BDD_TRUE
    end
end

function bdd_forward(expr::Defined, env::Env, available_information::BDD, state::BDDEvalState)
    # Execute Defined with a blanked out environment.
    return traced_bdd_forward(Pluck.lookup(expr.name).expr, Pluck.EMPTY_ENV, available_information, state, 0)
end


function bdd_forward(expr::ConstReal, env::Env, available_information::BDD, state::BDDEvalState)
    return [(FloatValue(expr.val), state.BDD_TRUE)], state.BDD_TRUE
end

function bdd_forward(expr; show_bdd = false, show_bdd_size = false, record_bdd_json = false, make_state = () -> BDDEvalState(), return_bdd_stats = false)
    if expr isa String
        expr = parse_expr(expr)
    end
    state = make_state()
    ret, used_information = traced_bdd_forward((expr), Pluck.EMPTY_ENV, state.BDD_TRUE, state, 0)
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
                        bit_bdd = bit_bdd & ~bit_formula
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

    if show_bdd_size
        summed_size = sum(Int(RSDD.bdd_size(bdd)) for (ret, (bdd)) in ret)
        num_vars = length(state.sorted_callstacks)
        printstyled("vars: $num_vars nodes: $summed_size\n"; color=:blue)
        println("BDD sizes: $([(ret, Int(RSDD.bdd_size(bdd))) for (ret, (bdd)) in ret])")
    end
    # Trying a model count of each possibility.
    if show_bdd
        results = [(v, repr(bdd), RSDD.bdd_wmc(bdd, state.weights)) for (v, bdd) in ret]
        used_information = repr(used_information)
    else
        results = [(v, RSDD.bdd_wmc(bdd, state.weights)) for (v, bdd) in ret]
    end

    if record_bdd_json
        println(ret[2][1].constructor == :True)
        true_results = findall(x -> x[1] == Pluck.TRUE_VALUE || x[1].constructor == :True, ret)
        @assert length(true_results) == 1 "Expected exactly one true result, got $(length(true_results))"
        record_bdd(state, ret[true_results[1]][2])
    end
    free_bdd_manager(state.manager)
    free_wmc_params(state.weights)
    if state.record_json
        dir = timestamp_dir(; base = "out/bdd")
        write_out(state.viz, joinpath(dir, "bdd_forward.json"))
        println(webaddress("html/bdd_forward.html", joinpath(dir, "bdd_forward.json"), false))
    end
    res = show_bdd ? (results, used_information) : results
    if return_bdd_stats
        return res, state.bdd_stats
    else
        return res
    end
end

function normalize(results)
    probabilities = [res[2] for res in results]
    total = sum(probabilities)
    return [(res[1], res[2] / total) for res in results]
end

function infer_full_distribution(initial_results, state)
    # Queue of (value, bdd) pairs to process
    queue = initial_results
    # Final set of fully resolved (value, bdd) pairs
    resolved = Vector{Tuple{Value, BDD}}()

    while !isempty(queue)
        (current_val, current_bdd) = pop!(queue)
        # Find first unresolved thunk in the value tree
        thunk_path = find_first_thunk(current_val)
        
        if isnothing(thunk_path)
            # No more thunks - this value is fully resolved
            push!(resolved, (current_val, current_bdd))
            continue
        end

        # Get the thunk at the path
        thunk = get_value_at_path(current_val, thunk_path)
        
        # Evaluate the thunk
        sub_results, _ = evaluate(thunk, current_bdd, state)
        
        # For each possible result of the thunk evaluation
        for (sub_val, sub_bdd) in sub_results
            # Create a copy of the value with this thunk replaced
            new_val = replace_at_path(current_val, thunk_path, sub_val)
            # Add to queue with conjunction of bdds
            push!(queue, (new_val, current_bdd & sub_bdd))
        end
    end

    return reverse(resolved)
end

# Helper function to find first thunk in a value tree using DFS
function find_first_thunk(val::Value, path::Vector{Int} = Int[])
    # Check direct arguments first
    for (i, arg) in enumerate(val.args)
        if arg isa BDDThunk || arg isa BDDThunkUnion
            push!(path, i)
            return path
        elseif arg isa Value
            # Recursively check this argument
            sub_path = find_first_thunk(arg, copy(path))
            if !isnothing(sub_path)
                pushfirst!(sub_path, i)
                return sub_path
            end
        end
    end
    return nothing
end

# Helper to get value at a path in the value tree
function get_value_at_path(val::Value, path::Vector{Int})
    current = val
    for i in path[1:end-1]
        current = current.args[i]
    end
    return current.args[path[end]]
end

# Helper to create a copy of a value with replacement at path
function replace_at_path(val::Value, path::Vector{Int}, new_val)
    if isempty(path)
        return new_val
    end
    
    # Create copy of value
    new_args = copy(val.args)
    
    if length(path) == 1
        # Direct replacement
        new_args[path[1]] = new_val
    else
        # Recursive replacement
        new_args[path[1]] = replace_at_path(val.args[path[1]], path[2:end], new_val)
    end
    
    return Value(val.constructor, new_args)
end