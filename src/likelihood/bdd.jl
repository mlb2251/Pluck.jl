export bdd_normalize, bdd_forward, BDDEvalState, make_uniform_nat, BDDEvalStateConfig, bdd_constrain, get_true_result


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
const ForwardResult = Tuple{Vector{World}, BDD}


struct BDDThunk
    expr::PExpr
    env::Env
    cache::Vector{Tuple{BDD, Vector{World}}}
    callstack::Callstack
    name::Symbol
    strict_order_index::Int

    function BDDThunk(expr::PExpr, env::Env, callstack::Callstack, name::Symbol, strict_order_index::Int, state)
        if expr isa Var && env[expr.idx] isa BDDThunk
            return env[expr.idx]
        end

        key = (expr, env, callstack)
        if state.use_thunk_cache && haskey(state.thunk_cache, key)
            # println("cache hit: $expr, $callstack, $name, $strict_order_index")
            return state.thunk_cache[key]
        else
            thunk = new(expr, Pluck.mask_thunk_env(env, expr), [], copy(callstack), name, strict_order_index)
            if state.use_thunk_cache
                state.thunk_cache[(expr, copy(env), copy(callstack))] = thunk
            end
            return thunk
        end
    end
end

struct BDDThunkUnion
    thunks::Vector{Tuple{BDDThunk, BDD}}
    function BDDThunkUnion(worlds::Vector{Tuple{T, BDD}}) where T
        # if length(worlds) == 1
        #     return first(worlds)
        # end

        # collapse identical worlds
        # uniq = Dict{BDDThunk, BDD}()
        uniq = IdDict{BDDThunk, BDD}()
        for (world, outer_bdd) in worlds

            if world isa BDDThunkUnion
                # @warn "Removing a layer of indirection..."
                # remove a layer of indirection
                for (world, bdd) in world.thunks
                    if haskey(uniq, world)
                        #@warn "Found duplicate world passed to BDDThunkUnion constructor: $world"
                        uniq[world] = uniq[world] | (outer_bdd & bdd)
                    else
                        uniq[world] = (outer_bdd & bdd)
                    end
                end

            elseif haskey(uniq, world)
                #@warn "Found duplicate world passed to BDDThunkUnion constructor: $world"
                uniq[world] = uniq[world] | outer_bdd
            else
                uniq[world] = outer_bdd
            end
        end

        worlds = Tuple{BDDThunk, BDD}[(world, bdd) for (world, bdd) in pairs(uniq)]
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

mutable struct BDDEvalStats
    time::Float64
    num_forward_calls::Int
    hit_limit::Bool
end
BDDEvalStats() = BDDEvalStats(0.0, 0, false)
function Base.:+(a::BDDEvalStats, b::BDDEvalStats)
    BDDEvalStats(a.time + b.time, a.num_forward_calls + b.num_forward_calls, a.hit_limit || b.hit_limit)
end

Base.@kwdef mutable struct BDDEvalStateConfig
    max_depth::Union{Int, Nothing} = nothing
    sample_after_max_depth::Bool = false
    use_strict_order::Bool = true
    use_thunk_cache::Bool = false
    use_thunk_unions::Bool = true
    record_json::Bool = false
    time_limit::Float64 = 0.0
    root_equality_fn::String = "old_list_eq"
    bdd_forward_fn::Function = bdd_forward
    state_vars::StateVars = StateVars()
end

mutable struct BDDEvalState
    callstack::Callstack
    var_of_callstack::Dict{Tuple{Callstack, Float64}, BDD}
    sorted_callstacks::Vector{Tuple{Callstack, Float64}}
    sorted_var_labels::Vector{Int}
    weights::WmcParams
    manager::RSDD.Manager
    BDD_TRUE::BDD
    BDD_FALSE::BDD
    depth::Int
    max_depth::Union{Int, Nothing}
    sample_after_max_depth::Bool
    use_strict_order::Bool
    use_thunk_cache::Bool
    thunk_cache::Dict{Tuple{PExpr, Env, Callstack}, BDDThunk}
    use_thunk_unions::Bool
    record_json::Bool
    time_limit::Float64
    stats::BDDEvalStats
    viz::Any # Union{Nothing, BDDJSONLogger}
    dirty::Bool
    start_time::Float64
    root_equality_fn::String
    bdd_forward_fn::Function
    hit_limit::Bool
    state_vars::StateVars
    # curr_expr::Union{Nothing,PExpr}
    function BDDEvalState(config::BDDEvalStateConfig)
        manager = RSDD.mk_bdd_manager_default_order(0)
        manager.time_limit = config.time_limit
        BDD_TRUE = RSDD.bdd_true(manager)
        BDD_FALSE = RSDD.bdd_false(manager)
        weights = RSDD.new_wmc_params_f64()
        state = new(
            Int[],
            Dict{Tuple{Callstack, Float64}, BDD}(),
            Tuple{Callstack, Float64}[],
            Int[],
            weights,
            manager,
            BDD_TRUE,
            BDD_FALSE,
            0,
            config.max_depth,
            config.sample_after_max_depth,
            config.use_strict_order,
            config.use_thunk_cache,
            Dict{Tuple{PExpr, Env, Callstack}, BDDThunk}(),
            config.use_thunk_unions,
            config.record_json,
            config.time_limit,
            BDDEvalStats(),
            nothing,
            false,
            0.0,
            config.root_equality_fn,
            config.bdd_forward_fn,
            false,
            config.state_vars,
            # nothing
        )
        if config.record_json
            state.viz = BDDJSONLogger(state)
        end
        finalizer(free_state!, state)
        return state
    end
end

function free_state!(state::BDDEvalState)
    if !state.manager.freed
        RSDD.free_wmc_params(state.weights)
        RSDD.free_bdd_manager(state.manager)
    end
end

function reset_state!(state::BDDEvalState)
    empty!(state.callstack)
    empty!(state.var_of_callstack)
    empty!(state.sorted_callstacks)
    empty!(state.sorted_var_labels)

    state.hit_limit = false

    free_state!(state)
    state.weights = RSDD.new_wmc_params_f64()
    state.manager = RSDD.mk_bdd_manager_default_order(0)
    state.manager.time_limit = state.time_limit

    state.BDD_TRUE = RSDD.bdd_true(state.manager)
    state.BDD_FALSE = RSDD.bdd_false(state.manager)
    
    state.depth = 0
    empty!(state.thunk_cache)
    state.stats = BDDEvalStats()
    if state.record_json
        state.viz = BDDJSONLogger(state)
    end
    state.dirty = false
    state
end


function traced_bdd_forward(expr::PExpr, env::Env, available_information::BDD, state::BDDEvalState, strict_order_index::Int)
    # println(repeat(" ", state.depth) * "traced_bdd_forward: $expr, $env")
    # Check whether available_information is false.
    if bdd_is_false(available_information)
        return World[], state.BDD_FALSE
    end

    #println(repeat(" ", state.depth) * "$expr")


    if state.max_depth !== nothing && state.depth > state.max_depth && !state.sample_after_max_depth
        state.hit_limit = true
        return World[], state.BDD_TRUE
    end

    if check_time_limit(state)
        state.hit_limit = true
        # println("time limit of $(state.time_limit) exceeded")
        return World[], state.BDD_TRUE
    end

    state.depth += 1
    push!(state.callstack, strict_order_index)

    if state.record_json
        record_forward!(state.viz, expr, env, available_information, strict_order_index)
    end

    # prev_expr = state.curr_expr
    # state.curr_expr = expr
    result, used_information = bdd_forward(expr, env, available_information, state)::ForwardResult
    # state.curr_expr = prev_expr

    if state.record_json
        record_result!(state.viz, result, used_information)
    end

    pop!(state.callstack)
    state.stats.num_forward_calls += 1
    state.depth -= 1

    if RSDD.time_limit_exceeded(state.manager)
        state.hit_limit = true
        return World[], state.BDD_TRUE
    end

    #println(repeat(" ", state.depth) * "($((finish_time - start_time) * 1000) ms)")
    return result, used_information
end

@inline function get_time_limit(state::BDDEvalState)
    return state.time_limit
end
@inline function get_start_time(state::BDDEvalState)
    return state.start_time
end

get_time_limit(cfg::BDDEvalStateConfig) = cfg.time_limit
set_time_limit!(cfg::BDDEvalStateConfig, time_limit::Float64) = (cfg.time_limit = time_limit)


@inline function elapsed_time(state)
    return time() - get_start_time(state)
end
@inline function check_time_limit(state)
    return get_time_limit(state) > 0. && elapsed_time(state) > get_time_limit(state)
end


# This is the 'join' of the monad.
# M X = Tuple{Vector{Tuple{X, BDD}}, BDD} = ([(X, Guard)], Used)
# M (M X) = ([(([(X, InnerGuard)], InnerUsed)), OuterGuard)], Used)

function combine_results(result_sets, used_information::BDD, state::BDDEvalState)::ForwardResult
    # TODO: check if determinism still holds

    join_results = Vector{World}()
    index_of_result = Dict{Any, Int}()
    results_for_constructor = Dict{Symbol, Vector{Tuple{Value, BDD}}}()

    for ((results, used_info), outer_guard) in result_sets
        # t=@timed( )
        used_information = used_information & bdd_implies(outer_guard, used_info)
        # if t.time > 0.01
        #     @warn "bdd_implies took $(t.time) seconds for $(RSDD.bdd_size(outer_guard)) $(outer_guard.ptr) x $(RSDD.bdd_size(used_info)) $(used_info.ptr) and result size $(RSDD.bdd_size(used_information)) $(used_information.ptr)"
        # end
        for (result, inner_guard) in results
            inner_and_outer = inner_guard & outer_guard
            if result isa Closure || result isa Float64 || result isa Symbol || (result isa Value && !state.use_thunk_unions)
                result_index = Base.get!(index_of_result, result, length(join_results) + 1)
                if result_index > length(join_results)
                    push!(join_results, (result, inner_and_outer))
                else
                    join_results[result_index] = (join_results[result_index][1], join_results[result_index][2] | (inner_and_outer))
                end
            elseif state.use_thunk_unions && result isa Value
                constructor = result.constructor
                if !haskey(results_for_constructor, constructor)
                    results_for_constructor[constructor] = [(result, inner_and_outer)]
                else
                    push!(results_for_constructor[constructor], (result, inner_and_outer))
                end
            else
                @assert false "combine_results found a result that is not a Value, Closure, Symbol, or Float64: $result"
            end
        end
    end
    if state.use_thunk_unions
        for constructor in sort(collect(keys(results_for_constructor)))
            uniq_worlds = Dict{Value, BDD}()
            for (world, guard) in results_for_constructor[constructor]
                if !haskey(uniq_worlds, world)
                    push!(uniq_worlds, world => guard)
                else
                    uniq_worlds[world] = uniq_worlds[world] | guard
                end
            end
            if length(uniq_worlds) > 1
                # t=@timed(overall_guard = reduce(|, sort([bdd for (_, bdd) in pairs(uniq_worlds)], by = x -> RSDD.bdd_size(x))))
                worlds_by_size = [(bdd, bdd_size(bdd)) for (_, bdd) in pairs(uniq_worlds)]
                sort!(worlds_by_size, by = x -> x[2])
                overall_guard = reduce(|, [bdd for (bdd, _) in worlds_by_size])
                overall_value = Value(Pluck.spt_of_constructor[constructor], constructor, [BDDThunkUnion([(world.args[i], bdd) for (world, bdd) in pairs(uniq_worlds)]) for i = 1:length(Pluck.args_of_constructor(constructor))])
                # if t.time > 0.1
                    # @warn "reduce took $(t.time)s for $(length(uniq_worlds)) worlds of constructor $constructor -> $(bdd_size(overall_guard))"
                    # for (world, bdd) in pairs(uniq_worlds)
                    #     # println("  $(bdd_size(bdd)) $world")
                    #     if world isa Value && world.constructor == :S && world.args[1] isa BDDThunkUnion
                    #         for (thunk, thunk_guard) in world.args[1].thunks
                    #             # println("    $(thunk.expr) $(bdd_size(thunk_guard))")
                    #         end
                    #     end
                    # end
                    # println("  $(bdd_size(overall_guard)) $overall_value")
                # end
                push!(join_results, (overall_value, overall_guard))
            else
                push!(join_results, [(world, bdd) for (world, bdd) in pairs(uniq_worlds)]...)
            end
        end
    end
    return join_results, used_information
end

function evaluate(thunk::BDDThunkUnion, available_information::BDD, state::BDDEvalState)::ForwardResult

    # println("Evaluating thunk union, thunks are $([(repr(result)) for (result, _) in thunk.thunks])")
    # println("BDD size of available information: $(Int(RSDD.bdd_size(available_information)))")
    # println("BDD sizes of thunk guards: $([Int(RSDD.bdd_size(guard)) for (_, guard) in thunk.thunks])")
    return combine_results([(evaluate(result, available_information & guard, state), guard)
                            for (result, guard) in thunk.thunks], state.BDD_TRUE, state)

end

function loud_time(f, res_msg_fn)
    t=@timed(res = f())
    if t.time > 0.01
        @warn res_msg_fn(res) * " took $(t.time)s"
    end
    res
end

function evaluate(thunk::BDDThunk, available_information::BDD, state::BDDEvalState)::ForwardResult
    if bdd_is_false(available_information)
        return World[], state.BDD_FALSE
    end

    # Check the cache
    #start_time = time()
    for (bdd, results) in thunk.cache
        if bdd_is_true(bdd_implies(available_information, bdd))
            #finish_time = time()
            #println(repeat(" ", state.depth) * "$(thunk.expr) (cached, $((finish_time - start_time) * 1000) ms.)")
            return (results, bdd)
        end
    end

    # Otherwise we have to evaluate the thunk. Set the callstack to the thunk's callstack.
    old_callstack = state.callstack
    state.callstack = thunk.callstack
    result, used_information = traced_bdd_forward(thunk.expr, thunk.env, available_information, state, thunk.strict_order_index)::ForwardResult
    state.callstack = old_callstack
    # Cache the result
    push!(thunk.cache, (used_information, result))

    return result, used_information
end

function bdd_forward(expr::PExpr, env::Env, available_information::BDD, state::BDDEvalState)
    error("bdd_forward not implemented for $(typeof(expr))")
end

function bdd_bind(cont, first_stage_results::Vector{World}, available_information, used_information, state)
    return combine_results(Tuple{ForwardResult, BDD}[(cont(result, result_guard), result_guard)
                            for (result, result_guard) in first_stage_results],
        used_information, state)
end

function bdd_forward(expr::App, env::Env, available_information::BDD, state::BDDEvalState)
    fs, used_information = traced_bdd_forward(expr.f, env, available_information, state, 0)
    thunked_argument = BDDThunk(expr.x, env, state.callstack, :app_x, 1, state)

    return bdd_bind(fs, available_information, used_information, state) do f, f_guard
        new_env = copy(f.env)
        x = Pluck.var_is_free(f.expr, 1) ? thunked_argument : nothing
        pushfirst!(new_env, x)
        return traced_bdd_forward(f.expr, new_env, available_information & f_guard, state, 2)
    end
end

function bdd_forward(expr::Abs, env::Env, available_information::BDD, state::BDDEvalState)
    # A lambda term deterministically evaluates to a closure.
    return World[(Closure(expr.body, env), state.BDD_TRUE)], state.BDD_TRUE
end

function bdd_forward(expr::Construct, env::Env, available_information::BDD, state::BDDEvalState)
    # Constructors deterministically evaluate to a WHNF value, with their arguments thunked.
    # Look up type of this constructor.
    spt = Pluck.spt_of_constructor[expr.constructor]
    # Create a thunk for each argument.
    thunked_arguments = BDDThunk[BDDThunk(arg, env, state.callstack, Symbol("$(expr.constructor).arg$i"), i, state) for (i, arg) in enumerate(expr.args)] # TODO: use global args_syms to avoid runtime cost of Symbol?
    # Return the constructor and its arguments.
    return World[(Value(spt, expr.constructor, thunked_arguments), state.BDD_TRUE)], state.BDD_TRUE
end

function bdd_forward(expr::CaseOf, env::Env, available_information::BDD, state::BDDEvalState)
    scrutinee_values, scrutinee_used_information = traced_bdd_forward(expr.scrutinee, env, available_information, state, 0)
    constructor_indices = Dict{Symbol, Int}()
    for (i, constructor) in enumerate(expr.constructors) # sort? reverse?
        constructor_indices[constructor] = i
    end
    bdd_bind(scrutinee_values, available_information, scrutinee_used_information, state) do scrutinee, scrutinee_guard
        if scrutinee.constructor in expr.constructors
            case_expr = expr.cases[scrutinee.constructor]
            num_args = length(args_of_constructor(scrutinee.constructor))
            if num_args == 0
                return traced_bdd_forward(case_expr, env, available_information & scrutinee_guard, state, constructor_indices[scrutinee.constructor])
            else
                for _ = 1:num_args
                    @assert case_expr isa Abs "case expression branch for constructor $(scrutinee.constructor) must have as many lambdas as the constructor has arguments ($(num_args) arguments)"
                    case_expr = case_expr.body
                end
                new_env = vcat(reverse(scrutinee.args), env)
                return traced_bdd_forward(case_expr, new_env, available_information & scrutinee_guard, state, constructor_indices[scrutinee.constructor])
            end
        else
            return World[], state.BDD_TRUE
        end
    end
end

function bdd_forward(expr::Y, env::Env, available_information::BDD, state::BDDEvalState)
    @assert expr.f isa Abs && expr.f.body isa Abs "y-combinator must be applied to a double-lambda"

    closure = Pluck.make_self_loop(expr.f.body.body, env)

    # set up a closure with a circular reference
    return World[(closure, state.BDD_TRUE)], state.BDD_TRUE
end

function bdd_forward(expr::PrimOp, env::Env, available_information::BDD, state::BDDEvalState)
    bdd_prim_forward(expr.op, expr.args, env, available_information, state)
end

function bdd_make_address(state::BDDEvalState, p::Float64)
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
            addr = RSDD.bdd_new_var(state.manager, true)
        else
            i = searchsortedfirst(state.sorted_callstacks, (state.callstack, p); by = x -> x[1])
            # Insert the callstack in the sorted list.
            addr = RSDD.bdd_new_var_at_position(state.manager, i - 1, true) # Rust uses 0-indexing
            insert!(state.sorted_callstacks, i, (callstack, p))
            insert!(state.sorted_var_labels, i, Int(bdd_topvar(addr)))
        end
        state.var_of_callstack[(callstack, p)] = addr
        # state.expr_of_var[Int(bdd_topvar(addr))] = state.curr_expr
        return addr
    end
end

function bdd_prim_forward(op::FlipOp, args, env::Env, available_information::BDD, state::BDDEvalState)

    ps, used_information = traced_bdd_forward(args[1], env, available_information, state, 0)
    bdd_bind(ps, available_information, used_information, state) do p, p_guard
        if isapprox(p, 0.0)
            return World[(Pluck.FALSE_VALUE, p_guard)], state.BDD_TRUE # TODO does this makes sense or should it have a BDD_TRUE?
        elseif isapprox(p, 1.0)
            return World[(Pluck.TRUE_VALUE, p_guard)], state.BDD_TRUE
        else
            # If we are past the max depth, AND we are sampling after the max depth, AND 
            # this flip is new (not previously instantiated), THEN sample a value.
            if state.max_depth !== nothing && state.depth > state.max_depth && state.sample_after_max_depth && !haskey(state.var_of_callstack, (state.callstack, p))
                sampled_value = rand() < p ? Pluck.TRUE_VALUE : Pluck.FALSE_VALUE
                return World[(sampled_value, state.BDD_TRUE)], state.BDD_TRUE
            end

            # Otherwise, we perform the usual logic.
            # BDDs do not represent quantitative probabilities. Therefore, for each 
            # different probability `p`, we need to create a new variable in the BDD.
            push!(state.callstack, 1)
            addr = bdd_make_address(state, p)
            wmc_param_f64_set_weight(state.weights, bdd_topvar(addr), 1.0 - p, p)
            pop!(state.callstack)
            return World[(Pluck.TRUE_VALUE, addr), (Pluck.FALSE_VALUE, !addr)], state.BDD_TRUE
        end
    end
end

function bdd_prim_forward(op::ConstructorEqOp, args, env::Env, available_information::BDD, state::BDDEvalState)
    # Evaluate both arguments.
    first_arg_results, first_arg_used_information = traced_bdd_forward(args[1], env, available_information, state, 0)
    bdd_bind(first_arg_results, available_information, first_arg_used_information, state) do arg1, arg1_guard
        second_arg_results, second_arg_used_information = traced_bdd_forward(args[2], env, available_information & arg1_guard, state, 1)
        bdd_bind(second_arg_results, available_information, second_arg_used_information, state) do arg2, arg2_guard
            if arg1.constructor == arg2.constructor
                return World[(Pluck.TRUE_VALUE, state.BDD_TRUE)], state.BDD_TRUE
            else
                return World[(Pluck.FALSE_VALUE, state.BDD_TRUE)], state.BDD_TRUE
            end
        end
    end
end

function bdd_prim_forward(op::GetConfig, args, env::Env, available_information::BDD, state::BDDEvalState)
    sym, used_information = traced_bdd_forward(args[1], env, available_information, state, 0)
    bdd_bind(sym, available_information, used_information, state) do sym, sym_guard
        return World[(to_value(getfield(state.state_vars, sym)), sym_guard)], state.BDD_TRUE
    end
end

function bdd_prim_forward(op::FloatDivOp, args, env::Env, available_information::BDD, state::BDDEvalState)
    bdd_prim_forward_simple((x, y) -> x / y, op, args, env, available_information, state)
end
function bdd_prim_forward(op::FloatMulOp, args, env::Env, available_information::BDD, state::BDDEvalState)
    bdd_prim_forward_simple((x, y) -> x * y, op, args, env, available_information, state)
end
function bdd_prim_forward(op::FloatAddOp, args, env::Env, available_information::BDD, state::BDDEvalState)
    bdd_prim_forward_simple((x, y) -> x + y, op, args, env, available_information, state)
end
function bdd_prim_forward(op::FloatSubOp, args, env::Env, available_information::BDD, state::BDDEvalState)
    bdd_prim_forward_simple((x, y) -> x - y, op, args, env, available_information, state)
end
# function bdd_prim_forward(op::FloatRoundOp, args, env::Env, available_information::BDD, state::BDDEvalState)
#     bdd_prim_forward_simple(x -> to_value(round(Int,x)), op, args, env, available_information, state)
# end
function bdd_prim_forward(op::FloatPowOp, args, env::Env, available_information::BDD, state::BDDEvalState)
    bdd_prim_forward_simple((x, y) -> x^y, op, args, env, available_information, state)
end
function bdd_prim_forward(op::FloatLessOp, args, env::Env, available_information::BDD, state::BDDEvalState)
    bdd_prim_forward_simple((x, y) -> x < y ? Pluck.TRUE_VALUE : Pluck.FALSE_VALUE, op, args, env, available_information, state)
end

function bdd_prim_forward(op::FloatCosOp, args, env::Env, available_information::BDD, state::BDDEvalState)
    bdd_prim_forward_simple(x -> isfinite(x) ? cos(x) : 0., op, args, env, available_information, state)
end
function bdd_prim_forward(op::FloatSinOp, args, env::Env, available_information::BDD, state::BDDEvalState)
    bdd_prim_forward_simple(x -> isfinite(x) ? sin(x) : 0., op, args, env, available_information, state)
end

function bdd_prim_forward_simple(f, op, args, env::Env, available_information::BDD, state::BDDEvalState)
    length(args) == 0 && return World[(f(), state.BDD_TRUE)], state.BDD_TRUE

    # 1+ args
    first_arg_results, first_arg_used_information = traced_bdd_forward(args[1], env, available_information, state, 0)
    bdd_bind(first_arg_results, available_information, first_arg_used_information, state) do arg1, arg1_guard
        length(args) == 1 && return World[(f(arg1), state.BDD_TRUE)], state.BDD_TRUE

        # 2+ args
        second_arg_results, second_arg_used_information = traced_bdd_forward(args[2], env, arg1_guard & available_information, state, 1)
        bdd_bind(second_arg_results, available_information, second_arg_used_information, state) do arg2, arg2_guard
            @assert length(args) == 2
            return World[(f(arg1, arg2), state.BDD_TRUE)], state.BDD_TRUE
        end
    end
end




function bdd_forward(expr::Var, env::Env, available_information::BDD, state::BDDEvalState)
    # Look up the variable in the environment.
    if expr.idx > length(env)
        @warn "Variable $expr not found in environment; shaving off probability."
        return World[], state.BDD_TRUE
    end

    v = env[expr.idx]
    if v isa BDDThunk || v isa BDDThunkUnion
        return evaluate(v, available_information, state)
    else
        # Does this case ever arise? One example is that for recursive calls,
        # we create a closure (not a thunk) and store it in the environment.
        return World[(v, state.BDD_TRUE)], state.BDD_TRUE
    end
end

function bdd_forward(expr::Defined, env::Env, available_information::BDD, state::BDDEvalState)
    # Execute Defined with a blanked out environment.
    return traced_bdd_forward(Pluck.get_def(expr.name).expr, Pluck.EMPTY_ENV, available_information, state, 0)
end

function bdd_forward(expr::Root, env::Env, available_information::BDD, state::BDDEvalState)
    return bdd_forward(expr.body, env, available_information, state)
end

function bdd_forward(expr::ConstReal, env::Env, available_information::BDD, state::BDDEvalState)
    return World[(expr.val, state.BDD_TRUE)], state.BDD_TRUE
end

function bdd_forward(expr::ConstSymbol, env::Env, available_information::BDD, state::BDDEvalState)
    return World[(expr.name, state.BDD_TRUE)], state.BDD_TRUE
end

function bdd_forward(expr; available_information=nothing, manual_state=nothing, return_state=false, env=Pluck.EMPTY_ENV, show_bdd = false, show_bdd_size = false, record_bdd_json = false, cfg=nothing, return_bdd = false, kwargs...)
    !isnothing(cfg) && @assert isempty(kwargs)
    cfg = isnothing(cfg) ? BDDEvalStateConfig(;kwargs...) : cfg
    state = isnothing(manual_state) ? BDDEvalState(cfg) : manual_state
    parsed = parse_expr(expr)

    # state.dirty && reset_state!(state)
    # state.dirty = true
    state.start_time = time()
    state.manager.start_time = state.start_time
    state.manager.time_limit = state.time_limit
    start_time_limit(state.manager, state.time_limit)

    available_information = isnothing(available_information) ? state.BDD_TRUE : available_information

    ret, used_information = try 
        traced_bdd_forward(parsed, env, available_information, state, 0)
    catch e
        if e isa StackOverflowError
            state.hit_limit = true
            World[], state.BDD_TRUE
        else
            rethrow(e)
        end
    end
    
    
    state.stats.time = time() - state.start_time
    state.stats.hit_limit = state.hit_limit

    if state.hit_limit
        # if !isempty(ret)
        #     @warn "BDD forward hit time limit but had nonempty result"
        # end
        ret = World[]
    end

    stop_time_limit(state.manager)
    # Get bdd size
    if show_bdd_size
        println("BDD sizes: $([(ret, Int(RSDD.bdd_size(bdd))) for (ret, (bdd)) in ret])")
        @show state.stats.num_forward_calls
    end
    # Trying a model count of each possibility.
    if show_bdd
        results = [(v, repr(bdd), RSDD.bdd_wmc(bdd, state.weights)) for (v, bdd) in ret]
        used_information = repr(used_information)
    else
        results = [(v, RSDD.bdd_wmc(bdd, state.weights)) for (v, bdd) in ret]
    end

    if state.record_json
        dir = timestamp_dir(; base = "out/bdd")
        write_out(state.viz, joinpath(dir, "bdd_forward.json"))
        println(webaddress("html/bdd_forward.html", joinpath(dir, "bdd_forward.json"), false))
    end

    free_state!(state)

    if record_bdd_json || return_bdd
        true_results = findall(x -> x[1] == Pluck.TRUE_VALUE, ret)
        @assert length(true_results) == 1 "Expected exactly one true result, got $(length(true_results))"
        bdd = ret[true_results[1]][2]
        record_bdd_json && record_bdd(state, bdd)
        return_bdd && return results, state, bdd
    end


    return_state && return results, state

    return show_bdd ? (results, used_information) : results
end

function bdd_forward_pretty(expr; max_depth = nothing, eval_state = BDDEvalState(; max_depth))
    worlds, used_information = bdd_forward(parse_expr(expr), Pluck.EMPTY_ENV, eval_state.BDD_TRUE, eval_state)
    weighted_worlds = [(val, RSDD.bdd_wmc(bdd, eval_state.weights)) for (val, bdd) in worlds]
    println("weighted_worlds: $weighted_worlds")
    println("BDD sizes: $([(val, Int(RSDD.bdd_size(bdd))) for (val, bdd) in worlds])")

    for (val, bdd) in worlds
        println(val, " ", bdd)
    end

    println("used_information: $used_information")

    # free_bdd_manager(eval_state.manager)
    # free_wmc_params(eval_state.weights)
    return worlds
end

function bdd_normalize(results)
    probabilities = [res[2] for res in results]
    total = sum(probabilities)
    return [(res[1], res[2] / total) for res in results]
end

function io_constrain(expr, io, cfg::BDDEvalStateConfig)
    expr = io_equality_expr(expr, io.inputs, io.output; equality_fn = cfg.root_equality_fn)
    # @show expr
    res, eval_state = cfg.bdd_forward_fn(expr; cfg, return_state = true)
    free_state!(eval_state)
    # @show res
    p = get_true_result(res) # could alternatively bdd_normalize this btw
    # @show p
    return IOConstrainResult(log(p), eval_state.stats)
    # return log(p), eval_state
end

function get_true_result(results)
    for (val, prob) in results
        if val == Pluck.TRUE_VALUE || val == true
            return prob
        end
    end
    return 0.0
end

function bdd_constrain(expr, inputs, output; cfg=nothing, kwargs...)
    equality_fn = !isnothing(cfg) ? cfg.root_equality_fn : get(kwargs, :root_equality_fn, "old_list_eq")
    expr = io_equality_expr(expr, inputs, output; equality_fn)
    res, eval_state = bdd_forward(expr; cfg, kwargs..., return_state=true)
    return log(get_true_result(res)), eval_state.stats
end


function get_result(results, output)
    for (val, prob) in results
        if val == output
            return prob
        end
    end
    return 0.0
end


function make_uniform(options)
    # Construct a nested sequence of coin flips that returns the expression in options[i] with probability 1/length(options).
    if length(options) == 1
        return options[1]
    else
        flip_scrutinee = PrimOp(FlipOp(), [ConstReal(1.0 / length(options))])
        constructors = [:True, :False]
        cases = Dict(:True => options[1], :False => make_uniform(options[2:end]))
        return CaseOf(flip_scrutinee, cases, constructors)
    end
end

function make_uniform_nat(n)
    # Construct a nested sequence of coin flips that returns the expression in options[i] with probability 1/length(options).
    if n == 0
        return Construct(nat, :O, [])
    else
        flip_scrutinee = PrimOp(FlipOp(), [ConstReal(1.0 / (n+1))])
        constructors = [:True, :False]
        cases = Dict(:True => Construct(nat, :O, []), :False => Construct(nat, :S, [make_uniform_nat(n-1)]))
        return CaseOf(flip_scrutinee, cases, constructors)
    end
end

function make_uniform_fast(options)
    # Construct a nested sequence of coin flips that returns the expression in options[i] with probability 1/length(options).
    if length(options) == 1
        return options[1]
    else
        midpoint = div(length(options), 2)
        # coin flip for "are we in the first half?"
        flip_scrutinee = PrimOp(FlipOp(), [ConstReal(midpoint / length(options))])
        cases = Dict(:True => make_uniform_fast(options[1:midpoint]), :False => make_uniform_fast(options[midpoint+1:end]))
        return CaseOf(flip_scrutinee, cases, [:True, :False])
    end
end

function make_uniform_nat_fast(n)
    make_uniform_fast(map(i -> parse_expr("$i"), 1:n))
end



# function make_uniform_nat_fast(n)
#     # Construct a nested sequence of coin flips that returns the expression in options[i] with probability 1/length(options).
#     if n == 0
#         return Construct(nat, :O, [])
#     else
#         first_half = div(n, 2)
#         second_half = n - first_half
#         flip_scrutinee = PrimOp(FlipOp(), [ConstReal(1.0 / (n+1))])
#         # constructors = [:True, :False]
#         # cases = Dict(:True => Construct(nat, :O, []), :False => Construct(nat, :S, [make_uniform_nat(n-1)]))
#         # return CaseOf(flip_scrutinee, cases, constructors)
#     end
# end



function synthesis_defs()
    @define "eq_nat" "(Y (λ rec m n -> (case m of O => (case n of O => true | S => (λ _ -> false)) | S => (λ mpred -> (case n of O => false | S => (λ npred -> (rec mpred npred)))))))"
    @define "my_and" "(λ x y -> (case x of True => y | False => false))"
    @define "same_len_list_eq" "(Y (λ rec xs ys -> (case xs of Nil => true | Cons => (λ xhd xtl -> (case ys of Cons => (λ yhd ytl -> (my_and (eq_nat xhd yhd) (rec xtl ytl))))))))"
    @define "my_list_eq" "(λ xs ys -> (my_and (eq_nat (length xs) (length ys)) (same_len_list_eq xs ys)))"

    @define "length_eq" "(λ xs ys -> (eq_nat (length xs) (length ys)))"

    @define "old_list_eq" "(Y (λ rec xs ys -> (case xs of Nil => (case ys of Nil => true | Cons => (λ _ _ -> false)) | Cons => (λ xhd xtl -> (case ys of Nil => false | Cons => (λ yhd ytl -> (my_and (eq_nat xhd yhd) (rec xtl ytl))))))))"

    # fill a list of given length with a given value
    @define "fill" "(Y (λ rec n val -> (case n of O => (Nil) | S => (λp -> (Cons val (rec p val))))))"
    @define "fillrand" "(Y (λ rec n -> (case n of O => (Nil) | S => (λp -> (Cons make_random_digit (rec p))))))"

    # replace make_random_digit and randlistdigit (which implicitly replace make_random_list)
    # Note random_digit is a primop so it can't be replaced.
    # DIGITS = [parse_expr("$(a)") for a = '0':'9']
    # DEFINITIONS[:make_random_digit] = Pluck.Definition(:make_random_digit, make_uniform(DIGITS), nothing, true)
    DEFINITIONS[:make_random_digit] = Pluck.Definition(:make_random_digit, make_uniform_nat(9), nothing)
    @define "randlistdigit" "((Y (λ rec unit -> (if (flip 0.5) (Nil) (Cons make_random_digit (rec unit))))) (Unit))"



end

