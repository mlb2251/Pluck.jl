const ERROR_VALUE::Value = Value(:Error)
iserror(val) = val isa Value && val.constructor == :Error

const GIVEN_VALUE::Value = Value(:Given)
isgiven(val) = val isa Value && val.constructor == :Given

posterior_exclude(val) = iserror(val) || isgiven(val)

"""
Shaves off probability. Used for the case where the path condition is not necessarily
false, but rather there's some sort of program error (e.g. scrutinee not in case expression).
"""
function program_error_worlds(state::LazyKCState)::GuardedWorlds
    return pure_monad(ERROR_VALUE, state.manager.BDD_TRUE, state)
end

function given_worlds(state::LazyKCState)::GuardedWorlds
    return pure_monad(GIVEN_VALUE, state.manager.BDD_TRUE, state)
end

"""
Some inference error eg a depth limit was hit
"""
function inference_error_worlds(state::LazyKCState)::GuardedWorlds
    return World[], state.manager.BDD_TRUE
end


"""
Shaves off probability. Used for the case where the path condition is false. This result
can be reused if you can prove false with your path condition.
"""
function false_path_condition_worlds(state::LazyKCState)::GuardedWorlds
    return World[], state.manager.BDD_FALSE
end

"""
Construct a single world with the given value. Lifts a deterministic
value into the monad.
"""
function pure_monad(val, path_condition, state::LazyKCState)
    return World[(val, state.manager.BDD_TRUE)], state.manager.BDD_TRUE
end

"""
Constructs a pair of worlds, one with the condition true and one with the condition false.
"""
function if_then_else_monad(val_if_true, val_if_false, condition, path_condition, state::LazyKCState)
    return World[(val_if_true, condition), (val_if_false, !condition)], state.manager.BDD_TRUE
end

"""
GuardedWorldsT{X} = is a monad (M X)
M X = GuardedWorldsT{X} = Tuple{Vector{WorldT{X}}, BDD}

pure :: a -> M a
bind :: M a -> (a -> M b) -> M b
join :: M (M a) -> M a
"""

function bind_monad(cont::F, pre_worlds, path_condition, state::LazyKCState; cont_state=false) where F <: Function
    pre_worlds, pre_used_info = pre_worlds

    # Get or lazily create the shared CDCL solver
    solver = _get_shared_solver!(state)

    nested_worlds = Vector{Tuple{GuardedWorlds, BDD}}()
    for (pre_val, pre_guard) in pre_worlds
        state.stats.hit_limit && return inference_error_worlds(state)

        inner_path_condition = path_condition & pre_guard

        # Check satisfiability incrementally: push one assumption onto the solver's
        # trail at a new decision level. Children push above this level; we pop after.
        # cdcl_new_selector! returns: >0 = selector literal, 0 = trivially true, -1 = trivially false
        pushed = false
        is_unsat = if solver isa CDCLSolver
            sel_lit = cdcl_new_selector!(solver, pre_guard.sat_expr)
            if sel_lit == Int32(-1)
                true  # guard is trivially false
            elseif sel_lit == Int32(0)
                false  # guard is trivially true, no assumption needed
            else
                result = cdcl_push_assumption!(solver, sel_lit)
                pushed = (result === :sat)
                result === :unsat
            end
        else
            bdd_is_false(inner_path_condition)
        end

        # Cache the solver's result on the BDD so bdd_is_false() hits the cache
        inner_path_condition.sat_known = is_unsat ? Int8(-1) : Int8(1)

        if is_unsat
            push!(nested_worlds, (false_path_condition_worlds(state), pre_guard))
            continue
        end

        # Assumption is on the solver's trail; recurse
        if cont_state
            post_worlds, post_used_info = cont(pre_val, inner_path_condition, state)
        else
            post_worlds, post_used_info = cont(pre_val, inner_path_condition)
        end

        if pushed
            cdcl_pop_assumption!(solver)
        end

        push!(nested_worlds, ((post_worlds, post_used_info), pre_guard))
    end
    nested_worlds = (nested_worlds, pre_used_info)
    return join_monad(nested_worlds, state)
end

"""
Get or lazily create the shared CDCL solver on LazyKCState.
"""
function _get_shared_solver!(state::LazyKCState)::Union{CDCLSolver, Symbol}
    state.cdcl_solver !== nothing && return state.cdcl_solver
    solver = CDCLSolver()
    state.cdcl_solver = solver
    return solver
end

struct JoinResults
    join_results::Vector{World}
    index_of_result::Dict{AbstractValue, Int}
    results_for_constructor::Dict{Tuple{Symbol, Int}, Vector{Tuple{Value, BDD}}}
    int_dist_results::Vector{Tuple{Any, BDD}}
    JoinResults() = new(Vector{World}(), Dict{AbstractValue, Int}(), Dict{Tuple{Symbol, Int}, Vector{Tuple{Value, BDD}}}(), Vector{Tuple{Any, BDD}}())
end

"""
join :: M (M a) -> M a
"""
function join_monad(nested_worlds, state::LazyKCState) #::Vector{Tuple{Tuple{Vector{Tuple{T, BDD}}, BDD}, BDD}} where T
    nested_worlds, pre_used_info = nested_worlds
    used_information = join_used_information(nested_worlds, pre_used_info, state)

    # Now lets join the resulting worlds.
    join_results = JoinResults()

    join_values!(nested_worlds, join_results, state)

    if state.cfg.use_thunk_unions
        join_thunk_unions!(join_results, state)
    end

    if length(join_results.int_dist_results) > 0
        push!(join_results.join_results, combine_int_dists(join_results.int_dist_results, state.manager))
    end

    return join_results.join_results, used_information
end

function join_used_information(nested_worlds, pre_used_info, state::LazyKCState)
    # first what is the total used information?
    used_information = pre_used_info
    for ((_, used_info), pre_guard) in nested_worlds
        state.cfg.disable_used_information && break
        """
        you can reuse this part of the result if you can prove 
        the info needed by the inner result (the continuation in the case of a join), given the pre_guard
        as well as your current path condition.
        """
        used_information &= bdd_implies(pre_guard, used_info)
    end
    return used_information
end

function join_values!(nested_worlds, join_results, state::LazyKCState)
    for ((post_worlds, _), pre_guard) in nested_worlds
        for (post_val, post_guard) in post_worlds
            pre_and_post = post_guard & pre_guard
            join_value!(post_val, pre_and_post, join_results, state)
        end
    end
end

function join_value!(post_val::Closure, pre_and_post, join_results, state::LazyKCState)
    join_value_simple!(post_val, pre_and_post, join_results, state)
end

function join_value!(post_val::NativeValue, pre_and_post, join_results, state::LazyKCState)
    join_value_simple!(post_val, pre_and_post, join_results, state)
end

function join_value!(post_val::Value, pre_and_post, join_results, state::LazyKCState)
    if state.cfg.use_thunk_unions
        key = (post_val.constructor, length(post_val.args))
        res = get!(Vector{Tuple{Value, BDD}}, join_results.results_for_constructor, key)
        push!(res, (post_val, pre_and_post))
        return
    end

    join_value_simple!(post_val, pre_and_post, join_results, state)
end

function join_value_simple!(post_val, pre_and_post, join_results, state::LazyKCState)
    result_index = Base.get!(join_results.index_of_result, post_val, length(join_results.join_results) + 1)
    if result_index > length(join_results.join_results)
        push!(join_results.join_results, (post_val, pre_and_post))
        return
    end
    old_guard = join_results.join_results[result_index][2]
    new_guard = old_guard | pre_and_post
    join_results.join_results[result_index] = (post_val, new_guard)
    return
end


function join_thunk_unions!(join_results, state::LazyKCState)
    for ((constructor, arity), results) in join_results.results_for_constructor
        world_of_value = Dict{Value, World}()
        for (post_val, pre_and_post) in results
            old_world = get(world_of_value, post_val, nothing)
            old_guard = isnothing(old_world) ? state.manager.BDD_FALSE : old_world[2]
            new_guard = old_guard | pre_and_post
            world_of_value[post_val] = (post_val, new_guard)
        end
        if length(world_of_value) <= 1
            append!(join_results.join_results, World[Tuple(world) for world in values(world_of_value)])
            continue
        end

        # multiple worlds case
        overall_guard = state.manager.BDD_FALSE
        thunks_of_arg = [World[] for _ in 1:arity]
        for (post_val, pre_and_post) in values(world_of_value)
            overall_guard |= pre_and_post
            for (i, arg) in enumerate(post_val.args)
                push!(thunks_of_arg[i], (arg, pre_and_post))
            end
        end
        overall_args = [LazyKCThunkUnion(thunks, state) for thunks in thunks_of_arg]
        overall_value = Value(constructor, overall_args)
        push!(join_results.join_results, (overall_value, overall_guard))
    end
end


function bind_compile(cont::F, expr, env, path_condition, state, strict_order_index) where F <: Function
    pre_worlds = traced_compile_inner(expr, env, path_condition, state, strict_order_index)
    return bind_monad(cont, pre_worlds, path_condition, state)
end