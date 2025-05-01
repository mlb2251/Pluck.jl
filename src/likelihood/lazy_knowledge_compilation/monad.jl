"""
Shaves off probability. Used for the case where the path condition is not necessarily
false, but rather there's some sort of program error (e.g. scrutinee not in case expression).
"""
function program_error_worlds(state)::GuardedWorlds
    return World[], state.manager.BDD_TRUE
end

"""
Shaves off probability. Used for the case where the path condition is false. This result
can be reused if you can prove false with your path condition.
"""
function false_path_condition_worlds(state)::GuardedWorlds
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
Condition every world in a set of worlds on a condition
"""
function condition_worlds(worlds, condition)
    return World[(val, guard & condition) for (val, guard) in worlds]
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
    nested_worlds = Vector{Tuple{GuardedWorlds, BDD}}()
    for (pre_val, pre_guard) in pre_worlds
        inner_path_condition = state.cfg.disable_path_conditions ? state.manager.BDD_TRUE : path_condition & pre_guard
        if !state.cfg.disable_used_information && bdd_is_false(inner_path_condition)
            # you can reuse this part of the result if you can prove false with your path condition + pre_guard
            push!(nested_worlds, (false_path_condition_worlds(state), pre_guard))
            continue
        end

        if cont_state
            post_worlds, post_used_info = cont(pre_val, inner_path_condition, state)
        else
            post_worlds, post_used_info = cont(pre_val, inner_path_condition)
        end
        push!(nested_worlds, ((post_worlds, post_used_info), pre_guard))
    end
    nested_worlds = (nested_worlds, pre_used_info)
    return join_monad(nested_worlds, state)
end

"""
join :: M (M a) -> M a
"""
function join_monad(nested_worlds, state::LazyKCState) #::Vector{Tuple{Tuple{Vector{Tuple{T, BDD}}, BDD}, BDD}} where T
    nested_worlds, pre_used_info = nested_worlds

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

    """
    Now lets join the resulting worlds.
    """
    join_results = Vector{World}()
    index_of_result = Dict{AbstractValue, Int}()
    results_for_constructor = Dict{Symbol, Vector{Tuple{Value, BDD}}}()
    int_dist_results = Vector{Tuple{IntDist, BDD}}()

    for ((post_worlds, _), pre_guard) in nested_worlds
        for (post_val, post_guard) in post_worlds
            pre_and_post = post_guard & pre_guard
            if state.cfg.use_thunk_unions && post_val isa Value
                constructor = post_val.constructor
                res = get!(Vector{Tuple{Value, BDD}}, results_for_constructor, constructor)
                push!(res, (post_val, pre_and_post))
            elseif post_val isa Closure || post_val isa Value || post_val isa NativeValue
                result_index = Base.get!(index_of_result, post_val, length(join_results) + 1)
                if result_index > length(join_results)
                    push!(join_results, (post_val, pre_and_post))
                    continue
                end
                old_guard = join_results[result_index][2]
                new_guard = old_guard | pre_and_post
                join_results[result_index] = (post_val, new_guard)
            elseif post_val isa IntDist
                push!(int_dist_results, (post_val, pre_and_post))
            else
                error("join_monad found a result with an unsupported type: $(typeof(post_val)): $post_val")
            end
        end
    end

    if state.cfg.use_thunk_unions
        for constructor in keys(results_for_constructor)
            world_of_value = Dict{Value, World}()
            for (post_val, pre_and_post) in results_for_constructor[constructor]
                old_world = get(world_of_value, post_val, nothing)
                old_guard = isnothing(old_world) ? state.manager.BDD_FALSE : old_world[2]
                new_guard = old_guard | pre_and_post
                world_of_value[post_val] = (post_val, new_guard)
            end
            if length(world_of_value) <= 1
                append!(join_results, World[Tuple(world) for world in values(world_of_value)])
                continue
            end

            # multiple worlds case
            overall_guard = state.manager.BDD_FALSE
            thunks_of_arg = [World[] for _ in 1:length(Pluck.args_of_constructor[constructor])]
            for (post_val, pre_and_post) in values(world_of_value)
                overall_guard |= pre_and_post
                for (i, arg) in enumerate(post_val.args)
                    push!(thunks_of_arg[i], (arg, pre_and_post))
                end
            end
            overall_args = [LazyKCThunkUnion(thunks, state) for thunks in thunks_of_arg]
            overall_value = Value(constructor, overall_args)
            push!(join_results, (overall_value, overall_guard))
        end
    end
    if length(int_dist_results) > 0
        push!(join_results, combine_int_dists(int_dist_results, state))
    end

    return join_results, used_information
end


function bind_compile(cont::F, expr::PExpr, env, path_condition, state, strict_order_index) where F <: Function
    pre_worlds = traced_compile_inner(expr, env, path_condition, state, strict_order_index)
    return bind_monad(cont, pre_worlds, path_condition, state)
end


# Not tested or used right now.
function bind_compile_many(cont::F, exprs::Vector{PExpr}, env, path_condition, state::LazyKCState, strict_order_indices::Vector{Int}) where F <: Function
    isempty(exprs) && return cont(Any[], path_condition)
    bind_compile(exprs[1], env, path_condition, state, strict_order_indices[1]) do head_val, path_condition
        bind_compile_many(exprs[2:end], env, path_condition, state, strict_order_indices[2:end]) do tail_vals, path_condition
            return cont(Any[head_val; tail_vals], path_condition)
        end
    end
end
