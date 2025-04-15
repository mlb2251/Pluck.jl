"""
Shaves off probability.
Constructs an empty set of worlds (zero probability)
"""
function shave_probabilty(state)::GuardedWorlds
    return World[], state.manager.BDD_TRUE
end

"""
Construct a single world with the given value. Lifts a deterministic
value into the monad.
"""
@inline function pure_monad(val, state)
    return World[(val, state.manager.BDD_TRUE)], state.manager.BDD_TRUE
end

"""
Constructs a pair of worlds, one with the condition true and one with the condition false.
"""
@inline function if_then_else_monad(val_if_true, val_if_false, condition, state)
    return World[(val_if_true, condition), (val_if_false, !condition)], state.manager.BDD_TRUE
end

"""
Condition every world in a set of worlds on a condition
"""
@inline function condition_worlds!(worlds, condition)
    for i in eachindex(worlds)
        worlds[i] = (worlds[i][1], worlds[i][2] & condition)
    end
    return worlds
end

"""
GuardedWorlds{X} = is a monad (M X)
M X = GuardedWorlds{X} = Tuple{Vector{World{X}}, BDD}

pure :: a -> M a
bind :: M a -> (a -> M b) -> M b
"""
function bind_monad(cont::F, guarded_worlds, path_condition::BDD, state::LazyKCState) where F <: Function
    pre_worlds, used_information = guarded_worlds

    post_worlds = Vector{Vector{World}}()
    for (val, pre_guard) in pre_worlds
        cont_path_condition = path_condition & pre_guard

        if bdd_is_false(cont_path_condition)
            # you can reuse this part of the result if you too can prove false
            # when you add pre_guard to your path condition.
            used_information &= bdd_implies(pre_guard, state.manager.BDD_FALSE)
            continue
        end

        state.cfg.disable_path_conditions && (cont_path_condition = state.manager.BDD_TRUE)
        
        cont_worlds, cont_used_info = cont(val, cont_path_condition, state)

        # Condition on the guard. We don't condition on cont_path_condition – if
        # we were doing that we would have just included path condition in the basic
        # pure_monad worlds directly. The reason we don't do either of those things
        # is because we want to cache our results.
        post_world = condition_worlds!(cont_worlds, pre_guard)
        push!(post_worlds, post_world)

        # you can reuse this part of the result if you can prove 
        # the info needed by the continuation, given the pre guard
        # as well as your current path condition.
        used_information &= bdd_implies(pre_guard, cont_used_info)
    end

    join_results = join_worlds(post_worlds, state)

    return join_results, used_information
end


"""
join :: M (M X) -> M X
"""
function join_monad(guarded_worlds::GuardedWorlds, path_condition, state)
    bind_monad(identity, guarded_worlds, path_condition, state)
end

function join_worlds(result_sets, state::LazyKCState)
    join_results = Vector{World}()
    index_of_result = Dict{AbstractValue, Int}()
    results_for_constructor = Dict{Symbol, Vector{Tuple{Value, BDD}}}()
    int_dist_results = Vector{Tuple{IntDist, BDD}}()

    for results in result_sets
        for (result, inner_and_outer) in results
            if state.cfg.use_thunk_unions && result isa Value
                constructor = result.constructor
                res = get!(Vector{Tuple{Value, BDD}}, results_for_constructor, constructor)
                push!(res, (result, inner_and_outer))
            elseif result isa Closure || result isa FloatValue || result isa Value
                result_index = Base.get!(index_of_result, result, length(join_results) + 1)
                if result_index > length(join_results)
                    push!(join_results, (result, inner_and_outer))
                    continue
                end
                old_guard = join_results[result_index][2]
                new_guard = old_guard | inner_and_outer
                join_results[result_index] = (result, new_guard)
            elseif result isa IntDist
                push!(int_dist_results, (result, inner_and_outer))
            else
                error("join_monad found a result that is not a Value, Closure, or Float64: $result")
            end
        end
    end

    if state.cfg.use_thunk_unions
        for constructor in keys(results_for_constructor)
            world_of_value = Dict{Value, World}()
            for (value, guard) in results_for_constructor[constructor]
                old_world = get(world_of_value, value, nothing)
                old_guard = isnothing(old_world) ? state.manager.BDD_FALSE : old_world[2]
                new_guard = old_guard | guard
                world_of_value[value] = (value, new_guard)
            end
            if length(world_of_value) <= 1
                append!(join_results, World[Tuple(world) for world in values(world_of_value)])
                continue
            end

            # multiple worlds case
            overall_guard = state.manager.BDD_FALSE
            thunks_of_arg = [World[] for _ in 1:length(Pluck.args_of_constructor[constructor])]
            for (val, guard) in values(world_of_value)
                overall_guard |= guard
                for (i, arg) in enumerate(val.args)
                    push!(thunks_of_arg[i], (arg, guard))
                end
            end
            overall_args = [LazyKCThunkUnion(thunks, state) for thunks in thunks_of_arg]

            # overall_args = map(1:length(Pluck.args_of_constructor[constructor])) do i
            #     thunks = [(world.args[i], bdd) for (world, bdd) in values(world_of_value)]
            #     LazyKCThunkUnion(thunks, state)
            # end
            overall_value = Value(constructor, overall_args)
            push!(join_results, (overall_value, overall_guard))
        end
    end

    if length(int_dist_results) > 0
        push!(join_results, combine_int_dists(int_dist_results, state))
    end

    return join_results
end