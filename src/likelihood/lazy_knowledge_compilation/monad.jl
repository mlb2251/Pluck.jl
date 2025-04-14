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
function pure_monad(val::T, state)::GuardedWorlds where T
    return World[(val, state.manager.BDD_TRUE)], state.manager.BDD_TRUE
end

"""
Constructs a pair of worlds, one with the condition true and one with the condition false.
"""
function if_then_else_monad(val_if_true::T1, val_if_false::T2, condition::BDD, state)::GuardedWorlds where {T1, T2}
    return World[(val_if_true, condition), (val_if_false, !condition)], state.manager.BDD_TRUE
end

"""
Condition every world in a set of worlds on a condition
"""
function condition_worlds(worlds::Vector{World}, condition::BDD)
    return [(val, guard & condition) for (val, guard) in worlds]
end

"""
GuardedWorlds{X} = is a monad (M X)
M X = GuardedWorlds{X} = Tuple{Vector{World{X}}, BDD}

pure :: a -> M a
bind :: M a -> (a -> M b) -> M b
"""
function bind_monad(cont::F, guarded_worlds, path_condition, state) where F <: Function
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
        post_world = condition_worlds(cont_worlds, pre_guard)
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

function join_worlds(result_sets::Vector{Vector{World}}, state::LazyKCState) #::Vector{Tuple{Tuple{Vector{Tuple{T, BDD}}, BDD}, BDD}} where T
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
                    uniq_world_guards[uniq_world_indices[world]] |= guard
                end
            end
            if length(uniq_worlds) > 1
                overall_guard = reduce((x, y) -> x | y, uniq_world_guards)
                overall_args = [(LazyKCThunkUnion([(world.args[i], bdd) for (world, bdd) in zip(uniq_worlds, uniq_world_guards)], state)) for i = 1:length(Pluck.args_of_constructor[constructor])]
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

    return join_results
end