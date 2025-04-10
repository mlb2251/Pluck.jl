"""
Binds a continuation to the results of the first stage.
"""
function bind_monad(cont, worlds, available_information, used_information, state)
    result_sets = Vector{Tuple{GuardedWorlds, BDD}}()
    for (val, result_guard) in worlds
        path_condition = state.cfg.disable_path_conditions ? state.manager.BDD_TRUE : result_guard
        cont_worlds, cont_used_info = cont(val, path_condition)
        push!(result_sets, ((cont_worlds, cont_used_info), result_guard))
    end
    return join_monad(result_sets, used_information, available_information, state)
end

# This is the 'join' of the monad.
# M X = Tuple{Vector{Tuple{X, BDD}}, BDD} = ([(X, Guard)], Used)
# M (M X) = ([(([(X, InnerGuard)], InnerUsed)), OuterGuard)], Used)
function join_monad(result_sets, used_information::BDD, available_information::BDD, state::LazyKCState) #::Vector{Tuple{Tuple{Vector{Tuple{T, BDD}}, BDD}, BDD}} where T
    join_results = Vector{World}()
    index_of_result = Dict{AbstractValue, Int}()
    results_for_constructor = Dict{Symbol, Vector{Tuple{Value, BDD}}}()
    int_dist_results = Vector{Tuple{IntDist, BDD}}()

    for ((results, used_info), outer_guard) in result_sets
        if !state.cfg.disable_used_information
            used_information = used_information & bdd_implies(outer_guard, used_info)
        end
        for (result, inner_guard) in results
            inner_and_outer = inner_guard & outer_guard
            if state.cfg.use_thunk_unions && result isa Value
                constructor = result.constructor
                if !haskey(results_for_constructor, constructor)
                    results_for_constructor[constructor] = [(result, inner_and_outer)]
                else
                    push!(results_for_constructor[constructor], (result, inner_and_outer))
                end
            elseif result isa Closure || result isa FloatValue || result isa Value
                result_index = Base.get!(index_of_result, result, length(join_results) + 1)
                if result_index > length(join_results)
                    push!(join_results, (result, inner_and_outer))
                else
                    new_guard = join_results[result_index][2] | inner_and_outer
                    join_results[result_index] = (join_results[result_index][1], new_guard)
                end
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
                    uniq_world_guards[uniq_world_indices[world]] = uniq_world_guards[uniq_world_indices[world]] | guard
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

    return join_results, used_information
end