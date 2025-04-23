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
@inline function condition_worlds(worlds, condition)
    return World[(val, guard & condition) for (val, guard) in worlds]
end

"""
GuardedWorldsT{X} = is a monad (M X)
M X = GuardedWorldsT{X} = Tuple{Vector{WorldT{X}}, BDD}

pure :: a -> M a
bind :: M a -> (a -> M b) -> M b
join :: M (M a) -> M a
"""

function bind_monad(cont::F, worlds, path_condition, state) where F <: Function
    worlds, used_information = worlds
    nested_worlds = Vector{Tuple{GuardedWorlds, BDD}}()
    for (val, result_guard) in worlds
        inner_path_condition = state.cfg.disable_path_conditions ? state.manager.BDD_TRUE : path_condition & result_guard
        cont_worlds, cont_used_info = cont(val, inner_path_condition)
        push!(nested_worlds, ((cont_worlds, cont_used_info), result_guard))
    end
    nested_worlds = (nested_worlds, used_information)
    return join_monad(nested_worlds, state)
end

"""
join :: M (M a) -> M a
"""
function join_monad(nested_worlds, state::LazyKCState) #::Vector{Tuple{Tuple{Vector{Tuple{T, BDD}}, BDD}, BDD}} where T
    nested_worlds, used_information = nested_worlds
    join_results = Vector{World}()
    index_of_result = Dict{AbstractValue, Int}()
    results_for_constructor = Dict{Symbol, Vector{Tuple{Value, BDD}}}()
    int_dist_results = Vector{Tuple{IntDist, BDD}}()

    # first what is the total used information?
    for ((_, used_info), pre_guard) in nested_worlds
        state.cfg.disable_used_information && break
        """
        you can reuse this part of the result if you can prove 
        the info needed by the inner result (the continuation in the case of a join), given the pre_guard
        as well as your current path condition.
        """
        used_information &= bdd_implies(pre_guard, used_info)
    end

    for ((results, _), pre_guard) in nested_worlds
        for (result, post_guard) in results
            pre_and_post = post_guard & pre_guard
            if state.cfg.use_thunk_unions && result isa Value
                constructor = result.constructor
                if !haskey(results_for_constructor, constructor)
                    results_for_constructor[constructor] = [(result, pre_and_post)]
                else
                    push!(results_for_constructor[constructor], (result, pre_and_post))
                end
            elseif result isa Closure || result isa FloatValue || result isa Value
                result_index = Base.get!(index_of_result, result, length(join_results) + 1)
                if result_index > length(join_results)
                    push!(join_results, (result, pre_and_post))
                else
                    new_guard = join_results[result_index][2] | pre_and_post
                    join_results[result_index] = (join_results[result_index][1], new_guard)
                end
            elseif result isa IntDist
                push!(int_dist_results, (result, pre_and_post))
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