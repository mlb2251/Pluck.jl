force_thunks(_::Nothing) = nothing
force_thunks(_::Nothing, _) = nothing
force_thunks(res::LazyKCResult) = force_thunks(res.worlds, res.state)

"""
Process thunks into fully resolved values.
"""
function force_thunks(worlds, state)
    # Queue of (value, bdd) pairs to process
    queue = worlds
    # Final set of fully resolved (value, bdd) pairs
    resolved = Vector{Tuple{Any, BDD}}()

    while !isempty(queue)
        (current_val, path_condition) = pop!(queue)
        bdd_is_false(path_condition) && continue
        # Find first unresolved thunk or IntDist in the value tree
        thunk_path = find_first_thunk(current_val)
        intdist_path = isnothing(thunk_path) ? find_first_intdist(current_val) : nothing
        
        if isnothing(thunk_path) && isnothing(intdist_path)
            # No more thunks or IntDists - this value is fully resolved
            bdd_is_false(path_condition) || push!(resolved, (current_val, path_condition))
            continue
        end

        if !isnothing(thunk_path)
            # Get the thunk at the path
            thunk = get_value_at_path(current_val, thunk_path)
            
            # Evaluate the thunk
            sub_results = toplevel_evaluate(thunk, state; path_condition)
            if isnothing(sub_results.worlds)
                # A limit was hit during evaluation, treat this path as infeasible
                continue
            end
            
            # For each possible result of the thunk evaluation
            for (sub_val, sub_bdd) in sub_results.worlds
                # Create a copy of the value with this thunk replaced
                new_val = replace_at_path(current_val, thunk_path, sub_val)
                # Add to queue with conjunction of bdds
                push!(queue, (new_val, path_condition & sub_bdd))
            end
        elseif !isnothing(intdist_path)
            intdist = get_value_at_path(current_val, intdist_path)::IntDist
            sub_results = enumerate_int_dist(intdist, path_condition, state.manager)
            for (sub_val, sub_bdd) in sub_results
                new_val = replace_at_path(current_val, intdist_path, NativeValue(sub_val))
                push!(queue, (new_val, sub_bdd))
            end
        end
    end

    return reverse(resolved)
end

# Helper function to find first thunk in a value tree using DFS
function find_first_thunk(val::Value, path::Vector{Int} = Int[])
    # Check direct arguments first
    for (i, arg) in enumerate(val.args)
        if arg isa Thunk
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


find_first_thunk(val, path = Int[]) = nothing

# Helper function to find first IntDist in a value tree using DFS
function find_first_intdist(val::Value, path::Vector{Int} = Int[])
    for (i, arg) in enumerate(val.args)
        if arg isa IntDist
            push!(path, i)
            return path
        elseif arg isa Value
            sub_path = find_first_intdist(arg, copy(path))
            if !isnothing(sub_path)
                pushfirst!(sub_path, i)
                return sub_path
            end
        end
    end
    return nothing
end

function find_first_intdist(val::IntDist, path = Int[])
    return path
end

function find_first_intdist(val::PExpr{T}, path = Int[]) where T <: Head
    for (i, arg) in enumerate(val.args)
        if arg isa IntDist
            push!(path, i)
            return path
        end
        sub_path = find_first_intdist(arg, copy(path))
        if !isnothing(sub_path)
            pushfirst!(sub_path, i)
            return sub_path
        end
    end
    return nothing
end

find_first_intdist(val, path = Int[]) = nothing

# Helper to get value at a path in the value tree
function get_value_at_path(val, path)
    isempty(path) && return val
    val = val.args[path[1]]
    get_value_at_path(val, view(path, 2:length(path)))
end



function replace_at_path(val::IntDist, path::Vector{Int}, new_val)
    @assert isempty(path)
    new_val
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