export posterior_sample, adaptive_rejection_sampling, SampleValueState

function posterior_sample(val, state)
    # First evaluate the evidence thunk to get true/false BDDs
    evidence_results, _ = evaluate(val.args[2], state.manager.BDD_TRUE, state)
    shared_thunks = LazyKCThunk[]
    n, concrete = from_value(evaluate(val.args[3], nothing, SampleValueState(nothing, [], nothing, false, state.manager, shared_thunks)))
    samples = []
    for i in 1:n
        # clear any cached results from previous sample
        for t in shared_thunks
            empty!(t.cache)
        end
        empty!(shared_thunks)
        if val.args[1] isa LazyKCThunk || val.args[1] isa LazyKCThunkUnion
            clear_thunk_cache!(val.args[1])
        end
        # Find the BDD where evidence is true
        evidence_bdd = nothing
        for (result, bdd) in evidence_results
            if result == Pluck.TRUE_VALUE || (result isa Value && result.constructor == :True)
                evidence_bdd, _ = RSDD.weighted_sample(bdd)
                break
            end
        end
    
        if isnothing(evidence_bdd) || RSDD.bdd_is_false(evidence_bdd)
            @warn "Evidence has zero probability; cannot take posterior sample."
            return []
        end
    
        # Create a sampling state that uses the evidence BDD as a constraint
        # We need to preserve the callstack from the query thunk
        query_thunk = val.args[1]
        sample_state = SampleValueState(
            evidence_bdd,
            [],
            state.var_of_callstack,
            true,
            state.manager,
            shared_thunks,
        )

        # Sample from the query under the evidence constraint
        sampled_value = evaluate(query_thunk, nothing, sample_state)
        forced = force_value(sampled_value, query_thunk.env, sample_state)
        push!(samples, forced)
    end
    return samples
end

# How to handle that some choices are irrelevant?
function adaptive_rejection_sampling(val, state)

    constraint = state.manager.BDD_TRUE
    sorted_callstacks = state.sorted_callstacks
    sorted_var_labels = state.sorted_var_labels

    shared_thunks = LazyKCThunk[]
    sample_state = SampleValueState(constraint, [], state.var_of_callstack, true, state.manager, shared_thunks)
    # clear caches on predicate/result thunks before sampling loop
    if val.args[1] isa LazyKCThunk || val.args[1] isa LazyKCThunkUnion
        clear_thunk_cache!(val.args[1])
    end
    if val.args[2] isa LazyKCThunk || val.args[2] isa LazyKCThunkUnion
        clear_thunk_cache!(val.args[2])
    end
    
    while true
        sampled_constraint, _ = RSDD.weighted_sample(constraint)
        sample_state.constraint = sampled_constraint
        sampled_pred = evaluate(val.args[2], nothing, sample_state)
        
        if sampled_pred == Pluck.TRUE_VALUE
            sample_state.lazy = false
            return evaluate(val.args[1], nothing, sample_state)
        end

        # Construct a BDD using the sampled trace.
        trace = sample_state.trace
        trace_as_bdd = sample_state.constraint
        for (callstack, result) in trace
            # Check if callstack already has a variable in the BDD.
            if !haskey(sample_state.var_of_callstack, callstack)
                # Add a new variable to the BDD.
                i = searchsortedfirst(sorted_callstacks, callstack; by = x -> x[1])
                # Insert the callstack in the sorted list.
                addr = RSDD.bdd_new_var_at_position(state.manager, i - 1, true) # Rust uses 0-indexing
                insert!(sorted_callstacks, i, callstack)
                insert!(sorted_var_labels, i, Int(bdd_topvar(addr)))
                sample_state.var_of_callstack[callstack] = addr
                RSDD.set_weight(state.manager, bdd_topvar(addr), 1.0 - callstack[2], callstack[2])
            end
            addr = sample_state.var_of_callstack[callstack]
            if result
                trace_as_bdd = RSDD.bdd_and(trace_as_bdd, addr)
            else
                trace_as_bdd = RSDD.bdd_and(trace_as_bdd, !(addr))
            end
        end

        constraint = RSDD.bdd_and(constraint, !trace_as_bdd)

        sample_state.lazy = false
        println(evaluate(val.args[1], nothing, sample_state))
        sample_state.lazy = true
        sample_state.trace = Dict{Tuple{Vector{Int}, Float64}, Bool}()
        for t in shared_thunks
            empty!(t.cache)
        end
        empty!(shared_thunks)
        @assert !RSDD.bdd_is_false(constraint) "Constraint is false..."
        println("Rejected trace. Total mass remaining: $(RSDD.bdd_wmc(constraint))")
    end

end

mutable struct SampleValueState
    constraint::Union{BDD, Nothing}
    callstack::Vector{Int}
    trace::Dict{Tuple{Vector{Int}, Float64}, Bool}
    var_of_callstack::Union{Dict{Tuple{Callstack, Float64}, BDD}, Nothing}
    manager::Union{RSDD.Manager, Nothing}
    lazy::Bool
    thunks::Vector{LazyKCThunk}
    call_frames::Vector{Any}
    def_name_stack::Vector{Symbol}

    function SampleValueState(constraint=nothing, callstack=Int[], var_of_callstack=nothing, lazy=false, manager=nothing, thunks=nothing)
        thunks_vec = isnothing(thunks) ? LazyKCThunk[] : thunks
        state = new(
            constraint,
            callstack,
            Dict{Tuple{Vector{Int}, Float64}, Bool}(),
            var_of_callstack,
            manager,
            lazy,
            thunks_vec,
            Any[],
            Symbol[],
        )
        return state
    end
end

push_call_frame!(::SampleValueState, ::Symbol, ::Any; caller_expr=nothing) = nothing
pop_call_frame!(::SampleValueState) = nothing

push_strict_frame!(::SampleValueState, ::Symbol, ::Any; caller_expr=nothing) = nothing
pop_strict_frame!(::SampleValueState) = nothing

function traced_compile_inner(expr, env, null, state::SampleValueState, strict_order_index::Int)
    push!(state.callstack, strict_order_index)
    print_enter(expr, env, state)
    result = compile_inner(expr, env, null, state)
    print_exit(expr, result, env, state)
    pop!(state.callstack)
    return result
end

function pure_monad(val, null, state::SampleValueState)
    return val
end

program_error_worlds(state::SampleValueState) = nothing
inference_error_worlds(state::SampleValueState) = nothing
false_path_condition_worlds(state::SampleValueState) = nothing

function bind_monad(cont::F, val, null, state::SampleValueState) where F <: Function
    isnothing(val) && return nothing
    return cont(val, null)
end



function evaluate(thunk::LazyKCThunk, null, state::SampleValueState)
    mgr = state.manager
    # Attempt cache hit
    if mgr !== nothing && !isempty(thunk.cache)
        worlds, guard = thunk.cache[1]
        if !bdd_is_false(guard)
            return worlds[1][1]
        end
    end

    res = evaluate_no_cache(thunk, null, state)

    if mgr !== nothing
        guarded = (Vector{World}([(res, mgr.BDD_TRUE)]), mgr.BDD_TRUE)
        empty!(thunk.cache)
        push!(thunk.cache, guarded)
    end
    return res
end

function clear_thunk_cache!(::Nothing) end
function clear_thunk_cache!(thunk::LazyKCThunk)
    empty!(thunk.cache)
    clear_env_thunk_caches(thunk.env)
end
function clear_thunk_cache!(union_thunk::LazyKCThunkUnion)
    for (t, _) in union_thunk.thunks
        clear_thunk_cache!(t)
    end
end

function clear_env_thunk_caches(env::EnvCons)
    val = env.val
    if val isa LazyKCThunk || val isa LazyKCThunkUnion
        clear_thunk_cache!(val)
    end
    clear_env_thunk_caches(env.tail)
end
clear_env_thunk_caches(::EnvNil) = nothing



function compile_inner(expr::PExpr{FlipOp}, env::Env, null::Nothing, state::SampleValueState)
    p = traced_compile_inner(expr.args[1], env, null, state, 0)
    p = p.value
    isapprox(p, 0.0) && return Pluck.FALSE_VALUE
    isapprox(p, 1.0) && return Pluck.TRUE_VALUE

    callstack_to_check = ([state.callstack..., 1], p)

    if haskey(state.trace, callstack_to_check)
        return state.trace[callstack_to_check] ? Pluck.TRUE_VALUE : Pluck.FALSE_VALUE
    end

    if state.constraint === nothing || state.var_of_callstack === nothing || !haskey(state.var_of_callstack, callstack_to_check)
        # Freely sample a value. 
        result = rand() < p
        state.trace[callstack_to_check] = result
        return result ? Pluck.TRUE_VALUE : Pluck.FALSE_VALUE
    end


    var = state.var_of_callstack[callstack_to_check]
    bdd_is_true(bdd_implies(state.constraint, var)) && return Pluck.TRUE_VALUE
    bdd_is_true(bdd_implies(state.constraint, !var)) && return Pluck.FALSE_VALUE
    result = rand() < p
    state.trace[callstack_to_check] = result
    return result ? Pluck.TRUE_VALUE : Pluck.FALSE_VALUE
end

function compile_inner(expr::PExpr{MkIntOp}, env::Env, null::Nothing, state::SampleValueState)
    bitwidth = traced_compile_inner(expr.args[1], env, null, state, 0)
    val = traced_compile_inner(expr.args[2], env, null, state, 1)
    width = bitwidth.value
    v = val.value
    bools = digits(Bool, v, base = 2, pad = width)
    return IntDist(bools)
end

function compile_inner(expr::PExpr{UniformIntOp}, env::Env, null::Nothing, state::SampleValueState)
    bitwidth = traced_compile_inner(expr.args[1], env, null, state, 0)
    width = bitwidth.value
    bits = Vector{Bool}(undef, width)

    for i = 1:width
        callstack_to_check = ([state.callstack..., i], 0.5)
        addr = nothing
        if state.var_of_callstack !== nothing && haskey(state.var_of_callstack, callstack_to_check)
            addr = state.var_of_callstack[callstack_to_check]
        end

        bit_val = rand(Bool)
        # If we have a constraint and a BDD var for this bit, respect it.
        if addr !== nothing && state.constraint !== nothing
            if bdd_is_true(bdd_implies(state.constraint, addr))
                bit_val = true
            elseif bdd_is_true(bdd_implies(state.constraint, !addr))
                bit_val = false
            end
        end

        if addr !== nothing
            state.trace[callstack_to_check] = bit_val
        end
        bits[i] = bit_val
    end

    return IntDist(bits)
end

function compile_inner(expr::PExpr{IntDistEqOp}, env::Env, null::Nothing, state::SampleValueState)
    first_int_dist = traced_compile_inner(expr.args[1], env, null, state, 0)
    second_int_dist = traced_compile_inner(expr.args[2], env, null, state, 1)
    @assert length(first_int_dist.bits) == length(second_int_dist.bits)
    are_equal = all(first_int_dist.bits[i] == second_int_dist.bits[i] for i in eachindex(first_int_dist.bits))
    return are_equal ? Pluck.TRUE_VALUE : Pluck.FALSE_VALUE
end

function compile_inner(expr::PExpr{UniformIntRangeOp}, env::Env, null::Nothing, state::SampleValueState)
    bitwidth = traced_compile_inner(expr.args[1], env, null, state, 0)
    lo = traced_compile_inner(expr.args[2], env, null, state, 1)
    hi = traced_compile_inner(expr.args[3], env, null, state, 2)
    width = bitwidth.value
    start = lo.value
    stop = hi.value
    @assert start isa Int && stop isa Int "uniform_int_range expects native Int bounds"
    @assert width isa Int "uniform_int_range expects native Int bitwidth"
    @assert stop >= start "uniform_int_range upper bound must be >= lower bound"

    function sample_range(lo_val::Int, hi_val::Int, depth::Int)
        if lo_val == hi_val
            return lo_val
        end
        mid = lo_val + (hi_val - lo_val) ÷ 2
        lower_size = mid - lo_val + 1
        upper_size = hi_val - mid
        p = lower_size / (lower_size + upper_size)
        callstack_to_check = ([state.callstack..., depth], p)

        result = if haskey(state.trace, callstack_to_check)
            state.trace[callstack_to_check]
        elseif state.constraint !== nothing && state.var_of_callstack !== nothing && haskey(state.var_of_callstack, callstack_to_check)
            var = state.var_of_callstack[callstack_to_check]
            if bdd_is_true(bdd_implies(state.constraint, var))
                true
            elseif bdd_is_true(bdd_implies(state.constraint, !var))
                false
            else
                rand() < p
            end
        else
            rand() < p
        end

        state.trace[callstack_to_check] = result
        return result ? sample_range(lo_val, mid, depth + 1) : sample_range(mid + 1, hi_val, depth + 1)
    end

    val = sample_range(start, stop, 0)
    bools = digits(Bool, val, base = 2, pad = width)
    return IntDist(bools)
end


function make_thunk(expr, env, strict_order_index, state::SampleValueState)
    # since posterior sampling just produces one result, we dont need to worry about binding in the strict case
    !state.lazy && return traced_compile_inner(expr, env, nothing, state, strict_order_index)
    thunk = LazyKCThunk(expr, env, strict_order_index, state)
    if thunk ∉ state.thunks
        push!(state.thunks, thunk)
    end
    print_make_thunk(thunk, state)
    return thunk
end

function traced_force_value(v, env, state)
    return force_value(v, env, state)
end

"""
thunks get evaluated, and their results are forced as well
"""
function force_value(v::Thunk, env, state::SampleValueState)
    return traced_force_value(evaluate(v, nothing, state), env, state)
end

"""
values get forced by forcing their args recursively
"""
function force_value(v::Value, env, state::SampleValueState)
    v.args = [traced_force_value(arg, env, state) for arg in v.args]
    return v
end

function force_value(v::PExpr, env, state::SampleValueState)
    v.args = [traced_force_value(arg, env, state) for arg in v.args]
    return v
end

function force_value(v::NativeValue{PExpr{T}}, env, state::SampleValueState) where T <: Head
    return traced_force_value(v.value, env, state)
end


"""
Force is a no-op for all other values
"""
force_value(v, env, state::SampleValueState) = v
