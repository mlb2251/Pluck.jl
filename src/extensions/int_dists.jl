struct IntDist
    bits::Vector{Any} # BDDs in KC paths; booleans in non-KC interpreters
end
Base.show(io::IO, x::IntDist) = print(io, "IntDist{$(length(x.bits))}")

function combine_int_dists(int_dist_results::Vector{Tuple{IntDist, BDD}}, mgr::RSDD.Manager)
    width = length(int_dist_results[1][1].bits)
    result = IntDist(fill(mgr.BDD_FALSE, width))
    overall_guard = mgr.BDD_FALSE
    for (int_dist, guard) in int_dist_results
        # should we compute an overall guard?
        overall_guard = overall_guard | guard
        @assert width == length(int_dist.bits)
        # For each bit, AND it with the guard then OR it into the result.
        for i = 1:width
            @inbounds bit = int_dist.bits[i]::BDD
            @inbounds new_bit = bit & guard
            @inbounds result.bits[i] = result.bits[i] | new_bit
        end
    end
    return (result, overall_guard)
end

"""
Equality of two int distributions is an AND over the equality (bdd_iff) of each bit.
"""
function int_dist_eq(x::IntDist, y::IntDist, mgr::RSDD.Manager)::BDD
    width = length(x.bits)
    @assert width == length(y.bits)
    result = mgr.BDD_TRUE
    for i = 1:width
        @inbounds xb = x.bits[i]::BDD
        @inbounds yb = y.bits[i]::BDD
        @inbounds result = bdd_and(result, bdd_iff(xb, yb))
        if bdd_is_false(result)
            return mgr.BDD_FALSE
        end
    end
    return result
end

"""
Get the BDD for a given integer value of an IntDist.
"""
function int_dist_at_int(val::IntDist, i::Int, mgr::RSDD.Manager)
    bits = digits(Bool, i, base = 2, pad = length(val.bits))
    # Start with TRUE BDD and conjoin constraints for each bit.
    bdd = mgr.BDD_TRUE

    for (bit_idx, bit_val) in enumerate(bits)
        bit_formula = val.bits[bit_idx]::BDD
        if bit_val
            bdd &= bit_formula
        else
            bdd &= ~bit_formula
        end
    end
    return bdd
end

function enumerate_int_dist(val::IntDist, bdd::BDD, mgr::RSDD.Manager)
    worlds = Tuple{Int, BDD}[]
    # Enumerate all 2^n possibilities (all setting of n bits)
    for i = 0:(2^length(val.bits)-1)
        world_bdd = int_dist_at_int(val, i, mgr) & bdd
        push!(worlds, (i, world_bdd))
    end
    return worlds
end

struct MkIntOp <: Head end
define_parser!("mk_int", MkIntOp, 2)

struct UniformIntOp <: Head end
define_parser!("uniform_int", UniformIntOp, 1)

struct UniformIntRangeOp <: Head end
define_parser!("uniform_int_range", UniformIntRangeOp, 3)

struct IntDistEqOp <: Head end
define_parser!("int_dist_eq", IntDistEqOp, 2)

function compile_inner(expr::PExpr{MkIntOp}, env, path_condition, state)
    bind_compile(expr.args[1], env, path_condition, state, 0) do bitwidth, pc1
        bind_compile(expr.args[2], env, pc1, state, 1) do val, pc2
            bools = digits(Bool, val.value, base = 2, pad = bitwidth.value)
            bits = map(b -> b ? state.manager.BDD_TRUE : state.manager.BDD_FALSE, bools)
            return pure_monad(IntDist(bits), pc2, state)
        end
    end
end

function compile_inner(expr::PExpr{UniformIntOp}, env, path_condition, state)
    bind_compile(expr.args[1], env, path_condition, state, 0) do bitwidth, pc1
        width = bitwidth.value
        @assert width isa Int "uniform_int expects a native Int bitwidth, got $(typeof(width))"

        bits = Vector{BDD}(undef, width)
        for i = 1:width
            push!(state.callstack, i)
            if state.cfg.max_depth !== nothing &&
                state.depth > state.cfg.max_depth &&
                state.cfg.sample_after_max_depth &&
                !haskey(state.var_of_callstack, (state.callstack, 0.5))
                sampled_bit = rand(Bool)
                bits[i] = sampled_bit ? state.manager.BDD_TRUE : state.manager.BDD_FALSE
            else
                addr = current_address(state, 0.5)
                RSDD.set_weight(state.manager, bdd_topvar(addr), 0.5, 0.5)
                bits[i] = addr
            end
            pop!(state.callstack)
        end

        return pure_monad(IntDist(bits), pc1, state)
    end
end

function compile_inner(expr::PExpr{UniformIntRangeOp}, env, path_condition, state)
    bind_compile(expr.args[1], env, path_condition, state, 0) do bitwidth, pc1
        bind_compile(expr.args[2], env, pc1, state, 1) do lo, pc2
            bind_compile(expr.args[3], env, pc2, state, 2) do hi, pc3
                width = bitwidth.value
                start = lo.value
                stop = hi.value
                @assert start isa Int && stop isa Int "uniform_int_range expects native Int bounds"
                @assert width isa Int "uniform_int_range expects native Int bitwidth"
                @assert stop >= start "uniform_int_range upper bound must be >= lower bound"

                bits = fill(state.manager.BDD_FALSE, width)
                function encode_range(lo_val, hi_val, guard, depth_idx)
                    guard isa BDD && bdd_is_false(guard) && return
                    if lo_val == hi_val
                        bools = digits(Bool, lo_val, base = 2, pad = width)
                        for i = 1:width
                            @inbounds bits[i] |= (bools[i] ? state.manager.BDD_TRUE : state.manager.BDD_FALSE) & guard
                        end
                        return
                    end
                    mid = lo_val + (hi_val - lo_val) ÷ 2
                    lower_size = mid - lo_val + 1
                    upper_size = hi_val - mid
                    p = lower_size / (lower_size + upper_size)
                    push!(state.callstack, depth_idx)
                    addr = current_address(state, p)
                    RSDD.set_weight(state.manager, bdd_topvar(addr), 1.0 - p, p)
                    pop!(state.callstack)

                    encode_range(lo_val, mid, guard & addr, depth_idx + 1)
                    encode_range(mid + 1, hi_val, guard & !addr, depth_idx + 1)
                end

                encode_range(start, stop, state.manager.BDD_TRUE, 0)
                return pure_monad(IntDist(bits), pc3, state)
            end
        end
    end
end

function compile_inner(expr::PExpr{IntDistEqOp}, env, path_condition, state)
    bind_compile(expr.args[1], env, path_condition, state, 0) do first_int_dist, path_condition
        bind_compile(expr.args[2], env, path_condition, state, 1) do second_int_dist, path_condition
            bdd = int_dist_eq(first_int_dist, second_int_dist, state.manager)
            return if_then_else_monad(Pluck.TRUE_VALUE, Pluck.FALSE_VALUE, bdd, path_condition, state)
        end
    end
end

function is_all_intdist(x::Value)
    xs = x
    while xs isa Value && xs.constructor == :Cons
        head = xs.args[1]
        (head isa IntDist && length(head.bits) == 8 && all(b -> b === true || b === false, head.bits)) || return false
        xs = xs.args[2]
    end
    return xs isa Value && xs.constructor === :Nil
end

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

function replace_at_path(val::IntDist, path::Vector{Int}, new_val)
    @assert isempty(path)
    new_val
end