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