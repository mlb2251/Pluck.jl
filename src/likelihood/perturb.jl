using StringDistances

export PerturbConfig, PerturbEvalState


struct PerturbConfig
    inner_cfg::LazyEnumeratorConfig
    map_zero::Union{Nothing, Float64}
    map_nonzero::Union{Nothing, Float64}
    function PerturbConfig(inner_cfg::LazyEnumeratorConfig; map_zero = nothing, map_nonzero = nothing)
        return new(inner_cfg, map_zero, map_nonzero)
    end
end

get_time_limit(cfg::PerturbConfig) = cfg.inner_cfg.time_limit
set_time_limit!(cfg::PerturbConfig, time_limit::Float64) = (cfg.inner_cfg.time_limit = time_limit)

struct PerturbEvalState
    cfg::PerturbConfig
    inner_state::LazyEnumeratorEvalState
    stats::LazyEnumeratorEvalStats
    function PerturbEvalState(cfg::PerturbConfig)
        inner_cfg = cfg.inner_cfg
        @assert inner_cfg.strict && inner_cfg.disable_traces && inner_cfg.disable_cache
        # @assert isnothing(inner_cfg.max_depth)
        inner_state = LazyEnumeratorEvalState(inner_cfg)
        return new(cfg, inner_state, inner_state.stats)
    end
end

"""
Modified Levenshtein distance for vectors of natural numbers. Adapted from https://github.com/matthieugomez/StringDistances.jl/blob/main/src/distances/edit.jl

The distance is defined with the following costs:
- Inserting number n: +(n+1)  
- Deleting number n: -(n+1)
- Substituting n with m: |n-m|
"""
function levenshtein_natlist(s1::Vector{Int}, s2::Vector{Int}; max_dist::Union{Integer, Nothing} = nothing)
    (s1 === missing) | (s2 === missing) && return missing
    len1, len2 = length(s1), length(s2)
    if len1 > len2
        s1, s2 = s2, s1
        len1, len2 = len2, len1
    end
    if max_dist !== nothing
        len2 - len1 > max_dist && return Int(max_dist + 1)
    end
    # prefix common to both sequences can be ignored
    k = 0
    while k < len1 && k < len2 && s1[k+1] == s2[k+1]
        k += 1
    end
    k == len1 && return sum(s2[i]+1 for i in k+1:len2; init=0) # Cost of inserting remaining numbers
    
    # first row of matrix set to cost of inserting s2[1:i]
    v = [sum(s2[j]+1 for j in 1:i) for i in 1:len2-k]
    current = 0
    for (i1, n1) in enumerate(s1)
        i1 > k || continue
        left = current = sum(s1[j]+1 for j in 1:i1-k-1; init=0)
        if max_dist !== nothing
            value_lb = left - 1
        end
        for (i2, n2) in enumerate(s2)
            i2 > k || continue
            above = current
            # cost on diagonal (substitution)
            current = left
            @inbounds left = v[i2 - k]
            if n1 != n2
                # minimum between substitution (|n1-n2|), deletion (n1+1), insertion (n2+1)
                current = min(
                    current + abs(n1 - n2),  # substitution
                    above + (n2 + 1),        # insertion 
                    left + (n1 + 1)          # deletion
                )
            end
            if max_dist !== nothing
                value_lb = min(value_lb, left)
            end
            @inbounds v[i2 - k] = current
        end
        if max_dist !== nothing
            value_lb > max_dist && return Int(max_dist + 1)
        end
    end
    if max_dist !== nothing
        current > max_dist && return Int(max_dist + 1)
    end
    return current
end


function io_constrain(expr, io, cfg::PerturbConfig)
    state = PerturbEvalState(cfg)
    inputs = Vector{Any}(io.inputs)
    output = io.output

    state.inner_state.start_time = time()

    res = lazy_enumerate(string(expr); env=inputs, cfg=state.inner_state.cfg)

    state.stats.time = time() - state.inner_state.start_time
    state.stats.hit_limit = state.inner_state.hit_limit

    # happens if the program errors
    if length(res) == 0
        logp = isnothing(state.cfg.map_zero) ? -Inf : state.cfg.map_zero
        return IOConstrainResult(logp, state.stats)
    end

    @assert length(res) == 1 "Expected at most one result, got $(length(res)) for $expr with input $inputs"

    (val, trace) = res[1]

    # PARA does log2(levenshtein_natlist() + 1) then sums that over ios.
    # dist = Levenshtein()(from_value(val), from_value(output))
    dist = log(levenshtein_natlist(Vector{Int}(from_value(val)), Vector{Int}(from_value(output))) + 1)
    logp = -dist


    state.stats.time = time() - state.inner_state.start_time # do this again now, to include the lev distance

    if dist > 0 && !isnothing(state.cfg.map_nonzero)
        return IOConstrainResult(state.cfg.map_nonzero, state.stats)
    end

    return IOConstrainResult(logp, state.stats)
end





