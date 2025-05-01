export compile_inner
import FunctionalCollections: PersistentHashMap, assoc



struct Choice
    addr::Int
    val::Bool
    weight::Float64
end

function Base.show(io::IO, choice::Choice)
    print(io, "(", choice.addr, " => ", choice.val, ")")
end

abstract type TraceImmut end
struct TraceImmutNil <: TraceImmut end
struct TraceImmutCons <: TraceImmut
    choice::Choice
    rest::TraceImmut
end

const ThunkCache = PersistentHashMap{Int, Any}

struct Trace
    trace::TraceImmut
    cache::ThunkCache
    weight::Float64
end
Trace() = Trace(TraceImmutNil(), ThunkCache(), 0.0)


function get_choice(trace::Trace, addr::Int, state)
    state.cfg.disable_traces && return nothing
    trace = trace.trace
    while trace isa TraceImmutCons
        if trace.choice.addr == addr
            return trace.choice
        end
        trace = trace.rest
    end
    return nothing
end

function get_cache(trace::Trace, id::Int, state)
    state.cfg.disable_cache && return nothing
    return get(trace.cache, id, nothing)
end

function set_cache(trace::Trace, id::Int, val::Any, state)
    state.cfg.disable_cache && return trace
    return Trace(trace.trace, assoc(trace.cache, id, val), trace.weight)
end

function Base.show(io::IO, trace::TraceImmutCons)
    print(io, "[")
    while trace isa TraceImmutCons
        print(io, trace.choice, ", ")
        trace = trace.rest
    end
    print(io, "]")
end

function Base.show(io::IO, trace::TraceImmutNil)
    print(io, "[]")
end

weight(trace::Trace) = trace.weight


function extend_trace(trace::Trace, choice::Choice, state)
    if state.cfg.disable_traces
        return Trace(trace.trace, trace.cache, trace.weight + choice.weight)
    end
    return Trace(TraceImmutCons(choice, trace.trace), trace.cache, trace.weight + choice.weight)
end

function cat_trace(trace::Trace, trace2::Trace)
    return Trace(cat_trace(trace.trace, trace2.trace), trace.cache, trace.weight + trace2.weight)
end

cat_trace(trace::TraceImmutNil, trace2::TraceImmutNil) = trace
cat_trace(trace::TraceImmutCons, trace2::TraceImmutNil) = trace
cat_trace(trace::TraceImmutNil, trace2::TraceImmutCons) = trace2
function cat_trace(trace::TraceImmutCons, trace2::TraceImmutCons)
    choices = []
    while trace2 isa TraceImmutCons
        push!(choices, trace2.choice)
        trace2 = trace2.rest
    end
    result = trace
    for choice in reverse(choices)
        result = extend_trace(result, choice, state)
    end
    return result
end

abstract type LazyEagerMode end
struct LazyMode <: LazyEagerMode end
struct EagerMode <: LazyEagerMode end


Base.@kwdef mutable struct LazyEnumeratorConfig
    max_depth::Union{Int, Nothing} = nothing
    time_limit::Union{Float64, Nothing} = nothing
    disable_traces::Bool = false
    disable_cache::Bool = true
    strict::Bool = false
end

mutable struct LazyEnumeratorEvalState{M <: LazyEagerMode}
    callstack::Vector{Int}
    id_of_callstack::Dict{Vector{Int}, Int}
    callstack_of_id::Vector{Vector{Int}}
    depth::Int
    start_time::Float64
    depth_reached::Int
    hit_limit::Bool
    next_thunk_id::Int
    cfg::LazyEnumeratorConfig

    function LazyEnumeratorEvalState(cfg::LazyEnumeratorConfig)
        args = (Int[], Dict(), Vector{Vector{Int}}(), 0, 0., 0, false, 1, cfg)
        if cfg.strict
            return new{EagerMode}(args...)
        else
            return new{LazyMode}(args...)
        end
    end

    function LazyEnumeratorEvalState(;kwargs...)
        cfg = LazyEnumeratorConfig(;kwargs...)
        LazyEnumeratorEvalState(cfg)
    end
end



function traced_compile_inner(expr::PExpr, env, trace, state::LazyEnumeratorEvalState, strict_order_index)
    # println(" " ^ state.depth * "traced_compile_inner($expr)")

    if state.hit_limit
        return []
    end

    if state.cfg.max_depth !== nothing && state.depth > state.cfg.max_depth
        state.hit_limit = true
        return []
    end

    if check_time_limit(state)
        state.hit_limit = true
        return []
    end

    state.depth += 1
    push!(state.callstack, strict_order_index)
    worlds = compile_inner(expr, env, trace, state)
    pop!(state.callstack)
    state.depth -= 1
    return worlds
end


function current_address(state::LazyEnumeratorEvalState, p::Float64)
    state.cfg.disable_traces && return 0
    if haskey(state.id_of_callstack, state.callstack)
        return state.id_of_callstack[state.callstack]
    else
        addr = length(state.id_of_callstack) + 1
        callstack = copy(state.callstack)
        state.id_of_callstack[callstack] = addr
        push!(state.callstack_of_id, callstack)
        return addr
    end
end


@inline function elapsed_time(state::LazyEnumeratorEvalState)
    return time() - state.start_time
end

@inline function check_time_limit(state::LazyEnumeratorEvalState)
    res = !isnothing(state.cfg.time_limit) && elapsed_time(state) > state.cfg.time_limit
    return res
end


function compile(expr; show_length = false, kwargs...)
    s = LazyEnumeratorEvalState(; kwargs...)
    if expr isa String
        expr = parse_expr(expr)
    end
    @assert !s.hit_limit
    s.start_time = time()
    
    ret = try
        compile_inner(expr, Pluck.EMPTY_ENV, Trace(), s)
    catch e
        if e isa StackOverflowError
            # printstyled("[compile_inner: stackoverflow]\n"; color=:yellow)
            s.hit_limit = true
            return []
        else
            rethrow(e)
        end
    end

    if s.hit_limit
        if !isempty(ret)
            @warn "enumeration hit time limit but had nonempty result"
        end
        ret = []
    end

    # Trying a model count of each possibility.
    results = [(ret, weight(trace)) for (ret, trace) in ret]
    if show_length
        @show length(results)
    end

    # @show results
    values = Dict{Any, Float64}()
    for (ret, weight) in results
        values[ret] = logaddexp(get(values, ret, -Inf), weight)
    end
    values = [(v, exp(weight)) for (v, weight) in values]
    return values
end
