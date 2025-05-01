export lazy_enumerate
import FunctionalCollections: PersistentHashMap, assoc


const ThunkCache = PersistentHashMap{Int, Any}

struct Choice
    addr::Int
    val::Any
    weight::Float64
end

function Base.show(io::IO, choice::Choice)
    print(io, "(", choice.addr, " => ", choice.val, ")")
    #  ", w = ", round(exp(choice.weight), sigdigits=2), ")")
end

abstract type TraceImmut end
struct TraceImmutNil <: TraceImmut end
struct TraceImmutCons <: TraceImmut
    choice::Choice
    rest::TraceImmut
end

struct Trace
    trace::TraceImmut
    cache::ThunkCache
    weight::Float64
end
Trace() = Trace(TraceImmutNil(), ThunkCache(), 0.0)


function get_choice(trace::Trace, addr::Int, state)
    state.disable_traces && return nothing
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
    state.disable_cache && return nothing
    return get(trace.cache, id, nothing)
end

function set_cache(trace::Trace, id::Int, val::Any, state)
    state.disable_cache && return trace
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


# weight(trace::Trace) = weight(trace.trace)
# weight(trace::TraceImmutCons) = trace.choice.weight + weight(trace.rest)
# weight(trace::TraceImmutNil) = 0.0
weight(trace::Trace) = trace.weight


function extend_trace(trace::Trace, choice::Choice, state)
    if state.disable_traces
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



mutable struct LazyEnumeratorEvalState
    callstack::Vector{Symbol}
    id_of_callstack::Dict{Vector{Symbol}, Int}
    callstack_of_id::Vector{Vector{Symbol}}
    depth::Int
    max_depth::Union{Int, Nothing}
    time_limit::Union{Float64, Nothing}
    start_time::Float64
    depth_reached::Int
    hit_limit::Bool
    next_thunk_id::Int
    disable_traces::Bool
    disable_cache::Bool # we actually find cache slows things down
    strict::Bool

    function LazyEnumeratorEvalState(; max_depth = nothing, time_limit = nothing, disable_traces = false, disable_cache = true, strict = false)
        return new(Symbol[], Dict(), Vector{Vector{Symbol}}(), 0, max_depth, time_limit, 0., 0., false, 1, disable_traces, disable_cache, strict)
    end
end

mutable struct LazyEnumeratorThunk
    expr::PExpr
    env::Vector{Any}
    callstack::Vector{Symbol}
    name::Symbol
    id::Int

    function LazyEnumeratorThunk(expr::PExpr, env::Vector{Any}, state::LazyEnumeratorEvalState, name::Symbol)
        @assert !state.strict
        if expr isa Var && env[expr.idx] isa LazyEnumeratorThunk
            return env[expr.idx]
        end
        id = state.next_thunk_id
        state.next_thunk_id += 1
        new(expr, env, copy(state.callstack), name, id)
    end
end

function traced_lazy_enumerate(expr::PExpr, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState, name::Symbol)
    # println(" " ^ state.depth * "traced_lazy_enumerate($expr)")

    if state.hit_limit
        return []
    end

    if state.max_depth !== nothing && state.depth > state.max_depth
        state.hit_limit = true
        return []
    end

    if check_time_limit(state)
        state.hit_limit = true
        return []
    end

    state.depth += 1
    push!(state.callstack, name)
    worlds = lazy_enumerate(expr, env, trace, state)
    pop!(state.callstack)
    state.depth -= 1
    return worlds
end

@inline function elapsed_time(state::LazyEnumeratorEvalState)
    return time() - state.start_time
end

@inline function check_time_limit(state::LazyEnumeratorEvalState)
    res = !isnothing(state.time_limit) && elapsed_time(state) > state.time_limit
    return res
end

function evaluate(thunk::LazyEnumeratorThunk, trace::Trace, state::LazyEnumeratorEvalState)
    if state.hit_limit
        return []
    end

    # Check the cache
    cached = get_cache(trace, thunk.id, state)
    if cached !== nothing
        # println("hitting cache containing:", cached)
        return [(cached, trace)]
    end

    # Otherwise we have to evaluate the thunk. Set the callstack to the thunk's callstack.
    old_callstack = state.callstack
    state.callstack = thunk.callstack
    result = traced_lazy_enumerate(thunk.expr, thunk.env, trace, state, thunk.name)
    state.callstack = old_callstack
    # Cache the result
    result = map(result) do (val, trace)
        (val, set_cache(trace, thunk.id, val, state))
    end
    return result
end

function lazy_enumerate(expr::PExpr, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    error("lazy_enumerate not implemented for $(typeof(expr))")
end

function lazy_enumerator_bind(cont, first_stage_results, state)
    if check_time_limit(state)
        state.hit_limit = true
        return []
    end
    results = []
    for (result, trace) in first_stage_results
        state.hit_limit && return []
        second_stage_worlds = cont(result, trace)
        state.hit_limit && return []
        for (final_result, final_trace) in second_stage_worlds
            push!(results, (final_result, final_trace))
        end
    end
    return results
end


function lazy_enumerate(expr::PExpr{App}, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    fs = traced_lazy_enumerate(expr.args[1], env, trace, state, :app_f)

    if state.strict
        # in strict semantics its safe to evaluate xs independently of f instead of nesting
        # it within the bind call.
        xs = traced_lazy_enumerate(expr.args[2], env, Trace(), state, :app_x)
        results = []
        for (f, ftrace) in fs
            for (x, xtrace) in xs
                state.hit_limit && return []
                new_env = copy(f.env)
                pushfirst!(new_env, x)
                new_trace = cat_trace(ftrace, xtrace)
                for result in traced_lazy_enumerate(f.expr, new_env, new_trace, state, :app_closure)
                    push!(results, result)
                end
            end
        end
        return results
        # same thing but with bind:
        # return lazy_enumerator_bind(fs, state) do f, trace
        #     lazy_enumerator_bind(xs, state) do x, trace
        #         new_env = copy(f.env)
        #         pushfirst!(new_env, x)
        #         return traced_lazy_enumerate(f.expr, new_env, trace, state, :app_closure)
        #     end
        # end
    end

    thunked_argument = LazyEnumeratorThunk(expr.args[2], env, state, :app_x)
    return lazy_enumerator_bind(fs, state) do f, trace
        new_env = copy(f.env)
        x = Pluck.var_is_free(f.expr, 1) ? thunked_argument : nothing
        pushfirst!(new_env, x)
        return traced_lazy_enumerate(f.expr, new_env, trace, state, :app_closure)
    end
end

function lazy_enumerate(expr::PExpr{Abs}, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    # A lambda term deterministically evaluates to a closure.
    return [(Closure(expr.args[1], env), trace)]
end

# function bind_recursive(args, state)
#     length(args) == 1 && return args[1]
#     lazy_enumerator_bind(args[1], state) do arg1, trace
#         bind_recursive(args[2:end], state)
#     end
# end
function lazy_enumerate(expr::PExpr{Construct}, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    # Constructors deterministically evaluate to a WHNF value, with their arguments thunked.
    # Look up type of this constructor.
    # spt = Pluck.spt_of_constructor[expr.constructor]

    if state.strict
        options_of_arg = []
        for (i, arg) in enumerate(expr.args[2])
            push!(options_of_arg, traced_lazy_enumerate(arg, env, Trace(), state, Symbol("$(expr.args[1]).arg$i")))
        end
        results = []
        for args in Iterators.product(options_of_arg...)
            if check_time_limit(state)
                state.hit_limit = true
                return []
            end
            new_trace = trace
            new_args = []
            for (arg, arg_trace) in args
                new_trace = cat_trace(new_trace, arg_trace)
                push!(new_args, arg)
            end
            push!(results, (Value(expr.args[1], new_args), new_trace))
        end
        return results
    end

    # Create a thunk for each argument.
    thunked_arguments = [LazyEnumeratorThunk(arg, env, state, Symbol("$(expr.args[1]).arg$i")) for (i, arg) in enumerate(expr.args[2])] # TODO: use global args_syms to avoid runtime cost of Symbol?
    # Return the constructor and its arguments.
    return [(Value(expr.args[1], thunked_arguments), trace)]
end

function lazy_enumerate(expr::PExpr{CaseOf}, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    scrutinee_values = traced_lazy_enumerate(expr.args[1], env, trace, state, :case_scrutinee)
    lazy_enumerator_bind(scrutinee_values, state) do scrutinee, trace
        if scrutinee.constructor in keys(expr.args[2])
            case_expr = expr.args[2][scrutinee.constructor]
            num_args = length(args_of_constructor[scrutinee.constructor])
            if num_args == 0
                return traced_lazy_enumerate(case_expr, env, trace, state, scrutinee.constructor)
            else
                for _ = 1:num_args
                    @assert case_expr isa PExpr{Abs} "case expression branch for constructor $(scrutinee.constructor) must have as many lambdas as the constructor has arguments ($(num_args) arguments)"
                    case_expr = case_expr.args[1]
                end
                new_env = vcat(reverse(scrutinee.args), env)
                return traced_lazy_enumerate(case_expr, new_env, trace, state, scrutinee.constructor)
            end
        else
            return []
        end
    end
end

function lazy_enumerate(expr::PExpr{Y}, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    @assert expr.args[1] isa PExpr{Abs} && expr.args[1].args[1] isa PExpr{Abs} "y-combinator must be applied to a double-lambda"
 
    closure = Pluck.make_self_loop(expr.args[1].args[1].args[1], env)

    # set up a closure with a circular reference
    return [(closure, trace)]
end


function lazy_enumerator_make_address(state::LazyEnumeratorEvalState)
    state.disable_traces && return 0
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

function lazy_enumerate(expr::PExpr{FlipOp}, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    ps = traced_lazy_enumerate(expr.args[1], env, trace, state, :flip_arg)
    lazy_enumerator_bind(ps, state) do p, trace
        if isapprox(p, 0.0)
            return [(Pluck.FALSE_VALUE, trace)]
        elseif isapprox(p, 1.0)
            return [(Pluck.TRUE_VALUE, trace)]
        else
            addr = lazy_enumerator_make_address(state)

            # check if we already have this choice in the trace
            choice = get_choice(trace, addr, state)
            if choice !== nothing
                return [(choice.val, trace)]
            end


            trace_true = extend_trace(trace, Choice(addr, Pluck.TRUE_VALUE, log(p)), state)
            trace_false = extend_trace(trace, Choice(addr, Pluck.FALSE_VALUE, log1p(-p)), state)
            return [(Pluck.TRUE_VALUE, trace_true), (Pluck.FALSE_VALUE, trace_false)]
        end
    end
end

function lazy_enumerate(expr::PExpr{ConstructorEqOp}, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)

    # Evaluate both arguments.  
    first_arg_results = traced_lazy_enumerate(expr.args[1], env, trace, state, :constructor_eq_arg1)

    if state.strict
        # in strict semantics its safe to evaluate second argument independently of first
        # instead of nesting it within the bind call.   
        second_arg_results = traced_lazy_enumerate(expr.args[2], env, trace, state, :constructor_eq_arg2)
        return lazy_enumerator_bind(first_arg_results, state) do arg1, trace
            return lazy_enumerator_bind(second_arg_results, state) do arg2, trace
                if arg1.constructor == arg2.constructor
                    return [(Pluck.TRUE_VALUE, trace)]
                else
                    return [(Pluck.FALSE_VALUE, trace)]
                end
            end
        end
    end

    lazy_enumerator_bind(first_arg_results, state) do arg1, trace
        second_arg_results = traced_lazy_enumerate(expr.args[2], env, trace, state, :constructor_eq_arg2)
        lazy_enumerator_bind(second_arg_results, state) do arg2, trace
            if arg1.constructor == arg2.constructor
                return [(Pluck.TRUE_VALUE, trace)]
            else
                return [(Pluck.FALSE_VALUE, trace)]
            end
        end
    end
end

function lazy_enumerate(expr::PExpr{Var}, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    # Look up the variable in the environment.
    if expr.args[1] > length(env)
        @warn "Variable $expr not found in environment; shaving off probability."
        return []
    end

    v = env[expr.args[1]]
    if v isa LazyEnumeratorThunk
        return evaluate(v, trace, state)
    else
        return [(v, trace)]
    end
end

function lazy_enumerate(expr::PExpr{Defined}, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    # Execute Defined with a blanked out environment.
    return traced_lazy_enumerate(lookup(expr.args[1]).expr, Pluck.EMPTY_ENV, trace, state, expr.args[1])
end

function lazy_enumerate(expr::PExpr{ConstReal}, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    return [(expr.args[1], trace)]
end

function lazy_enumerate(expr; show_length = false, kwargs...)
    s = LazyEnumeratorEvalState(; kwargs...)
    if expr isa String
        expr = parse_expr(expr)
    end
    @assert !s.hit_limit
    s.start_time = time()
    
    ret = try
        lazy_enumerate(expr, Pluck.EMPTY_ENV, Trace(), s)
    catch e
        if e isa StackOverflowError
            # printstyled("[lazy_enumerate: stackoverflow]\n"; color=:yellow)
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
