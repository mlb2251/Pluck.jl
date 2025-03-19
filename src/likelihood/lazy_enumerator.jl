export lazy_enumerate, LazyEnumeratorEvalState, LazyEnumeratorConfig, sample_output, sample_output_lazy
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


# weight(trace::Trace) = weight(trace.trace)
# weight(trace::TraceImmutCons) = trace.choice.weight + weight(trace.rest)
# weight(trace::TraceImmutNil) = 0.0
weight(trace::Trace) = trace.weight


function extend_trace(trace::Trace, choice::Choice, state)
    if state.cfg.disable_traces
        return Trace(trace.trace, trace.cache, trace.weight + choice.weight)
    end
    return Trace(TraceImmutCons(choice, trace.trace), trace.cache, trace.weight + choice.weight)
end

function cat_trace(trace::Trace, trace2::Trace, state)
    return Trace(cat_trace(trace.trace, trace2.trace, state), trace.cache, trace.weight + trace2.weight)
end

cat_trace(trace::TraceImmutNil, trace2::TraceImmutNil, state) = trace
# cat_trace(trace::TraceImmutCons, trace2::TraceImmutNil, state) = trace
# cat_trace(trace::TraceImmutNil, trace2::TraceImmutCons, state) = trace2
# function cat_trace(trace::TraceImmutCons, trace2::TraceImmutCons, state)
#     choices = []
#     while trace2 isa TraceImmutCons
#         push!(choices, trace2.choice)
#         trace2 = trace2.rest
#     end
#     result = trace
#     for choice in reverse(choices)
#         result = extend_trace(result, choice, state)
#     end
#     return result
# end

mutable struct LazyEnumeratorEvalStats
    time::Float64
    hit_limit::Bool
end
LazyEnumeratorEvalStats() = LazyEnumeratorEvalStats(0.0, false)
function Base.:+(a::LazyEnumeratorEvalStats, b::LazyEnumeratorEvalStats)
    LazyEnumeratorEvalStats(a.time + b.time, a.hit_limit || b.hit_limit)
end


Base.@kwdef mutable struct LazyEnumeratorConfig
    disable_traces::Bool = false
    disable_cache::Bool = true
    strict::Bool = false
    time_limit::Float64 = 0.0
    max_depth::Union{Int, Nothing} = nothing
    sample::Bool = false
    state_vars::StateVars = StateVars()
end


mutable struct LazyEnumeratorEvalState
    callstack::Vector{Symbol}
    id_of_callstack::Dict{Vector{Symbol}, Int}
    callstack_of_id::Vector{Vector{Symbol}}
    depth::Int
    hit_limit::Bool
    next_thunk_id::Int
    start_time::Float64
    stats::LazyEnumeratorEvalStats
    cfg::LazyEnumeratorConfig

    function LazyEnumeratorEvalState(cfg::LazyEnumeratorConfig = LazyEnumeratorConfig())
        return new(Symbol[], Dict(), Vector{Vector{Symbol}}(), 0, false, 1, 0.0, LazyEnumeratorEvalStats(), cfg)
    end
end

mutable struct LazyEnumeratorThunk
    expr::PExpr
    env::Vector{Any}
    callstack::Vector{Symbol}
    name::Symbol
    id::Int

    function LazyEnumeratorThunk(expr::PExpr, env::Vector{Any}, state::LazyEnumeratorEvalState, name::Symbol)
        @assert !state.cfg.strict
        if expr isa Var && env[expr.idx] isa LazyEnumeratorThunk
            return env[expr.idx]
        end
        id = state.next_thunk_id
        state.next_thunk_id += 1
        new(expr, Pluck.mask_thunk_env(env, expr), copy(state.callstack), name, id)
    end
end

function traced_lazy_enumerate(expr::PExpr, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState, name::Symbol)
    if state.hit_limit
        # println("hit limit")
        return []
    end
    # println("  " ^ state.depth, expr)
    if state.cfg.max_depth !== nothing && state.depth > state.cfg.max_depth
        state.hit_limit = true
        # println("max depth reached")
        return []
    end

    if check_time_limit(state)
        state.hit_limit = true
        # println("time limit reached")
        return []
    end

    state.depth += 1
    push!(state.callstack, name)
    worlds = lazy_enumerate(expr, env, trace, state)
    pop!(state.callstack)
    state.depth -= 1
    return worlds
end

get_time_limit(cfg::LazyEnumeratorConfig) = cfg.time_limit
set_time_limit!(cfg::LazyEnumeratorConfig, time_limit::Float64) = (cfg.time_limit = time_limit)

@inline function elapsed_time(state::LazyEnumeratorEvalState)
    return time() - state.start_time
end
@inline function check_time_limit(state::LazyEnumeratorEvalState)
    return state.cfg.time_limit > 0. && elapsed_time(state) > state.cfg.time_limit
end

function evaluate(thunk::LazyEnumeratorThunk, trace::Trace, state::LazyEnumeratorEvalState)
    state.hit_limit && return []
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

function force(thunk::LazyEnumeratorThunk, trace::Trace, state::LazyEnumeratorEvalState)
    res = evaluate(thunk, trace, state)
    lazy_enumerator_bind(res, state) do val, trace
        force(val, trace, state)
    end
end

force(other::Any, trace::Trace, state::LazyEnumeratorEvalState) = [(other, trace)]

function force(value::Value, trace::Trace, state::LazyEnumeratorEvalState)
    # force all the args
    length(value.args) == 0 && return [(value, trace)]
    first_arg_results = force(value.args[1], trace, state)
    lazy_enumerator_bind(first_arg_results, state) do first_arg, trace
        length(value.args) == 1 && return [(Value(value.spt, value.constructor, [first_arg]), trace)]
        second_arg_results = force(value.args[2], trace, state)
        lazy_enumerator_bind(second_arg_results, state) do second_arg, trace
            length(value.args) == 2 && return [(Value(value.spt, value.constructor, [first_arg, second_arg]), trace)]
            third_arg_results = force(value.args[3], trace, state)
            lazy_enumerator_bind(third_arg_results, state) do third_arg, trace
                length(value.args) == 3 && return [(Value(value.spt, value.constructor, [first_arg, second_arg, third_arg]), trace)]
                fourth_arg_results = force(value.args[4], trace, state)
                lazy_enumerator_bind(fourth_arg_results, state) do fourth_arg, trace
                    length(value.args) == 4 && return [(Value(value.spt, value.constructor, [first_arg, second_arg, third_arg, fourth_arg]), trace)]
                    fifth_arg_results = force(value.args[5], trace, state)
                    lazy_enumerator_bind(fifth_arg_results, state) do fifth_arg, trace
                        length(value.args) == 5 && return [(Value(value.spt, value.constructor, [first_arg, second_arg, third_arg, fourth_arg, fifth_arg]), trace)]
                        @assert length(value.args) == 6 "too many args"
                    end
                end
            end
        end
    end
end

function lazy_prim_enumerate(::ForceOp, args, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    val_results = traced_lazy_enumerate(args[1], env, trace, state, :force_arg)
    lazy_enumerator_bind(val_results, state) do val, trace
        return force(val, trace, state)
    end
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


function lazy_enumerate(expr::App, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    fs = traced_lazy_enumerate(expr.f, env, trace, state, :app_f)

    if state.cfg.strict
        # in strict semantics its safe to evaluate xs independently of f instead of nesting
        # it within the bind call.
        xs = traced_lazy_enumerate(expr.x, env, Trace(), state, :app_x)
        results = []
        for (f, ftrace) in fs
            @assert f isa Closure "expected a closure got: $(typeof(f)): $f"
            for (x, xtrace) in xs
                state.hit_limit && return []
                new_env = copy(f.env)   
                pushfirst!(new_env, x)
                new_trace = cat_trace(ftrace, xtrace, state)
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

    thunked_argument = LazyEnumeratorThunk(expr.x, env, state, :app_x)
    return lazy_enumerator_bind(fs, state) do f, trace
        new_env = copy(f.env)
        x = Pluck.var_is_free(f.expr, 1) ? thunked_argument : nothing
        pushfirst!(new_env, x)
        return traced_lazy_enumerate(f.expr, new_env, trace, state, :app_closure)
    end
end

function lazy_enumerate(expr::Abs, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    # A lambda term deterministically evaluates to a closure.
    return [(Closure(expr.body, env), trace)]
end

# function bind_recursive(args, state)
#     length(args) == 1 && return args[1]
#     lazy_enumerator_bind(args[1], state) do arg1, trace
#         bind_recursive(args[2:end], state)
#     end
# end
function lazy_enumerate(expr::Construct, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    # Constructors deterministically evaluate to a WHNF value, with their arguments thunked.
    # Look up type of this constructor.
    spt = Pluck.spt_of_constructor[expr.constructor]

    if state.cfg.strict
        options_of_arg = []
        for (i, arg) in enumerate(expr.args)
            push!(options_of_arg, traced_lazy_enumerate(arg, env, Trace(), state, Symbol("$(expr.constructor).arg$i")))
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
                new_trace = cat_trace(new_trace, arg_trace, state)
                push!(new_args, arg)
            end
            push!(results, (Value(spt, expr.constructor, new_args), new_trace))
        end
        return results
    end

    # Create a thunk for each argument.
    thunked_arguments = [LazyEnumeratorThunk(arg, env, state, Symbol("$(expr.constructor).arg$i")) for (i, arg) in enumerate(expr.args)] # TODO: use global args_syms to avoid runtime cost of Symbol?
    # Return the constructor and its arguments.
    return [(Value(spt, expr.constructor, thunked_arguments), trace)]
end

function lazy_enumerate(expr::CaseOf, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    scrutinee_values = traced_lazy_enumerate(expr.scrutinee, env, trace, state, :case_scrutinee)
    # @show expr
    # @show expr.scrutinee
    lazy_enumerator_bind(scrutinee_values, state) do scrutinee, trace
        if scrutinee.constructor in expr.constructors
            case_expr = expr.cases[scrutinee.constructor]
            num_args = length(args_of_constructor(scrutinee.constructor))
            if num_args == 0
                return traced_lazy_enumerate(case_expr, env, trace, state, scrutinee.constructor)
            else
                for _ = 1:num_args
                    @assert case_expr isa Abs "case expression branch for constructor $(scrutinee.constructor) must have as many lambdas as the constructor has arguments ($(num_args) arguments)"
                    case_expr = case_expr.body
                end
                new_env = vcat(reverse(scrutinee.args), env)
                return traced_lazy_enumerate(case_expr, new_env, trace, state, scrutinee.constructor)
            end
        else
            # could also error out here
            # @warn "constructor $(scrutinee.constructor) not found in case of $(expr)"
            return []
        end
    end
end

function lazy_enumerate(expr::Y, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    @assert expr.f isa Abs && expr.f.body isa Abs "y-combinator must be applied to a double-lambda"

    closure = Pluck.make_self_loop(expr.f.body.body, env)

    # set up a closure with a circular reference
    return [(closure, trace)]
end

function lazy_enumerate(expr::PrimOp, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    lazy_prim_enumerate(expr.op, expr.args, env, trace, state)
end

function lazy_enumerator_make_address(state::LazyEnumeratorEvalState)
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

function lazy_prim_enumerate(op::FlipOp, args, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    ps = traced_lazy_enumerate(args[1], env, trace, state, :flip_arg)
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

            state.cfg.sample && return [rand() < p ? (Pluck.TRUE_VALUE, trace_true) : (Pluck.FALSE_VALUE, trace_false)]

            return [(Pluck.TRUE_VALUE, trace_true), (Pluck.FALSE_VALUE, trace_false)]
        end
    end
end

function lazy_prim_enumerate(op::ConstructorEqOp, args, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    
    # Evaluate both arguments.  
    first_arg_results = traced_lazy_enumerate(args[1], env, trace, state, :constructor_eq_arg1)

    if state.cfg.strict
        # in strict semantics its safe to evaluate second argument independently of first
        # instead of nesting it within the bind call.   
        second_arg_results = traced_lazy_enumerate(args[2], env, trace, state, :constructor_eq_arg2)
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
        second_arg_results = traced_lazy_enumerate(args[2], env, trace, state, :constructor_eq_arg2)
        lazy_enumerator_bind(second_arg_results, state) do arg2, trace
            if arg1.constructor == arg2.constructor
                return [(Pluck.TRUE_VALUE, trace)]
            else
                return [(Pluck.FALSE_VALUE, trace)]
            end
        end
    end
end

function lazy_prim_enumerate(op::GetConfig, args, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    sym = traced_lazy_enumerate(args[1], env, trace, state, :get_config_sym)
    lazy_enumerator_bind(sym, state) do sym, trace
        return [(to_value(getfield(state.cfg.state_vars, sym)), trace)]
    end
end

function lazy_prim_enumerate(op::FloatDivOp, args, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    lazy_prim_enumerate_simple((x, y) -> x / y, op, args, env, trace, state)
end

function lazy_prim_enumerate(op::FloatMulOp, args, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    lazy_prim_enumerate_simple((x, y) -> x * y, op, args, env, trace, state)
end

function lazy_prim_enumerate(op::FloatAddOp, args, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    lazy_prim_enumerate_simple((x, y) -> x + y, op, args, env, trace, state)
end

function lazy_prim_enumerate(op::FloatSubOp, args, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    lazy_prim_enumerate_simple((x, y) -> x - y, op, args, env, trace, state)
end

function lazy_prim_enumerate(op::FloatPowOp, args, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    lazy_prim_enumerate_simple((x, y) -> x^y, op, args, env, trace, state)
end

function lazy_prim_enumerate(op::FloatLessOp, args, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    lazy_prim_enumerate_simple((x, y) -> x < y ? Pluck.TRUE_VALUE : Pluck.FALSE_VALUE, op, args, env, trace, state)
end

# fcos/fsin

function lazy_prim_enumerate(op::FloatCosOp, args, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    lazy_prim_enumerate_simple(cos, op, args, env, trace, state)
end
function lazy_prim_enumerate(op::FloatSinOp, args, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    lazy_prim_enumerate_simple(sin, op, args, env, trace, state)
end

function lazy_prim_enumerate_simple(f, op, args, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    first_arg_results = traced_lazy_enumerate(args[1], env, trace, state, :first_arg)
    lazy_enumerator_bind(first_arg_results, state) do arg1, trace
        length(args) == 1 && return [(f(arg1), trace)]
        second_arg_results = traced_lazy_enumerate(args[2], env, trace, state, :second_arg)
        lazy_enumerator_bind(second_arg_results, state) do arg2, trace
            @assert length(args) == 2 "too many args"
            return [(f(arg1, arg2), trace)]
        end
    end
end

# function lazy_prim_enumerate(::ForceOp, args, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
#     val_results = traced_lazy_enumerate(args[1], env, trace, state, :force_arg)
#     lazy_enumerator_bind(val_results, state) do val, trace
#         if val isa Value
#             # force all the args
#             args = [traced_lazy_enumerate(PrimOp(ForceOp(), PExpr[arg]), env, trace, state, Symbol("$(val.constructor).arg$i")) for (i, arg) in enumerate(val.args)]
#         else
#             # just return it
#             return [(arg, trace)]
#         end
#     end
# end










function lazy_enumerate(expr::Var, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    # Look up the variable in the environment.
    if expr.idx > length(env)
        @warn "Variable $expr not found in environment; shaving off probability."
        return []
    end

    v = env[expr.idx]
    if v isa LazyEnumeratorThunk
        return evaluate(v, trace, state)
    else
        return [(v, trace)]
    end
end

function lazy_enumerate(expr::Defined, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    # Execute Defined with a blanked out environment.
    return traced_lazy_enumerate(Pluck.get_def(expr.name).expr, Pluck.EMPTY_ENV, trace, state, expr.name)
end

function lazy_enumerate(expr::Root, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    return lazy_enumerate(expr.body, env, trace, state)
end

function lazy_enumerate(expr::ConstReal, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    return [(expr.val, trace)]
end
function lazy_enumerate(expr::ConstSymbol, env::Vector{Any}, trace::Trace, state::LazyEnumeratorEvalState)
    return [(expr.name, trace)]
end

function lazy_enumerate(expr; env = Pluck.EMPTY_ENV, show_length = false, return_state=false, cfg=nothing, kwargs...)
    !isnothing(cfg) && @assert isempty(kwargs)
    cfg = isnothing(cfg) ? LazyEnumeratorConfig(;kwargs...) : cfg
    state = LazyEnumeratorEvalState(cfg)
    parsed = parse_expr(expr)
    # @assert isempty(state.id_of_callstack)

    state.start_time = time()

    ret = try
        lazy_enumerate(parsed, env, Trace(), state)
    catch e
        if e isa StackOverflowError
            state.hit_limit = true
            # println("stack overflow")
            []
        else
            rethrow(e)
        end
    end
    
    state.stats.time = time() - state.start_time
    state.stats.hit_limit = state.hit_limit

    if state.hit_limit
        if !isempty(ret)
            @warn "lazy enum hit time limit but had nonempty result"
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
        # @show ret
        values[ret] = logaddexp(get(values, ret, -Inf), weight)
    end
    values = [(v, exp(weight)) for (v, weight) in values]
    # sort!(values)
    return_state && return values, state
    return values
end

function io_constrain(expr, io, cfg::LazyEnumeratorConfig)
    expr = io_equality_expr(expr, io.inputs, io.output)
    res, state = lazy_enumerate(expr; cfg=cfg, return_state=true)
    # @show res
    p = get_true_result(res) # could alternatively bdd_normalize this btw
    # @show state.stats
    # return log(p), state
    return IOConstrainResult(log(p), state.stats)
end

function sample_output(expr; env = Pluck.EMPTY_ENV)
    res = lazy_enumerate(expr; env=env, strict=true, sample=true, disable_traces=true, max_depth=100000)
    return isempty(res) ? nothing : first(res)[1]
end


function sample_output_lazy(expr; env = Pluck.EMPTY_ENV)
    res = lazy_enumerate("(force $expr)"; env=env, sample=true, max_depth=1000, disable_cache=false)
    @assert length(res) < 2
    return isempty(res) ? nothing : first(res)[1]
end
