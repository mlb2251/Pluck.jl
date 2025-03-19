export traced_constrain, TaskConstrain, make_state,
    constrain, traced_forward, forward, weight, EvalState, StatsEval, merge_stats
export timed_constrain, timed_forward, summarize, exhaustive_forward, SPN_TRUE, SPN_FALSE
export record_constrain, record_forward, hit_limit, EvalConfig

mutable struct StatsEval
    forward::Int
    constrain::Int
    condition_spn::Int
    max_depth_hit::Int
    depth_limit_hit::Int
    eval_limit_hit::Int
    time_limit_hit::Int
    max_worlds::Int
    total_worlds::Int
    time::Float64
    constrain_cache::CacheStats
    constrain_cache1::CacheStats
    constrain_cache2::CacheStats
    constrain_cache3::CacheStats
    forward_cache::CacheStats
    forward_cache1::CacheStats
    forward_cache2::CacheStats
    forward_cache3::CacheStats
end
StatsEval() = StatsEval(
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0.0,
    CacheStats("c"),
    CacheStats("c1"),
    CacheStats("c2"),
    CacheStats("c3"),
    CacheStats("f"),
    CacheStats("f1"),
    CacheStats("f2"),
    CacheStats("f3"),
)


Base.show(io::IO, stats::StatsEval) = print(
    io,
    "StatsEval(forward: ",
    stats.forward,
    ", constrain: ",
    stats.constrain,
    ", condition_spn: ",
    stats.condition_spn,
    ", depth: ",
    stats.max_depth_hit,
    ", depth_limit_hit: ",
    stats.depth_limit_hit,
    ", eval_limit_hit: ",
    stats.eval_limit_hit,
    ", time_limit_hit: ",
    stats.time_limit_hit,
    ", max_worlds: ",
    stats.max_worlds,
    ", total_worlds: ",
    stats.total_worlds,
    ", time: ",
    round(stats.time, sigdigits = 3),
    ", ",
    stats.constrain_cache,
    ", ",
    stats.forward_cache,
    ", ",
    stats.constrain_cache1,
    ", ",
    stats.forward_cache1,
    ", ",
    stats.constrain_cache2,
    ", ",
    stats.forward_cache2,
    ", ",
    stats.constrain_cache3,
    ", ",
    stats.forward_cache3,
    ")",
)

hit_limit(stats::StatsEval) =
    stats.depth_limit_hit > 0 || stats.eval_limit_hit > 0 || stats.time_limit_hit > 0

function Base.:+(a::StatsEval, b::StatsEval)
    StatsEval(
        a.forward + b.forward,
        a.constrain + b.constrain,
        a.condition_spn + b.condition_spn,
        max(a.max_depth_hit, b.max_depth_hit),
        a.depth_limit_hit + b.depth_limit_hit,
        a.eval_limit_hit + b.eval_limit_hit,
        a.time_limit_hit + b.time_limit_hit,
        max(a.max_worlds, b.max_worlds),
        a.total_worlds + b.total_worlds,
        a.time + b.time,
        a.constrain_cache + b.constrain_cache,
        a.constrain_cache1 + b.constrain_cache1,
        a.constrain_cache2 + b.constrain_cache2,
        a.constrain_cache3 + b.constrain_cache3,
        a.forward_cache + b.forward_cache,
        a.forward_cache1 + b.forward_cache1,
        a.forward_cache2 + b.forward_cache2,
        a.forward_cache3 + b.forward_cache3,
    )
end

function merge_stats(v::Vector{StatsEval})
    reduce(+, v; init = StatsEval())
end

# c1: (expr, env, output)
const ConstrainKey1 = Tuple{PExpr, Vector{Any}, Any, Bool}
# f1: (expr, env)
const ForwardKey1 = Tuple{PExpr, Vector{Any}, Bool}

# c2: (expr, env, output, spn)
const ConstrainKey2 = Tuple{PExpr, Vector{Any}, Any, Bool, SPN}
# f2: (expr, env, spn)
const ForwardKey2 = Tuple{PExpr, Vector{Any}, Bool, SPN}

# c3: (expr, env, output, spn, callstack)
const ConstrainKey3 = Tuple{PExpr, Vector{Any}, Any, Bool, SPN, Vector{Symbol}}
# f3: (expr, env, spn, callstack)
const ForwardKey3 = Tuple{PExpr, Vector{Any}, Bool, SPN, Vector{Symbol}}

const ConstrainRet = SPN
const ForwardRet = Vector{Tuple{Any, SPN}}


# An `EvalState` captures state that is threaded through both the
# `constrain` and `forward` methods.
# It tracks:
#   * memoizing: whether the primitive random choices that occur within 
#                the currently evaluated expression should be memoized.
#   * current:   the current call stack, which is a list of symbols.
#                each application and primop invocation is annotated with 
#                a statically known gensym. thunks that represent lazy 
#                computations remember their stack trace, and we reload it 
#                when evaluating expressions in those thunks.
#   * names:     the SPN data structure contains symbol names, so we need to 
#                remember which names correspond to which stack traces. this 
#                dictionary maps stack traces to SPN variable names.

Base.@kwdef struct EvalConfig
    reachability::Bool = false
    cache_stats::Bool = false
    use_cache::Bool = false
    check_cache::Bool = false
    cache_per::Symbol = :all # :expr, :task, :all
    dedup_and_factor::Bool = false # TODO turn back on
    disable_memoize::Bool = false
    spn_intersection::Bool = false
    record_json::Bool = false
    verbose::Bool = false
    memoizing_default = false
    depth_limit::Int = 1000
    eval_limit::Int = 10000 #40000
    time_limit::Float64 = 10.0
    timeout_factor = 1.0
end
function Base.show(io::IO, config::EvalConfig)
    print(io, "EvalConfig(")
    for k in fieldnames(typeof(config))
        print(io, k, "=", getfield(config, k), ", ")
    end
    print(io, ")")
end

# allocation re-use (1.1x speedup in benchmark)
struct ReusedAllocations
    product_weights::IdDict{Vector{SPN}, Float64}
    leaf_weights::IdDict{Tuple{Scope, Any}, Float64}
    children_as_products::Vector{Tuple{Vector{SPN}, Float64}}
    children_processed::Vector{SPN}
end
ReusedAllocations() = ReusedAllocations(
    IdDict{Vector{SPN}, Float64}(),
    IdDict{Tuple{Scope, Any}, Float64}(),
    Vector{Tuple{Vector{SPN}, Float64}}(),
    Vector{SPN}(),
)

mutable struct EvalState
    config::EvalConfig
    id_of_callstack::Dict{Vector{Symbol}, Address}
    callstack_of_id::Vector{Vector{Symbol}}
    callstack::Vector{Symbol}
    memoizing::Bool
    depth::Int
    start_time::Float64
    stats::StatsEval
    json_children::Vector
    unreachable_addrs::Vector{Vector{Address}}
    expr_stack::Vector{PExpr}
    timeout_stack::Vector{Float64}
    constrain_cache_check::Dict{ConstrainKey1, Dict{SPN, Set{Vector{Symbol}}}}
    forward_cache_check::Dict{ForwardKey1, Dict{SPN, Set{Vector{Symbol}}}}
    constrain_cache::Dict{ConstrainKey3, ConstrainRet}
    forward_cache::Dict{ForwardKey3, ForwardRet}
    spn_hash::SPNHash
    reused::ReusedAllocations

    EvalState(config::EvalConfig) = new(
        config,
        Dict{Vector{Symbol}, Address}(),
        Vector{Vector{Symbol}}(),
        Vector{Symbol}(),
        config.memoizing_default,
        0,
        0.0,
        StatsEval(),
        Vector(),
        Vector{Vector{Address}}(),
        Vector{PExpr}(),
        Vector{Float64}(),
        Dict{ConstrainKey1, Dict{SPN, Set{Vector{Symbol}}}}(),
        Dict{ForwardKey1, Dict{SPN, Set{Vector{Symbol}}}}(),
        Dict{ConstrainKey3, ConstrainRet}(),
        Dict{ForwardKey3, ForwardRet}(),
        SPNHash(),
        ReusedAllocations(),
    )
    EvalState(; kwargs...) = EvalState(EvalConfig(; kwargs...))
end

function clear_cache!(eval_state::EvalState)
    empty!(eval_state.constrain_cache)
    empty!(eval_state.forward_cache)
    empty!(eval_state.constrain_cache_check)
    empty!(eval_state.forward_cache_check)
    empty!(eval_state.id_of_callstack)
    empty!(eval_state.callstack_of_id)
    empty!(eval_state.spn_hash)
end

function assert_ready(eval_state::EvalState)
    @assert eval_state.depth == 0
    @assert eval_state.memoizing == eval_state.config.memoizing_default
    @assert isempty(eval_state.callstack)
    @assert isempty(eval_state.expr_stack)
    @assert isempty(eval_state.unreachable_addrs)
    @assert isempty(eval_state.json_children)
    @assert isempty(eval_state.timeout_stack)
end

Base.show(io::IO, eval_state::EvalState) =
    print(io, "EvalState(", eval_state.stats, ", ", eval_state.config, ")")

function weight(res::Tuple{SPN, EvalState})
    weight(res[2].spn_hash, res[1])
end

make_state(config::EvalConfig) = EvalState[EvalState(config) for _ = 1:Threads.threadpoolsize()]


function JSON.lower(eval_state::EvalState)
    Dict(
        k => getfield(eval_state, k) for k in fieldnames(EvalState) if
        !(k in (:json_children, :constrain_cache, :forward_cache))
    )
end

struct TaskConstrain{E}
    task::PTask
    eval_states::Vector{E}
    cache::Dict{PExpr, Tuple{Float64, Any}}
    use_cache::Bool
    temperature::Float64
end
TaskConstrain(task, eval_state; use_cache = true, temperature = 1.0) = TaskConstrain(task, [eval_state], Dict{PExpr, Tuple{Float64, Any}}(), use_cache, temperature)
TaskConstrain(task, eval_states::Vector{E}; use_cache = true, temperature = 1.0) where {E} = TaskConstrain(task, eval_states, Dict{PExpr, Tuple{Float64, Any}}(), use_cache, temperature)
JSON.lower(tc::TaskConstrain) = Dict(:task => tc.task, :temperature => tc.temperature, :cache => map(kv -> (kv[1], exp(kv[2][1]), kv[2][2]), collect(tc.cache)))
total_time(tc::TaskConstrain) = sum(kv -> kv[2][2].time, tc.cache)

(tc::TaskConstrain)(expr::String) = tc(parse_expr(expr))

function (tc::TaskConstrain)(exprs::Vector{PExpr})
    # single thread: filter to the unique exprs that are not in the cache
    worklist = unique(exprs)
    filter!(expr -> !haskey(tc.cache, expr), worklist)

    # parallel: run eval
    results = Vector{Any}(undef, length(worklist))
    launch_workers(worklist, worker_id -> tc.eval_states[worker_id]) do i_expr, worker_id, eval_state
        # for (i,expr) in enumerate(worklist)
        i = i_expr[1]::Int
        results[i] = eval_task(i_expr[2], tc, eval_state)
    end
    # end

    # single thread: add to cache
    for (expr, res) in zip(worklist, results)
        tc.cache[expr] = res
    end

    # single thread: construct output (undoing the unique!())
    res = [tc.cache[expr] for expr in exprs]
    return res
end

function (tc::TaskConstrain)(expr::PExpr)
    eval_state = tc.eval_states[1]
    res = cached_eval_task(expr, tc, eval_state)
    return res
end

function cached_eval_task(expr::PExpr, tc, eval_state)
    tc.use_cache && haskey(tc.cache, expr) && return tc.cache[expr]
    res = eval_task(expr, tc, eval_state)
    tc.use_cache && (tc.cache[expr] = res)
    return res
end

function eval_task(expr::PExpr, tc::TaskConstrain, eval_state)
    total = 0.0
    all_stats = []
    for io in tc.task.ios
        (weight, eval_state) = io_constrain(expr, io, eval_state)
        total += weight
        push!(all_stats, eval_state.stats)
        total == -Inf && break
    end
    total /= tc.temperature
    return total, merge_stats(all_stats)
end

# Evaluator for PExprs that represents the posterior using an SPN.

constrain_value(val, output, spn::SPN, eval_state::EvalState) =
    val == output ? spn : SPN_FALSE
# float -> value conversion
constrain_value(val::Value, output::Float64, spn::SPN, eval_state::EvalState) =
    constrain_value(from_value(val), output, spn, eval_state)

# floats use isapprox
constrain_value(val, output::Float64, spn::SPN, eval_state::EvalState) =
    val ≈ output ? spn : SPN_FALSE

# use the stack and env of the thunk
function constrain_value(thunk::Thunk, output, spn::SPN, eval_state::EvalState)
    old_stack = eval_state.callstack
    old_memoizing = eval_state.memoizing
    eval_state.callstack = copy(thunk.callstack)
    eval_state.memoizing = thunk.memoizing
    result = traced_constrain(thunk.expr, thunk.env, output, spn, eval_state, thunk.name)
    eval_state.memoizing = old_memoizing
    eval_state.callstack = old_stack
    return result
end

function forward_value(thunk::Thunk, spn::SPN, eval_state::EvalState)
    old_stack = eval_state.callstack
    old_memoizing = eval_state.memoizing
    eval_state.callstack = copy(thunk.callstack)
    eval_state.memoizing = thunk.memoizing
    result = traced_forward(thunk.expr, thunk.env, spn, eval_state, thunk.name)
    eval_state.memoizing = old_memoizing
    eval_state.callstack = old_stack
    return result
end

@inline forward_value(val, spn::SPN, ::EvalState) = [(val, spn)]


function constrain_value(partial_value::Succ, output::Succ, spn::SPN, eval_state::EvalState)
    return constrain_value(partial_value.pred, output.pred, spn, eval_state)
end
function constrain_value(partial_value::Cons, output::Cons, spn::SPN, eval_state::EvalState)
    head_spn = constrain_value(partial_value.head, output.head, spn, eval_state)
    impossible(head_spn) && return head_spn
    tail_spn = constrain_value(partial_value.tail, output.tail, head_spn, eval_state)
    return tail_spn
end

# Two mutually recursive methods:
# - constrain(e, env, out, spn, eval_state): Construct an SPN representing the subspace of the original SPN where [[e]](env) = out.
# - forward(e, env, spn, eval_state): For each possible value of [[e]](env), construct the SPN representing the subspace of the original SPN where [[e]](env) is equal to that value.

constrain(expr::String, env::Vector{Value}, output::Value, eval_state = nothing) =
    constrain(parse_expr(expr), env, output, eval_state)
constrain(expr::String, env::Any, output::Any, eval_state = nothing) =
    constrain(parse_expr(expr), to_value.(env), to_value(output), eval_state)
function constrain(expr::PExpr, env, output, eval_state = nothing)
    eval_state = isnothing(eval_state) ? EvalState() : eval_state
    timed_constrain(expr, env, output, eval_state)
end

forward(expr::String, env::Vector{Any}, eval_state = EvalState()) =
    forward(parse_expr(expr), to_value.(env), eval_state)

forward(expr::String, env::Vector{Value}, eval_state = EvalState()) =
    forward(parse_expr(expr), env, eval_state)

forward(expr::PExpr, env, eval_state = EvalState()) =
    timed_forward(expr, env, eval_state)

function constrain_stats(expr::PExpr, env, output, eval_state = EvalState())
    result = constrain(expr, env, output, eval_state)
    return result, eval_state.stats
end
function forward_stats(expr::PExpr, env, eval_state = EvalState())
    result = forward(expr, env, eval_state)
    return result, eval_state.stats
end

# TODO: Consider whether the old methods of logprob and enumerate are still worth having
# too. If a sub-expression uses no free variables that are thunks, then even if some 
# sharing happens *within* the expression, *outer* code can depend only on the logprob /
# values of the expression. (Assuming the values do not themselves have thunks...)
# These methods can then only be called when the caller is sure that memoized randomness
# cannot 'escape.' (Possibly only logprob is needed? And logprob of an app calls constrain.
# This does seem like a better way to do it, which also may avoid the need to do linearity 
# analysis.)

function timed_constrain(expr::PExpr, env, output, eval_state::EvalState)
    # clear_cache!(eval_state)
    env = mask_thunk_env(env, expr)
    eval_state.config.cache_per === :expr && clear_cache!(eval_state)
    assert_ready(eval_state)
    eval_state.start_time = time()
    eval_state.stats = StatsEval()
    result = traced_constrain(expr, env, output, SPN_TRUE, eval_state, :timed)
    eval_state.stats.time = round(time() - eval_state.start_time, sigdigits = 3)
    if eval_state.config.record_json
        @assert length(eval_state.json_children) == 1
        write_spe(eval_state.json_children[1])
        eval_state.json_children = []
    end
    return (result, eval_state)
end
function timed_forward(expr::PExpr, env, eval_state::EvalState)
    assert_ready(eval_state)
    eval_state.start_time = time()
    eval_state.stats = StatsEval()
    result = traced_forward(expr, env, SPN_TRUE, eval_state, :timed)
    eval_state.stats.time = round(time() - eval_state.start_time, sigdigits = 3)
    if eval_state.config.record_json
        @assert length(eval_state.json_children) == 1
        write_spe(eval_state.json_children[1])
        eval_state.json_children = []
    end
    return result
end

@inline function get_timeout(eval_state::EvalState)::Float64
    # update timeout
    if isempty(eval_state.timeout_stack)
        # push overall deadline on
        return eval_state.start_time + eval_state.config.time_limit
    else
        # make a new deadline: how long is remaining in our parents deadline? take a fraction of that
        timelimit = (eval_state.timeout_stack[end] - time()) * (1 - eval_state.config.timeout_factor)
        deadline = eval_state.timeout_stack[end] - max(timelimit, 0.0)
        # deadline = eval_state.timeout_stack[end]
        return deadline
    end
end

function traced_constrain(
    expr::PExpr,
    env,
    output::Value,
    spn::SPN,
    eval_state::EvalState,
    name::Symbol,
)#::SPN
    push!(eval_state.callstack, name)
    push!(eval_state.expr_stack, expr)
    push!(eval_state.timeout_stack, get_timeout(eval_state))

    # reachability
    if eval_state.config.reachability
        s = collect(scope(spn))
        scope_mask = reachable_scope(expr, env, s, eval_state)
        unreachable_addrs = s[.!scope_mask]
        push!(eval_state.unreachable_addrs, unreachable_addrs)
    end

    # analyze cache hits under different caching policies
    if eval_state.config.cache_stats
        constrain_cache_key =
            (expr, mask_thunk_env(env, expr), output, eval_state.memoizing)
        spns = get!(
            Dict{SPN, Set{Vector{Symbol}}},
            eval_state.constrain_cache_check,
            constrain_cache_key,
        )
        hit!(eval_state.stats.constrain_cache1, !isempty(spns))
        hit!(eval_state.stats.constrain_cache2, !isempty(spns) && haskey(spns, spn))
        hit!(
            eval_state.stats.constrain_cache3,
            !isempty(spns) && haskey(spns, spn) && eval_state.callstack in spns[spn],
        )
        callstacks = get!(Set{Vector{Symbol}}, spns, spn)
        push!(callstacks, copy(eval_state.callstack))
    end

    eval_state.config.verbose && println(
        "  "^eval_state.depth,
        "<constrain::",
        typeof(expr),
        " @ ",
        eval_state.depth,
        " (",
        eval_state.stats.constrain,
        "|",
        eval_state.stats.forward,
        ")",
        "> ",
        string(expr),
        " TO ",
        string(output),
    )
    (eval_state.config.verbose || eval_state.config.record_json) && (tstart = time())
    eval_state.stats.max_depth_hit = max(eval_state.stats.max_depth_hit, eval_state.depth)

    # set up json record
    if eval_state.config.record_json
        new_record, old_children = new_json_record(
            :constrain,
            Dict(
                :expr => expr,
                :env =>
                    [var_is_free(expr, i) ? v : "unused" for (i, v) in enumerate(env)],
                :output => output,
                :spn => json_spn(spn, eval_state.spn_hash),
                :name => name,
                :expr_type => typeof(expr),
                :shortname => shortname(expr),
            ),
            eval_state,
        )
    end

    # check for cache hit
    if eval_state.config.use_cache
        cache_key = (
            expr,
            mask_thunk_env(env, expr),
            output,
            eval_state.memoizing,
            spn,
            copy(eval_state.callstack),
        )
        cache_res = get(eval_state.constrain_cache, cache_key, nothing)
        hit!(eval_state.stats.constrain_cache, !isnothing(cache_res))
        if !eval_state.config.check_cache && !isnothing(cache_res)
            res = cache_res
            eval_state.config.record_json && json_record_result(
                new_record,
                res,
                limit_hit,
                true,
                eval_state,
                old_children,
            )
            @assert pop!(eval_state.callstack) === name
            @assert pop!(eval_state.expr_stack) === expr
            pop!(eval_state.timeout_stack)
            eval_state.config.reachability &&
                @assert pop!(eval_state.unreachable_addrs) === unreachable_addrs
            return res
        end
    end

    # check for hitting limits
    limit_hit = check_limits(eval_state)

    # handle limit hits
    if limit_hit !== :none
        eval_state.config.verbose &&
            printstyled("  "^eval_state.depth, "hit ", limit_hit, " limit", color = :yellow)
        res = SPN_FALSE
        eval_state.config.record_json &&
            json_record_result(new_record, res, limit_hit, false, eval_state, old_children)
        @assert pop!(eval_state.callstack) === name
        @assert pop!(eval_state.expr_stack) === expr
        pop!(eval_state.timeout_stack)
        eval_state.config.reachability &&
            @assert pop!(eval_state.unreachable_addrs) === unreachable_addrs
        return res
    end

    eval_state.stats.constrain += 1
    incoming_spn = eval_state.config.spn_intersection ? SPN_TRUE : spn
    eval_state.depth += 1
    result = constrain(expr, env, output, incoming_spn, eval_state)
    # for now spn_intersection is a weird thing that doesnt preserve choices, much like disable_memoize
    result =
        eval_state.config.spn_intersection ?
        mul_weight(eval_state.spn_hash, result, weight(spn)) : result
    eval_state.depth -= 1

    # @assert result == result
    eval_state.config.check_cache && @assert !eval_state.config.use_cache ||
                                             isnothing(cache_res) ||
                                             hit_limit(eval_state.stats) ||
                                             result == cache_res "$expr $output \n$(typeof(result)) != \n$(typeof(cache_res)) \n$(result) != \n$(cache_res)"

    eval_state.config.use_cache &&
        !hit_limit(eval_state.stats) &&
        (eval_state.constrain_cache[cache_key] = result)

    if eval_state.config.record_json
        json_record_result(new_record, result, limit_hit, false, eval_state, old_children)
        eval_state.json_children = old_children
    end

    eval_state.config.verbose && println(
        "  "^eval_state.depth,
        "</constrain @ ",
        eval_state.depth,
        " (",
        eval_state.stats.constrain,
        "|",
        eval_state.stats.forward,
        ")",
        "> ",
        string(expr),
        " in ",
        round(time() - tstart, sigdigits = 3),
        "s",
        " -> ",
        exp(weight(result)),
    )
    @assert pop!(eval_state.callstack) === name
    @assert pop!(eval_state.expr_stack) === expr
    pop!(eval_state.timeout_stack)
    eval_state.config.reachability &&
        @assert pop!(eval_state.unreachable_addrs) === unreachable_addrs
    return result
end

function traced_forward(expr::PExpr, env, spn::SPN, eval_state::EvalState, name::Symbol)#::Vector{Tuple{Any, SPN}}
    push!(eval_state.callstack, name)
    push!(eval_state.expr_stack, expr)
    push!(eval_state.timeout_stack, get_timeout(eval_state))

    # reachability
    if eval_state.config.reachability
        s = collect(scope(spn))
        scope_mask = reachable_scope(expr, env, s, eval_state)
        unreachable_addrs = s[.!scope_mask]
        push!(eval_state.unreachable_addrs, unreachable_addrs)
    end

    # analyze cache hits under different caching policies
    if eval_state.config.cache_stats
        forward_cache_key = (expr, mask_thunk_env(env, expr), eval_state.memoizing)
        spns = get!(
            Dict{SPN, Set{Vector{Symbol}}},
            eval_state.forward_cache_check,
            forward_cache_key,
        )
        hit!(eval_state.stats.forward_cache1, !isempty(spns))
        hit!(eval_state.stats.forward_cache2, !isempty(spns) && haskey(spns, spn))
        hit!(
            eval_state.stats.forward_cache3,
            !isempty(spns) && haskey(spns, spn) && eval_state.callstack in spns[spn],
        )
        callstacks = get!(Set{Vector{Symbol}}, spns, spn)
        push!(callstacks, copy(eval_state.callstack))
    end

    eval_state.config.verbose && println(
        "  "^eval_state.depth,
        "<forward::",
        typeof(expr),
        " @ ",
        eval_state.depth,
        " (",
        eval_state.stats.forward,
        "|",
        eval_state.stats.forward,
        ")",
        "> ",
        string(expr),
    )
    (eval_state.config.verbose || eval_state.config.record_json) && (tstart = time())
    eval_state.stats.max_depth_hit = max(eval_state.stats.max_depth_hit, eval_state.depth)

    # set up json record
    if eval_state.config.record_json
        new_record, old_children = new_json_record(
            :forward,
            Dict(
                :expr => expr,
                :env =>
                    [var_is_free(expr, i) ? v : "unused" for (i, v) in enumerate(env)],
                :spn => json_spn(spn, eval_state.spn_hash),
                :name => name,
                :expr_type => typeof(expr),
                :shortname => shortname(expr),
            ),
            eval_state,
        )
    end

    # check for cache hit
    if eval_state.config.use_cache
        cache_key = (
            expr,
            mask_thunk_env(env, expr),
            eval_state.memoizing,
            spn,
            copy(eval_state.callstack),
        )
        cache_res = get(eval_state.forward_cache, cache_key, nothing)
        hit!(eval_state.stats.forward_cache, !isnothing(cache_res))
        if !eval_state.config.check_cache && !isnothing(cache_res)
            res = cache_res
            eval_state.config.record_json && json_record_result(
                new_record,
                res,
                limit_hit,
                true,
                eval_state,
                old_children,
            )
            @assert pop!(eval_state.callstack) === name
            @assert pop!(eval_state.expr_stack) === expr
            pop!(eval_state.timeout_stack)
            eval_state.config.reachability &&
                @assert pop!(eval_state.unreachable_addrs) === unreachable_addrs
            return res
        end
    end

    # check for hitting limits
    limit_hit = check_limits(eval_state)

    # handle limit hits
    if limit_hit !== :none
        eval_state.config.verbose &&
            printstyled("  "^eval_state.depth, "hit ", limit_hit, " limit", color = :yellow)
        res = []
        if eval_state.config.record_json
            json_record_result(new_record, res, limit_hit, false, eval_state, old_children)
        end
        @assert pop!(eval_state.callstack) === name
        @assert pop!(eval_state.expr_stack) === expr
        pop!(eval_state.timeout_stack)
        eval_state.config.reachability &&
            @assert pop!(eval_state.unreachable_addrs) === unreachable_addrs
        return res
    end

    cache_hit = false
    eval_state.stats.forward += 1
    eval_state.depth += 1
    result = forward(expr, env, spn, eval_state)
    eval_state.depth -= 1

    # @assert result == result
    if eval_state.config.check_cache
        @assert !eval_state.config.use_cache ||
                isnothing(cache_res) ||
                hit_limit(eval_state.stats) ||
                result == cache_res "$expr \n$(typeof(result)) != \n$(typeof(cache_res)) \n$(result) != \n$(cache_res)"
    end

    eval_state.config.use_cache &&
        !hit_limit(eval_state.stats) &&
        (eval_state.forward_cache[cache_key] = result)

    if eval_state.config.record_json
        json_record_result(
            new_record,
            result,
            limit_hit,
            cache_hit,
            eval_state,
            old_children,
        )
    end

    eval_state.config.verbose && println(
        "  "^eval_state.depth,
        "</forward @ ",
        eval_state.depth,
        " (",
        eval_state.stats.forward,
        "|",
        eval_state.stats.forward,
        ")",
        "> ",
        string(expr),
        " in ",
        round(time() - tstart, sigdigits = 3),
        "s",
        " -> ",
        length(result),
    )
    @assert pop!(eval_state.callstack) === name
    @assert pop!(eval_state.expr_stack) === expr
    pop!(eval_state.timeout_stack)
    eval_state.config.reachability &&
        @assert pop!(eval_state.unreachable_addrs) === unreachable_addrs
    return result
end

function json_worlds(worlds)
    [
        Dict(:val => string(val), :spn => json_spn(spn, eval_state.spn_hash)) for
        (val, spn) in worlds
    ]
end

function new_json_record(mode::Symbol, info::Dict{Symbol, Any}, eval_state)
    tstart = time()
    old_children = eval_state.json_children
    new_children = []
    new_record = Dict(
        info...,
        :type => mode,
        :eval_state_before => deepcopy(JSON.lower(eval_state)), # do this now before it gets mutated
        :res => nothing,
        :children => new_children,
        :tstart => tstart,
    )
    push!(old_children, new_record)
    eval_state.json_children = new_children

    new_record[:time_overhead] = time() - tstart
    (new_record, old_children)
end

function json_record_result(
    new_record,
    result::Any,
    limit_hit,
    cache_hit,
    eval_state,
    old_children,
)
    elapsed = time() - new_record[:tstart]
    json_res = Dict(
        :time_total => elapsed,
        :result => json_result(new_record[:type], result, eval_state.spn_hash),
        :limit_hit => limit_hit,
        :cache_hit => cache_hit,
        :eval_state_after => deepcopy(JSON.lower(eval_state)),
    )
    new_record[:res] = json_res
    eval_state.json_children = old_children
    nothing
end

function json_result(mode, result, spn_hash)
    if mode == :forward
        map(result) do world
            Dict(:val => world[1], :spn => json_spn(world[2], spn_hash))
        end
    else
        json_spn(result, spn_hash)
    end
end


@inline function check_limits(eval_state)::Symbol
    # if time() - eval_state.start_time > eval_state.config.time_limit
    if time() > eval_state.timeout_stack[end]
        eval_state.stats.time_limit_hit = 1
        :time
    elseif eval_state.depth >= eval_state.config.depth_limit
        eval_state.stats.depth_limit_hit = 1
        :depth
    elseif eval_state.stats.constrain + eval_state.stats.forward >=
           eval_state.config.eval_limit
        eval_state.stats.eval_limit_hit = 1
        :eval
    else
        :none
    end
end

function summarize(worlds; limit = 2)
    res = "["

    for (val, spn) in worlds[1:min(limit, end)]
        res *=
            "(" *
            string(val)[1:min(end, 100)] *
            ",p=" *
            string(round(exp(weight(spn)), sigdigits = 2)) *
            "),"
    end

    if length(worlds) > limit
        res *= "... and " * string(length(worlds) - limit) * " more"
    else
        res = res[1:end-1]
    end

    return res * "]"
end

# CONSTANTS
function constrain(expr::Const, env, output, spn::SPN, eval_state::EvalState)
    return constrain_value(expr.val, output, spn, eval_state)
end

# Enumerate [(val, spn)] pairs.
function forward(expr::Const, env, spn::SPN, eval_state::EvalState)
    # The value of the constant does not depend on or update the SPN.
    return [(expr.val, spn)]
end

function constrain(expr::ConstReal, env, output, spn::SPN, eval_state::EvalState)
    return constrain_value(expr.val, output, spn, eval_state)
end

function forward(expr::ConstReal, env, spn::SPN, eval_state::EvalState)
    return [(expr.val, spn)]
end

function constrain(expr::ConstBool, env, output, spn::SPN, eval_state::EvalState)
    return constrain_value(expr.val, output, spn, eval_state)
end

function forward(expr::ConstBool, env, spn::SPN, eval_state::EvalState)
    return [(expr.val, spn)]
end

# VARIABLES
function constrain(expr::Var, env, output, spn::SPN, eval_state::EvalState)
    if expr.idx > length(env)
        return SPN_FALSE
    end

    # The env might be storing a thunk, so we need to check for that.
    val = env[expr.idx]

    # Otherwise, we already have a value.
    return constrain_value(val, output, spn, eval_state)
end

function forward(expr::Var, env, spn::SPN, eval_state::EvalState)
    if expr.idx > length(env)
        return []
    end

    # The env might be storing a thunk, so we need to check for that.
    val = env[expr.idx]

    forward_value(val, spn, eval_state)
end

# ABS / YLAMLAM
function constrain(expr::Abs, env, output, spn::SPN, eval_state::EvalState)
    # This should never happen
    error("cannot constrain lambda")
end

function forward(expr::Abs, env, spn::SPN, eval_state::EvalState)
    # A lambda is already a value
    return [(Closure(expr.body, env), spn)]
end

function constrain(expr::Ylamlam, env, output, spn::SPN, eval_state::EvalState)
    # This should never happen
    error("cannot constrain y combinator")
end

function constrain(expr::Y, env, output, spn::SPN, eval_state::EvalState)
    # This should never happen
    error("cannot constrain (Y f) since it's a function type")
end

function forward(expr::Y, env, spn::SPN, eval_state::EvalState)
    @assert expr.f isa Abs && expr.f.body isa Abs "y-combinator must be applied to a double-lambda"

    # Could broaden implementation to allow for non-lambda functions, but that seems somewhat unnecessary
    # since its not a big hassle to write the two lambdas. Also I tried it a bit and it's hard to get right
    # when you are trying to set up the self-referential closure for a two-argument lambda through evaluating
    # each in turn. At least if you want to get the exact semantics of possible references to the outer closure
    # when constructing the inner one it gets a bit weird. All in all pretty unnecessary too since you can just
    # eta expand things to put them in this form.

    closure = make_self_loop(expr.f.body.body, env)

    # set up a closure with a circular reference
    # @show length(closure.env)
    return [(closure, spn)]
end

# (Y f) = (f (Y f))
# (Y (λrec 0)) = ((λrec 0) (Y (λrec 0)))

function constrain(expr::If, env, output, spn::SPN, eval_state::EvalState)
    # Create a conditional SPN for each condition, true and false
    # TODO: is this better than 'forward' on the Boolean expression?
    # TODO: this is somewhere that (assuming no free variables corresponding to thunks) 
    #       we could just call logprob(true).

    # todo note that if expressions are allowed to error and error results in -inf instead
    # of some sort of "error" value, then you cant do Pfalse = 1-Ptrue
    cond_true_spn = traced_constrain(expr.cond, env, TRUE_VALUE, spn, eval_state, :cond)
    cond_false_spn = traced_constrain(expr.cond, env, FALSE_VALUE, spn, eval_state, :cond)

    # Extend each one with the then and else branches
    nodes = SPN[]
    if !impossible(cond_true_spn)
        push!(
            nodes,
            traced_constrain(
                expr.then_expr,
                env,
                output,
                cond_true_spn,
                eval_state,
                :then_expr,
            ),
        )
    end
    if !impossible(cond_false_spn)
        push!(
            nodes,
            traced_constrain(
                expr.else_expr,
                env,
                output,
                cond_false_spn,
                eval_state,
                :else_expr,
            ),
        )
    end

    # Combine the two SPNs
    new_sum_node = new_sum(nodes, eval_state)
    return new_sum_node
end

function forward(expr::If, env, spn::SPN, eval_state::EvalState)
    # Create a conditional SPN for each condition, true and false
    cond_true_spn = traced_constrain(expr.cond, env, TRUE_VALUE, spn, eval_state, :cond)
    cond_false_spn = traced_constrain(expr.cond, env, FALSE_VALUE, spn, eval_state, :cond)
    worlds = []
    # Extend each one with the then and else branches
    if !impossible(cond_true_spn)
        append!(
            worlds,
            traced_forward(expr.then_expr, env, cond_true_spn, eval_state, :then_expr),
        )
    end
    if !impossible(cond_false_spn)
        append!(
            worlds,
            traced_forward(expr.else_expr, env, cond_false_spn, eval_state, :else_expr),
        )
    end
    return merge_worlds(worlds, eval_state)
end

function constrain(expr::App, env, output, spn::SPN, eval_state::EvalState)
    lams = traced_forward(expr.f, env, spn, eval_state, :f)
    # For each lambda, extend the environment with the argument and constrain
    # the body to the output.
    spns = SPN[]
    thunk = Thunk(expr.x, env, eval_state.callstack, :x, true)
    for (lam, spn) in lams
        @assert lam isa Closure
        # extend environment
        new_env = copy(lam.env)
        x = var_is_free(lam.expr, 1) ? thunk : nothing
        pushfirst!(new_env, x)
        # @show length(new_env)
        push!(spns, traced_constrain(lam.expr, new_env, output, spn, eval_state, :closure))
    end

    return new_sum(spns, eval_state)
end

function forward(expr::App, env, spn::SPN, eval_state::EvalState)
    lams = traced_forward(expr.f, env, spn, eval_state, :f)
    # For each lambda, extend the environment with the argument.
    worlds = []
    thunk = Thunk(expr.x, env, eval_state.callstack, :x, true)
    for (lam, spn) in lams
        @assert lam isa Closure "expected closure, got $lam for lhs of $expr"
        # extend environment
        new_env = copy(lam.env)
        x = var_is_free(lam.expr, 1) ? thunk : nothing
        pushfirst!(new_env, x)
        append!(worlds, traced_forward(lam.expr, new_env, spn, eval_state, :closure))
    end
    return merge_worlds(worlds, eval_state)
end

function constrain(expr::PrimOp, env, output, spn::SPN, eval_state::EvalState)
    prim_constrain(expr.op, expr.args, env, output, spn, eval_state)
end

function forward(expr::PrimOp, env, spn::SPN, eval_state::EvalState)
    # Call prim_forward
    prim_forward(expr.op, expr.args, env, spn, eval_state)
end


function constrain(expr::Defined, env, output, spn::SPN, eval_state::EvalState)
    # TODO: using stale symbols?
    # always execute Defined with a blanked out environment
    return traced_constrain(
        get_def(expr.name).expr,
        EMPTY_ENV,
        output,
        spn,
        eval_state,
        expr.name,
    )
end

function forward(expr::Defined, env, spn::SPN, eval_state::EvalState)
    # TODO: using stale symbols?
    # always execute Defined with a blanked out environment
    return traced_forward(get_def(expr.name).expr, EMPTY_ENV, spn, eval_state, expr.name)
end

function constrain(expr::Root, env, output, spn::SPN, eval_state::EvalState)
    return constrain(expr.body, env, output, spn, eval_state)
end

function forward(expr::Root, env, spn::SPN, eval_state::EvalState)
    return forward(expr.body, env, spn, eval_state)
end

# primitives

function constrain(expr::Construct, env, output, spn::SPN, eval_state::EvalState)
    @assert length(expr.args) == length(args_of_constructor(expr.constructor))
    !isa(output, Value) && return SPN_FALSE
    output.spt != expr.spt && return SPN_FALSE
    output.constructor != expr.constructor && return SPN_FALSE
    @assert length(output.args) == length(expr.args)
    for i = 1:length(expr.args)
        spn = traced_constrain(
            expr.args[i],
            env,
            output.args[i],
            spn,
            eval_state,
            args_syms[i],
        )
        impossible(spn) && return SPN_FALSE
    end
    return spn
end

function forward(expr::Construct, env, spn::SPN, eval_state::EvalState)
    @assert length(expr.args) == length(args_of_constructor(expr.constructor))
    # if !eval_state.exhaustive_forward
    thunks = Thunk[
        Thunk(e, env, eval_state.callstack, args_syms[i], eval_state.memoizing) for
        (i, e) in enumerate(expr.args)
    ]
    # return a single world which is our constructor in weak head normal form
    return [(Value(expr.spt, expr.constructor, thunks), spn)]
end

function constrain(expr::CaseOf, env, output, spn::SPN, eval_state::EvalState)
    scrutinee_worlds = traced_forward(expr.scrutinee, env, spn, eval_state, :scruntinee)
    spns = SPN[]
    for (scrutinee, spn) in scrutinee_worlds
        isa(scrutinee, Value) || continue
        scrutinee.constructor in expr.constructors || continue
        case_expr = expr.cases[scrutinee.constructor]

        # expected style: Cons => (λhd tl -> body)
        num_args = length(args_of_constructor(scrutinee.constructor))
        spn = if num_args == 0
            traced_constrain(case_expr, env, output, spn, eval_state, scrutinee.constructor)
        else
            for _ = 1:num_args
                @assert case_expr isa Abs "case expression branch must have as many lambdas as the constructor has arguments"
                case_expr = case_expr.body
            end
            new_env = vcat(reverse(scrutinee.args), env)
            traced_constrain(
                case_expr,
                new_env,
                output,
                spn,
                eval_state,
                scrutinee.constructor,
            )
        end

        impossible(spn) && continue
        push!(spns, spn)
    end

    isempty(spns) && return SPN_FALSE
    return new_sum(spns, eval_state)
end

function forward(expr::CaseOf, env, spn::SPN, eval_state::EvalState)
    scrutinee_worlds = traced_forward(expr.scrutinee, env, spn, eval_state, :scrutinee)
    worlds = []
    for (scrutinee, spn) in scrutinee_worlds
        isa(scrutinee, Value) || continue
        scrutinee.constructor in expr.constructors || continue
        case_expr = expr.cases[scrutinee.constructor]

        # expected style: Cons => (λhd tl -> body)
        num_args = length(args_of_constructor(scrutinee.constructor))
        new_worlds = if num_args == 0
            traced_forward(case_expr, env, spn, eval_state, scrutinee.constructor)
        else
            for _ = 1:num_args
                @assert case_expr isa Abs "case expression branch must have as many lambdas as the constructor has arguments"
                case_expr = case_expr.body
            end
            new_env = vcat(reverse(scrutinee.args), env)
            traced_forward(case_expr, new_env, spn, eval_state, scrutinee.constructor)
        end

        append!(worlds, new_worlds)
    end
    return merge_worlds(worlds, eval_state)
end

function make_address(eval_state::EvalState)
    # eval_state.memoizing || return 0

    addr = if haskey(eval_state.id_of_callstack, eval_state.callstack)
        eval_state.id_of_callstack[eval_state.callstack]
    else
        callstack = copy(eval_state.callstack)
        push!(eval_state.callstack_of_id, callstack)
        eval_state.id_of_callstack[callstack] = length(eval_state.callstack_of_id)
    end

    # check that our reachable_addr guarantees work
    for i in eachindex(eval_state.unreachable_addrs)
        for unreachable_addr in eval_state.unreachable_addrs[i]
            @assert unreachable_addr != addr
        end
    end

    addr
end

function prim_constrain(
    op::FlipOp,
    args,
    env,
    output::Value,
    spn::SPN,
    eval_state::EvalState,
)
    # !isa(output, Bool) && return SPN_FALSE
    @assert output.constructor === :True || output.constructor === :False

    # If we are memoizing, we need a name for the flip (if we don't already have one).
    addr = make_address(eval_state)

    # First, get the possible p values.
    ps = traced_forward(args[1], env, spn, eval_state, :p_values)

    # For each p value, we need to condition on the flip having the given value.
    nodes = SPN[]
    for (val, spn) in ps
        push!(
            nodes,
            traced_condition_spn(
                spn,
                addr,
                output,
                output.constructor === :True ? log(val) : log1p(-val),
                eval_state,
            ),
        )
    end
    return new_sum(nodes, eval_state)
end

function prim_forward(op::FlipOp, args, env, spn::SPN, eval_state::EvalState)
    # If we are memoizing, we need a name for the flip (if we don't already have one).
    addr = make_address(eval_state)

    ps = traced_forward(args[1], env, spn, eval_state, :p_values)

    # The representation we are choosing to use here,
    # where a separate SPN is returned for the true 
    # and false branches, is not the most efficient, 
    # and in the case of a memoized choice, loses the fact 
    # (to some extent) that it is independent of other choices. 
    true_nodes = SPN[]
    false_nodes = SPN[]
    for (p, spn) in ps
        impossible(spn) && continue
        true_spn = traced_condition_spn(spn, addr, TRUE_VALUE, log(p), eval_state)
        false_spn = traced_condition_spn(spn, addr, FALSE_VALUE, log1p(-p), eval_state)
        if !impossible(true_spn)
            push!(true_nodes, true_spn)
        end
        if !impossible(false_spn)
            push!(false_nodes, false_spn)
        end
    end
    possibilities = []
    if length(true_nodes) > 0
        push!(possibilities, (TRUE_VALUE, new_sum(true_nodes, eval_state)))
    end
    if length(false_nodes) > 0
        push!(possibilities, (FALSE_VALUE, new_sum(false_nodes, eval_state)))
    end
    return possibilities
end

function prim_constrain(
    op::RandomDigitOp,
    args,
    env,
    output,
    spn::SPN,
    eval_state::EvalState,
)
    output.spt !== nat && return SPN_FALSE
    output_as_int = from_value(output)
    @assert output_as_int isa Int
    if output_as_int < 0 || output_as_int > 9
        return SPN_FALSE
    end

    # If we are memoizing, we need a name for the choice (if we don't already have one).
    addr = make_address(eval_state)
    return traced_condition_spn(spn, addr, output, log(0.1), eval_state)
end

function prim_forward(op::RandomDigitOp, args, env, spn::SPN, eval_state::EvalState)
    # If we are memoizing, we need a name for the choice (if we don't already have one).
    addr = make_address(eval_state)

    range = 0:9
    return merge_worlds(
        [
            (output, traced_condition_spn(spn, addr, output, log(0.1), eval_state)) for
            output in digit_values
        ],
        eval_state,
    )
end

function print_constrain_state(expr, env, output, spn::SPN, eval_state::EvalState)
    println("constrain($expr, $output)")
end


function write_spe(json; outdir = "out/spe")
    mkpath(outdir)
    timestamp = Dates.format(now(), "yyyy-mm-dd_HH-MM-SS")
    out = joinpath(outdir, "$timestamp.json")
    while isfile(out)
        timestamp *= "_"
        out = joinpath(outdir, "$timestamp.json")
    end
    open(out, "w") do io
        JSON.print(io, json)
    end
    println("http://localhost:8000/html/spe_graph.html?path=$out")
end




# How to handle laziness? 
# How to handle memoized functions that return lists?
# In general, the idea that one memoized variable corresponds to one 
# entry is not great: products (e.g. lists) should still be able to retain 
# that individual entries are independent.
# This would seem to require making it so e.g. (car l), where l is a value 
# that depends on many things, only depends on some things.
# New scalar representation: a function and a list of values that can be looked up
# in the memo table.
# Memo table only stores "atomic" random choices.
# Values are functions of those atomic choices... returning an enumeration.
#    What if it's something like, depending on the value of a variable I either depend 
#    on one thing or another?
# An alternative is: enumerate (value, memo table conditioned on that value).
#    Possibly should allow each memo table to have multiple (value, logprob) pairs?
#    Essentially like producting into the memo table, but without the need to store 
#    non-atomic values in the memo table.
#    Let's try to write that version and see if it's crazy difficult.
