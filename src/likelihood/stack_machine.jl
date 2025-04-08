export stack_constrain, StackEvalState, StackEvalConfig, StackStatsEval, run!


const EnvVal = Union{Value, Thunk, Closure, Missing, Nothing}

mutable struct ConstrainFrame
    expr::PExpr
    env
    output::Value
    spn::SPN
    name::Symbol
end

mutable struct ForwardFrame
    expr::PExpr
    env
    spn::SPN
    name::Symbol
end

name(frame::ForwardFrame) = frame.name
name(frame::ConstrainFrame) = frame.name
expr(frame::ForwardFrame) = frame.expr
expr(frame::ConstrainFrame) = frame.expr

mutable struct StackFrame
    step::Int
    outputs::Vector{Any}
    state::Any
    inner::Union{ConstrainFrame, ForwardFrame}
end


Base.@kwdef mutable struct StackStatsEval
    forward::Int = 0
    constrain::Int = 0
    condition_spn::Int = 0
    max_depth_hit::Int = 0
    depth_limit_hit::Int = 0
    eval_limit_hit::Int = 0
    time_limit_hit::Int = 0
    max_worlds::Int = 0
    total_worlds::Int = 0
    time::Float64 = 0.0
end

Base.show(io::IO, stats::StackStatsEval) = print(
    io,
    "StackStatsEval(forward: ",
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
    round(stats.time, sigdigits = 3)
)

hit_limit(stats::StackStatsEval) =
    stats.depth_limit_hit > 0 || stats.eval_limit_hit > 0 || stats.time_limit_hit > 0

function merge_stats(v::Vector{Any})
    reduce(+, v)
end

function Base.:+(a::StackStatsEval, b::StackStatsEval)
    StackStatsEval(
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
    )
end


function merge_stats(v::Vector{StackStatsEval})
    reduce(+, v; init = StackStatsEval())
end

Base.@kwdef struct StackEvalConfig
    dedup_and_factor::Bool = false # TODO turn back on
    disable_memoize::Bool = false
    record_json::Bool = false
    memoizing_default = false
    depth_limit::Int = 1000
    eval_limit::Int = 10000
    time_limit::Float64 = 10.0
end
function Base.show(io::IO, config::StackEvalConfig)
    print(io, "StackEvalConfig(")
    for k in fieldnames(typeof(config))
        print(io, k, "=", getfield(config, k), ", ")
    end
    print(io, ")")
end

Base.@kwdef struct StackReusedAllocations
    product_weights::IdDict{Vector{SPNNode}, Float64} = IdDict{Vector{SPNNode}, Float64}()
    leaf_weights::IdDict{Tuple{Scope, Any}, Float64} = IdDict{Tuple{Scope, Any}, Float64}()
    children_as_products::Vector{Tuple{Vector{SPNNode}, Float64}} = Vector{Tuple{Vector{SPNNode}, Float64}}()
    children_processed::Vector{SPN} = Vector{SPN}()
    vec_alloc::RegionAlloc{Vector{Any}} = RegionAlloc{Vector{Any}}()
end

mutable struct StackEvalState
    config::StackEvalConfig
    stack::Vector{StackFrame}
    callstack::Vector{Symbol}
    id_of_callstack::Dict{Vector{Symbol}, Address}
    callstack_of_id::Vector{Vector{Symbol}}
    memoizing::Bool
    depth::Int
    start_time::Float64
    stats::StackStatsEval
    spn_hash::SPNHash
    reused::StackReusedAllocations

    StackEvalState(config::StackEvalConfig) = new(
        config,
        StackFrame[],
        Symbol[],
        Dict{Vector{Symbol}, Address}(),
        Vector{Vector{Symbol}}(),
        config.memoizing_default,
        0,
        0.,
        StackStatsEval(),
        SPNHash(),
        StackReusedAllocations(),
    )
    StackEvalState() = StackEvalState(StackEvalConfig())
end

make_state(config::StackEvalConfig) = StackEvalState(config)

# constrain(expr, env, output, eval_state = nothing) =
#     inner_constrain(expr, env, output, eval_state)
function inner_constrain(expr, env, output, eval_state = nothing)
    if isnothing(eval_state)
        eval_state = StackEvalState()
    end
    if expr isa String
        expr = parse_expr(expr)
    end
    if !(output isa Value)
        output = to_value(output)
    end
    if !(env isa Vector{Value})
        env = to_value.(env)
    end
    stack_constrain(expr, env, output, eval_state)
end

function stack_constrain(expr::PExpr, env, output, eval_state)
    env = mask_thunk_env(env, expr)
    @assert isempty(eval_state.stack)
    frame = ConstrainFrame(expr, env, output, SPN_TRUE, :timed)
    push_frame!(eval_state, frame)
    res = run!(eval_state)
    # println("$expr in $env => $output with P=$(exp(weight(res)))")
    res
end

@inline function vec(eval_state::StackEvalState)::Vector{Any}
    get(eval_state.reused.vec_alloc)
end

@inline function push_frame!(eval_state::StackEvalState, frame::Union{ConstrainFrame, ForwardFrame})
    push_region!(eval_state.reused.vec_alloc)
    push!(eval_state.stack, StackFrame(1, vec(eval_state), nothing, frame))
    push!(eval_state.callstack, name(frame))
    eval_state
end
@inline function pop_frame!(eval_state::StackEvalState)
    outer = eval_state.stack[end]
    cleanup(outer.inner, expr(outer.inner), outer.step, outer.outputs, outer.state, eval_state)
    pop!(eval_state.stack)
    pop!(eval_state.callstack)
    pop_region!(eval_state.reused.vec_alloc)
    eval_state
end

@inline function check_limits(eval_state::StackEvalState)::Symbol
    if time() - eval_state.start_time > eval_state.config.time_limit
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

@inline function check_time_limit(spn, name, output, new_weight, eval_state::StackEvalState)
    eval_state.stats.condition_spn += 1
    if time() - eval_state.start_time > eval_state.config.time_limit
        eval_state.stats.time_limit_hit = 1
        return false
    end
    return true
end

function run!(eval_state::StackEvalState)
    @assert length(eval_state.stack) == 1
    @assert length(eval_state.callstack) == 1
    @assert eval_state.memoizing == eval_state.config.memoizing_default
    eval_state.stats = StackStatsEval()
    empty!(eval_state.id_of_callstack)
    empty!(eval_state.callstack_of_id)
    eval_state.start_time = time()
    result = nothing
    while true
        eval_state.depth = length(eval_state.stack)
        outer_frame = eval_state.stack[end]::StackFrame
        limit_hit = check_limits(eval_state)
        if limit_hit !== :none
            output = outer_frame.inner isa ConstrainFrame ? SPN_FALSE : []
            pop_frame!(eval_state)
            if isempty(eval_state.stack)
                result = output
                break
            end
            push!(eval_state.stack[end].outputs, output)
            continue
        end

        eval_state.stats.constrain += outer_frame.inner isa ConstrainFrame
        eval_state.stats.forward += outer_frame.inner isa ForwardFrame

        output = process(outer_frame.inner, expr(outer_frame.inner), outer_frame.step, outer_frame.outputs, outer_frame.state, eval_state)
        outer_frame.step += 1

        if output isa Tuple
            outer_frame.state = output[2]
            output = output[1]
        end


        if output isa ConstrainFrame || output isa ForwardFrame
            push_frame!(eval_state, output)
        elseif ismissing(output)
            push!(eval_state.stack[end].outputs, missing)
            # nothing to do here! We just run the same frame again incremented
        else
            # we got a value! pop the stack and give it to our parent
            @assert !isnothing(output)
            pop_frame!(eval_state)
            if isempty(eval_state.stack)
                result = output
                break
            end
            push!(eval_state.stack[end].outputs, output)
        end
    end
    eval_state.stats.time = round(time() - eval_state.start_time, sigdigits = 3)
    return result, eval_state
end
weight(res::Tuple{SPN, StackEvalState}) = weight(res[2].spn_hash, res[1])

cleanup(frame::ConstrainFrame, expr, step, outputs, state, eval_state) = nothing
cleanup(frame::ForwardFrame, expr, step, outputs, state, eval_state) = nothing

function process(frame::ConstrainFrame, expr::If, step, outputs, state, eval_state)
    if step == 1
        ConstrainFrame(expr.cond, frame.env, TRUE_VALUE, frame.spn, :cond)
    elseif step == 2
        ConstrainFrame(expr.cond, frame.env, FALSE_VALUE, frame.spn, :cond)
    elseif step == 3
        cond_true_spn = outputs[1]::SPN
        impossible(cond_true_spn) && return missing
        ConstrainFrame(expr.then_expr, frame.env, frame.output, cond_true_spn, :then_expr)
    elseif step == 4
        cond_false_spn = outputs[2]::SPN
        impossible(cond_false_spn) && return missing
        ConstrainFrame(expr.else_expr, frame.env, frame.output, cond_false_spn, :else_expr)
    elseif step == 5
        nodes = SPN[]
        !ismissing(outputs[3]) && push!(nodes, outputs[3]::SPN)
        !ismissing(outputs[4]) && push!(nodes, outputs[4]::SPN)
        new_sum(nodes, eval_state)
    else
        error("invalid step: $step")
    end
end

function process(frame::ForwardFrame, expr::If, step, outputs, state, eval_state)
    if step == 1
        ConstrainFrame(expr.cond, frame.env, TRUE_VALUE, frame.spn, :cond)
    elseif step == 2
        ConstrainFrame(expr.cond, frame.env, FALSE_VALUE, frame.spn, :cond)
    elseif step == 3
        cond_true_spn = outputs[1]::SPN
        impossible(cond_true_spn) && return missing
        ForwardFrame(expr.then_expr, frame.env, cond_true_spn, :then_expr)
    elseif step == 4
        cond_false_spn = outputs[2]::SPN
        impossible(cond_false_spn) && return missing
        ForwardFrame(expr.else_expr, frame.env, cond_false_spn, :else_expr)
    elseif step == 5
        worlds = []
        !ismissing(outputs[3]) && append!(worlds, outputs[3])
        !ismissing(outputs[4]) && append!(worlds, outputs[4])
        return merge_worlds(worlds, eval_state)
    else
        error("invalid step: $step")
    end
end

function extend_env(lam::Closure, thunk::Thunk)
    new_env = copy(lam.env)
    x = var_is_free(lam.expr, 1) ? thunk : nothing
    pushfirst!(new_env, x)
    new_env
end

function process(frame::ConstrainFrame, expr::App, step, outputs, state, eval_state)
    if step == 1
        thunk = Thunk(expr.x, frame.env, eval_state.callstack, :x, true)
        return (ForwardFrame(expr.f, frame.env, frame.spn, :f), thunk)
    end
    idx = step - 1
    if idx <= length(outputs[1])
        lam, spn = outputs[1][idx]::Tuple{Closure, SPN}
        new_env = extend_env(lam, state)
        return ConstrainFrame(lam.expr, new_env, frame.output, spn, :closure)
    end

    @assert idx == length(outputs[1]) + 1

    res = SPN[Int(e) for e in (@view outputs[2:end])]
    return new_sum(res, eval_state)
end

function process(frame::ForwardFrame, expr::App, step, outputs, state, eval_state)
    if step == 1
        thunk = Thunk(expr.x, frame.env, eval_state.callstack, :x, true)
        return (ForwardFrame(expr.f, frame.env, frame.spn, :f), thunk)
    end
    idx = step - 1
    if idx <= length(outputs[1])
        lam, spn = outputs[1][idx]::Tuple{Closure, SPN}
        new_env = extend_env(lam, state)
        return ForwardFrame(lam.expr, new_env, spn, :closure)
    end

    @assert idx == length(outputs[1]) + 1
    return merge_worlds(reduce(vcat,@view outputs[2:end]), eval_state)
end

function process(frame::ConstrainFrame, expr::CaseOf, step, outputs, state, eval_state)
    if step == 1
        return ForwardFrame(expr.scrutinee, frame.env, frame.spn, :scrutinee)
    end

    idx = step - 1
    if idx <= length(outputs[1])
        scrutinee, spn = outputs[1][idx]::Tuple{Value, SPN}
        isa(scrutinee, Value) || return missing
        scrutinee.constructor in expr.constructors || return missing
        case_expr = expr.cases[scrutinee.constructor]

        # expected style: Cons => (λhd tl -> body)
        num_args = length(args_of_constructor(scrutinee.constructor))
        if num_args == 0
            return ConstrainFrame(case_expr, frame.env, frame.output, spn, scrutinee.constructor)
        else
            for _ = 1:num_args
                @assert case_expr isa Abs "case expression branch must have as many lambdas as the constructor has arguments"
                case_expr = case_expr.body
            end
            new_env = vcat(reverse(scrutinee.args), frame.env)
            return ConstrainFrame(case_expr, new_env, frame.output, spn, scrutinee.constructor)
        end
    end

    @assert idx == length(outputs[1]) + 1

    res = SPN[e for e in (@view outputs[2:end]) if !(e isa Missing)]

    return new_sum(res, eval_state)
end

function process(frame::ForwardFrame, expr::CaseOf, step, outputs, state, eval_state)
    if step == 1
        return ForwardFrame(expr.scrutinee, frame.env, frame.spn, :scrutinee)
    end

    idx = step - 1
    if idx <= length(outputs[1])
        scrutinee, spn = outputs[1][idx]::Tuple{Value, SPN}
        isa(scrutinee, Value) || return missing
        scrutinee.constructor in expr.constructors || return missing
        case_expr = expr.cases[scrutinee.constructor]

        # expected style: Cons => (λhd tl -> body)
        num_args = length(args_of_constructor(scrutinee.constructor))
        if num_args == 0
            return ForwardFrame(case_expr, frame.env, spn, scrutinee.constructor)
        else
            for _ = 1:num_args
                @assert case_expr isa Abs "case expression branch must have as many lambdas as the constructor has arguments"
                case_expr = case_expr.body
            end
            new_env = vcat(reverse(scrutinee.args), frame.env)
            return ForwardFrame(case_expr, new_env, spn, scrutinee.constructor)
        end
    end

    @assert idx == length(outputs[1]) + 1

    return merge_worlds(reduce(vcat,skipmissing(outputs[2:end]);init=[]), eval_state)
end

function process(frame::ForwardFrame, expr::PrimOp, step, outputs, state, eval_state)
    process_prim(frame, expr, expr.op, step, outputs, state, eval_state)
end
function process(frame::ConstrainFrame, expr::PrimOp, step, outputs, state, eval_state)
    process_prim(frame, expr, expr.op, step, outputs, state, eval_state)
end

function process_prim(frame::ConstrainFrame, expr::PrimOp, ::RandomDigitOp, step, outputs, state, eval_state)
    @assert step == 1
    output_as_int = from_value(frame.output)
    # @show output_as_int
    !(output_as_int isa Int) && return SPN_FALSE
    if output_as_int < 0 || output_as_int > 9
        return SPN_FALSE
    end

    # If we are memoizing, we need a name for the choice (if we don't already have one).
    addr = make_address(eval_state)
    return traced_condition_spn(frame.spn, addr, frame.output, log(0.1), eval_state)
end


function process_prim(frame::ForwardFrame, expr::PrimOp, ::RandomDigitOp, step, outputs, state, eval_state)
    @assert step == 1
    addr = make_address(eval_state)
    return merge_worlds(
        [
            (output, traced_condition_spn(frame.spn, addr, output, log(0.1), eval_state)) for
            output in digit_values
        ],
        eval_state,
    )
end




function process_prim(frame::ConstrainFrame, expr::PrimOp, ::FlipOp, step, outputs, state, eval_state)
    if step == 1
        @assert frame.output.constructor === :True || frame.output.constructor === :False
        # If we are memoizing, we need a name for the flip (if we don't already have one).
        addr = make_address(eval_state)
        return (ForwardFrame(expr.args[1], frame.env, frame.spn, :p_values), addr)
    end

    addr = state

    @assert step == 2
    nodes = SPN[]
    for (p, spn) in outputs[1]::Vector{Tuple{Float64, SPN}}
        push!(
            nodes,
            traced_condition_spn(
                spn,
                addr,
                frame.output,
                frame.output.constructor === :True ? log(p) : log1p(-p),
                eval_state,
            ),
        )
    end
    return new_sum(nodes, eval_state)
end


function process_prim(frame::ForwardFrame, expr::PrimOp, ::FlipOp, step, outputs, state, eval_state)
    if step == 1
        # If we are memoizing, we need a name for the flip (if we don't already have one).
        addr = make_address(eval_state)
        return (ForwardFrame(expr.args[1], frame.env, frame.spn, :p_values), addr)
    end

    addr = state

    @assert step == 2
    true_nodes = SPN[]
    false_nodes = SPN[]
    for (p, spn) in outputs[1]::Vector{Tuple{Float64, SPN}}
        true_spn = traced_condition_spn(spn, addr, TRUE_VALUE, log(p), eval_state)
        false_spn = traced_condition_spn(spn, addr, FALSE_VALUE, log1p(-p), eval_state)
        !impossible(true_spn) && push!(true_nodes, true_spn)
        !impossible(false_spn) && push!(false_nodes, false_spn)
    end

    possibilities = []
    !isempty(true_nodes) && push!(possibilities, (true, new_sum(true_nodes, eval_state)))
    !isempty(false_nodes) && push!(possibilities, (false, new_sum(false_nodes, eval_state)))

    return possibilities
end

constrain_value(val, output, spn, step, outputs, state, eval_state) =
    val == output ? spn : SPN_FALSE
@inline forward_value(val, spn, step, outputs, state, eval_state) = [(val, spn)]
cleanup_constrain_value(val, output, spn, step, outputs, state, eval_state) = nothing
cleanup_forward_value(val, spn, step, outputs, state, eval_state) = nothing

function process(frame::ConstrainFrame, expr::Const, step, outputs, state, eval_state)
    return constrain_value(expr.val, frame.output, frame.spn, step, outputs, state, eval_state)
end

function process(frame::ForwardFrame, expr::Const, step, outputs, state, eval_state)
    return [(expr.val, frame.spn)]
end

function process(frame::ConstrainFrame, expr::Var, step, outputs, state, eval_state)
    expr.idx > length(frame.env) && return []
    val = frame.env[expr.idx]
    constrain_value(val, frame.output, frame.spn, step, outputs, state, eval_state)
end
function cleanup(frame::ConstrainFrame, expr::Var, step, outputs, state, eval_state)
    expr.idx > length(frame.env) && return
    val = frame.env[expr.idx]
    cleanup_constrain_value(val, frame.output, frame.spn, step, outputs, state, eval_state)
end

function process(frame::ForwardFrame, expr::Var, step, outputs, state, eval_state)
    expr.idx > length(frame.env) && return []
    val = frame.env[expr.idx]
    forward_value(val, frame.spn, step, outputs, state, eval_state)
end
function cleanup(frame::ForwardFrame, expr::Var, step, outputs, state, eval_state)
    expr.idx > length(frame.env) && return
    val = frame.env[expr.idx]
    cleanup_forward_value(val, frame.spn, step, outputs, state, eval_state)
end


function constrain_value(thunk::Thunk, output, spn, step, outputs, state, eval_state)
    if step == 1
        old_stack = eval_state.callstack
        old_memoizing = eval_state.memoizing
        eval_state.callstack = copy(thunk.callstack)
        eval_state.memoizing = thunk.memoizing
        return (ConstrainFrame(thunk.expr, thunk.env, output, spn, thunk.name), (old_memoizing, old_stack))
    end
    @assert step == 2
    return outputs[1]::SPN
end

function cleanup_constrain_value(thunk::Thunk, output, spn, step, outputs, state, eval_state)
    step == 1 && return
    eval_state.memoizing, eval_state.callstack = state;
end


function forward_value(thunk::Thunk, spn, step, outputs, state, eval_state)
    if step == 1
        old_stack = eval_state.callstack
        old_memoizing = eval_state.memoizing
        eval_state.callstack = copy(thunk.callstack)
        eval_state.memoizing = thunk.memoizing
        return (ForwardFrame(thunk.expr, thunk.env, spn, thunk.name), (old_memoizing, old_stack))
    end
    @assert step == 2
    return outputs[1]
end

function cleanup_forward_value(thunk::Thunk, spn, step, outputs, state, eval_state)
    step == 1 && return
    eval_state.memoizing, eval_state.callstack = state;
end

function process(frame::ConstrainFrame, expr::ConstReal, step, outputs, state, eval_state)
    return constrain_value(expr.val, frame.output, frame.spn, step, outputs, state, eval_state)
end

function process(frame::ForwardFrame, expr::ConstReal, step, outputs, state, eval_state)
    return [(expr.val, frame.spn)]
end

function process(frame::ConstrainFrame, expr::ConstBool, step, outputs, state, eval_state)
    return constrain_value(expr.val, frame.output, frame.spn, step, outputs, state, eval_state)
end

function process(frame::ForwardFrame, expr::ConstBool, step, outputs, state, eval_state)
    return [(expr.val, frame.spn)]
end

function process(frame::ConstrainFrame, expr::Abs, step, outputs, state, eval_state)
    error("cannot constrain lambda")
end

function process(frame::ForwardFrame, expr::Abs, step, outputs, state, eval_state)
    return [(Closure(expr.body, frame.env), frame.spn)]
end

function process(frame::ConstrainFrame, expr::Y, step, outputs, state, eval_state)
    error("cannot constrain lambda")
end

function process(frame::ForwardFrame, expr::Y, step, outputs, state, eval_state)
    @assert expr.f isa Abs && expr.f.body isa Abs "y-combinator must be applied to a double-lambda"

    # Could broaden implementation to allow for non-lambda functions, but that seems somewhat unnecessary
    # since its not a big hassle to write the two lambdas. Also I tried it a bit and it's hard to get right
    # when you are trying to set up the self-referential closure for a two-argument lambda through evaluating
    # each in turn. At least if you want to get the exact semantics of possible references to the outer closure
    # when constructing the inner one it gets a bit weird. All in all pretty unnecessary too since you can just
    # eta expand things to put them in this form.

    closure = make_self_loop(expr.f.body.body, frame.env)

    # set up a closure with a circular reference
    # @show length(closure.env)
    return [(closure, frame.spn)]
end

# (Y f) = (f (Y f))
# (Y (λrec 0)) = ((λrec 0) (Y (λrec 0)))

function process(frame::ConstrainFrame, expr::Defined, step, outputs, state, eval_state)
    # always execute Defined with a blanked out environment
    if step == 1
        return ConstrainFrame(
            lookup(expr.name).expr,
            EMPTY_ENV,
            frame.output,
            frame.spn,
            expr.name
            )
    end
    @assert step == 2
    return outputs[1]::SPN
end

function process(frame::ForwardFrame, expr::Defined, step, outputs, state, eval_state)
    # always execute Defined with a blanked out environment
    if step == 1
        return ForwardFrame(
            lookup(expr.name).expr,
            EMPTY_ENV,
            frame.spn,
            expr.name
        )
    end
    @assert step == 2
    return outputs[1]
end


function process(frame::ConstrainFrame, expr::Construct, step, outputs, state, eval_state)
    if step == 1
        @assert length(expr.args) == length(args_of_constructor(expr.constructor))
        !isa(frame.output, Value) && return SPN_FALSE
        frame.output.spt != expr.spt && return SPN_FALSE
        frame.output.constructor != expr.constructor && return SPN_FALSE
        @assert length(frame.output.args) == length(expr.args)
    end

    if step <= length(expr.args)
        # get the spn from the previous step (initialize with frame.spn) since we need
        # to thread the spns along thru all these calls
        spn = step > 1 ? outputs[step-1]::SPN : frame.spn
        impossible(spn) && return SPN_FALSE

        return ConstrainFrame(
            expr.args[step],
            frame.env,
            frame.output.args[step],
            spn,
            args_syms[step],
        )
    end

    @assert step == length(expr.args) + 1
    spn = step > 1 ? outputs[step-1]::SPN : frame.spn
    return spn
end

function process(frame::ForwardFrame, expr::Construct, step, outputs, state, eval_state)
    @assert step == 1
    @assert length(expr.args) == length(args_of_constructor(expr.constructor))
    thunks = [Thunk(e, frame.env, eval_state.callstack, args_syms[i], eval_state.memoizing) for (i, e) in enumerate(expr.args)]
    # return a single world which is our constructor in weak head normal form
    return [
        (Value(expr.spt, expr.constructor, thunks), frame.spn)
    ]
end


function make_address(eval_state)
    # eval_state.memoizing || return 0

    addr = if haskey(eval_state.id_of_callstack, eval_state.callstack)
        eval_state.id_of_callstack[eval_state.callstack]
    else
        callstack = copy(eval_state.callstack)
        push!(eval_state.callstack_of_id, callstack)
        eval_state.id_of_callstack[callstack] = length(eval_state.callstack_of_id)
    end

    # check that our reachable_addr guarantees work
    # for i in eachindex(eval_state.unreachable_addrs)
    #     for unreachable_addr in eval_state.unreachable_addrs[i]
    #         @assert unreachable_addr != addr
    #     end
    # end

    addr
end

