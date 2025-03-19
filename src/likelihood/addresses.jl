

@inline function isprefix(prefix::Vector{T}, x::Vector{T}) where {T}
    length(x) >= length(prefix) || return false
    for i in eachindex(prefix)
        if prefix[i] != x[i]
            return false
        end
    end
    return true
end

mutable struct ReachState
    callstack::Vector{Symbol}
    scope::Vector{Vector{Symbol}}
    scope_seen::BitVector
    done::Bool
    need_closures::Bool
    depth::Int
    depth_limit::Int
    seen_thunk::Dict{Thunk, Vector{Closure}}
end

const EMP::Vector{Address} = Address[]
function reachable_scope(
    expr::PExpr,
    env,
    scope::Vector{Int},
    eval_state::EvalState,
)::BitVector
    isempty(scope) && return EMP
    scope = Vector{Symbol}[eval_state.callstack_of_id[id] for id in scope]
    scope_seen = falses(length(scope))
    callstack = copy(eval_state.callstack) # could actually just have this not be a copy btw
    state = ReachState(
        callstack,
        scope,
        scope_seen,
        isempty(scope),
        false,
        eval_state.depth,
        eval_state.config.depth_limit,
        Dict{Thunk, Vector{Closure}}(),
    )
    reachable_scope(expr, env, state)
    scope_seen
end

function var_reachable_scope(var::Thunk, state)::Vector{Closure}
    haskey(state.seen_thunk, var) && return state.seen_thunk[var]
    # @show var.expr
    old_callstack = state.callstack
    # old_need_closures = state.need_closures
    state.callstack = var.callstack
    # state.need_closures = true
    # go catch up by greedily evaluating the thunk's env
    # var_env = env_reachable_scope(var.env, state)
    res = traced_reachable_scope(var.expr, var.env, state, var.name)
    state.callstack = old_callstack
    # state.need_closures = old_need_closures
    state.seen_thunk[var] = res
    res
end

function var_reachable_scope(var::Closure, state)::Vector{Closure}
    # go catch up by greedily evaluating the closure's env
    # but watch out for y-combinator induced loops
    if var.env[1] === var
        # y combinator induced loop
        closure = Closure(var.expr, EMPTY_ENV)
        closure.env = [Closure[closure], var.env[2:end]...]
        Closure[closure]
    else
        # normal closure, no loop
        Closure[var]
    end
end

var_reachable_scope(var::Vector{Closure}, state) = var
var_reachable_scope(::Any, state) = EMPTY_CLOSURES


# note that this does not get all the reachable thunks in the env of the thunk itself!
function reachable_thunks(expr::PExpr, env, is_closure = false, thunks = Vector{Thunk}())
    for (i, var) in enumerate(env)
        # check for y-combinator induced loops
        is_closure &&
            i == 1 &&
            var isa Closure &&
            var.expr === expr &&
            var.env === env &&
            continue
        # check if var not used; and in closure we need +1 bc of shifting when prepending the closure arg
        var_is_free(expr, is_closure ? i + 1 : i) || continue
        var isa Thunk && push!(thunks, var)
        var isa Closure && reachable_thunks(var.expr, var.env, true, thunks)
    end
    thunks
end


function traced_reachable_scope(
    expr::PExpr,
    env,
    state::ReachState,
    name::Symbol,
)::Vector{Closure}
    state.done && return EMPTY_CLOSURES

    push!(state.callstack, name)
    # println("  "^state.depth, "traced_reachable_scope: ", state.callstack, " ", expr)

    # @show state.need_closures
    # prefix-based pruning: if the current callstack is not a prefix of anything in the scope,
    # it can't possibly reach anything in the scope, so we can just return empty
    # However, we can only do this when we haven't been asked to provide the set of closures that the term
    # might eval to, since those might have been requested from us. 
    if !state.need_closures
        prefix_exists = false
        for i in eachindex(state.scope)
            state.scope_seen[i] && continue
            if isprefix(state.callstack, state.scope[i])
                prefix_exists = true
                break
            end
        end
        if !prefix_exists
            pop!(state.callstack)

            # we're done! But... wait! Is there some thunk in our env that could explain any of the scope?
            old_need_closures = state.need_closures
            state.need_closures = false # when forcing any thunks in our env here we dont care whether they return closures
            thunks = reachable_thunks(expr, env)
            for thunk in thunks
                # we already collected all thunks + accessible closures, tho we didnt
                # get thunks within thunks bc those will be handled by var_reachable_scope anyways
                # when it hits this same loop internally
                var_reachable_scope(thunk, state)
                state.done && break
            end

            state.need_closures = old_need_closures
            return EMPTY_CLOSURES

            # for (idx,var) in enumerate(env)
            #     var isa Thunk || var isa Closure || continue
            #     var_is_free(expr, idx) || continue # we only care about thunks that are actually used somewhere potentially (overappx is fine)

            #     var_reachable_scope(var, state)
            #     state.done && break

            # for i in eachindex(state.scope)
            #     state.scope_seen[i] && continue
            #     # we can't just prefix check, because what if the Thunk body has a
            #     # free var and THAT var bound in the thunks env is the one that uses the thing!
            #     # so we need to var_reachable_scope which will itself do the prefix check as appropriate
            #     var_reachable_scope(var, state)
            #     break # skip rest of scope addrs, move onto next var
            #     # if isprefix(var.callstack, state.scope[i])
            #     #     # this thunk shares a prefix with an unseen scope addr so lets force it! Note we've
            #     #     # already set need_closures=false.
            #     #     var_reachable_scope(var, state)
            #     #     break # skip rest of scope addrs, move onto next var
            #     # end
            # end
            # end
        end
    end

    # handle limit hits
    if state.depth >= state.depth_limit
        res = []
        @assert pop!(state.callstack) === name
        return res
    end

    state.depth += 1
    result = reachable_scope(expr, env, state)
    state.depth -= 1

    @assert pop!(state.callstack) === name
    return result
end

const EMPTY_CLOSURES::Vector{Closure} = Closure[]

function union_closures(a::Vector{Closure}, b::Vector{Closure})
    isempty(a) && return b
    isempty(b) && return a
    vcat(a, b)
end

reachable_scope(::Const, env, state) = EMPTY_CLOSURES
reachable_scope(::ConstReal, env, state) = EMPTY_CLOSURES
reachable_scope(::ConstBool, env, state) = EMPTY_CLOSURES
reachable_scope(e::Var, env, state) = var_reachable_scope(env[e.idx], state)
reachable_scope(e::Abs, env, state) = [Closure(e.body, env)]
function reachable_scope(e::Y, env, state)
    @assert e.f isa Abs && e.f.body isa Abs "y-combinator must be applied to a double-lambda"
    closure = Closure(e.f.body.body, EMPTY_ENV)
    closure.env = [Closure[closure], env...]
    return Closure[closure]
end
function reachable_scope(e::If, env, state)
    old_need_closures = state.need_closures
    state.need_closures = false # this is a cond, we dont need to trace closures
    traced_reachable_scope(e.cond, env, state, :cond)
    state.need_closures = old_need_closures # but for branches we need to do whatever our parent was doing
    union_closures(
        traced_reachable_scope(e.then_expr, env, state, :then_expr),
        traced_reachable_scope(e.else_expr, env, state, :else_expr),
    )
end
function reachable_scope(e::App, env, state)
    # we do need to ask for the possible closures returned by `x` too sadly. If we knew that `x` was not an arrow
    # type we wouldnt need to do this which would help with the prefix-based pruning. But that's a bit of a pain and
    # given that x is probably pretty small this likely is not a big deal.
    old_need_closures = state.need_closures
    state.need_closures = true
    lams = traced_reachable_scope(e.f, env, state, :f)

    # instead of thunking we actually strictly eval the argument after a quick free var check
    # to make sure it's used at least once (note this is pretty cursory, for example if it's used
    # as an arg to a deeper App we dont go and try to figure out if that App uses it or not, we just
    # say it's used)
    # The advantage of strict eval here is since our env will only ever hold sets of closures instead of
    # randomness-containing thunks can do the randomness address prefix check more aggressively in
    # traced_reachable_scope because we know the env cant create new address prefixes. 

    state.need_closures = old_need_closures # when it comes executing the body of the lambda, we can do whatever our parent was doing


    x_closures = (
        any(closure -> var_is_free(closure.expr, 1), lams) ?
        Thunk(e.x, env, state.callstack, :x, true) # not traced_* since we wanna mirror how SPE traces thunks
        : EMPTY_CLOSURES
    ) # we're never using this arg anyways so dont need to trace it and can pretend it just returns nothing

    res = EMPTY_CLOSURES
    for closure in lams
        new_env = [x_closures, closure.env...]
        res = union_closures(
            res,
            traced_reachable_scope(closure.expr, new_env, state, :closure),
        )
    end
    res
end

reachable_scope(e::Defined, env, state) =
    traced_reachable_scope(get_def(e.name).expr, EMPTY_ENV, state, e.name)
reachable_scope(e::Root, env, state) = reachable_scope(e.body, env, state)

function reachable_scope(e::CaseOf, env, state)
    old_need_closures = state.need_closures
    state.need_closures = false # we dont need to trace closures for the scrutinee bc its a bool
    traced_reachable_scope(e.scrutinee, env, state, :scrutinee)
    state.need_closures = old_need_closures # but for branches we need to do whatever our parent was doing
    for constructor in e.constructors
        case_expr = e.cases[constructor]

        # # expected style: Cons => λhead. λtail. body 
        num_args = length(args_of_constructor(constructor))

        # since we were strict with Constructor() we actually dont need to worry about these arg bindings
        new_env = num_args == 0 ? env : vcat(fill(EMPTY_CLOSURES, num_args), env)
        for _ = 1:num_args
            @assert case_expr isa Abs "case expression branch must have as many lambdas as the constructor has arguments"
            case_expr = case_expr.body
        end

        traced_reachable_scope(case_expr, new_env, state, constructor)
    end
    EMPTY_CLOSURES
end

function reachable_scope(e::Construct, env, state)
    # NOT lazy – but we still wont hit infinities thanks to our state.scope
    old_need_closures = state.need_closures
    state.need_closures = false # we dont need to trace closures for the scrutinee bc its a bool
    for i = 1:length(e.args)
        @assert isempty(traced_reachable_scope(e.args[i], env, state, args_syms[i]))
    end
    state.need_closures = old_need_closures
    EMPTY_CLOSURES
end

function reached_address(state::ReachState)
    for i = 1:length(state.scope)
        state.scope_seen[i] && continue
        if state.scope[i] == state.callstack
            state.scope_seen[i] = true
            # println("seen ", state.callstack)
        end
    end
    EMPTY_CLOSURES
end

reachable_scope(e::PrimOp, env, state) = reachable_scope_prim(e.op, e.args, env, state)
function reachable_scope_prim(::FlipOp, args, env, state)
    traced_reachable_scope(args[1], env, state, :p_values)
    reached_address(state)
end
reachable_scope_prim(::RandomDigitOp, args, env, state) = reached_address(state)
reachable_scope_prim(::RandomNatOp, args, env, state) = reached_address(state)
