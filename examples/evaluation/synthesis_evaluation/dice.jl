using Dice: List, Nat, flip, match, prob_equals, @dice_ite
using Dice


module Unit
    using Dice
    @inductive t U()
end

# (x::Unit.t)(y) = Unit.U()

function geom(fuel; p=0.5)
    fuel == 0 && return Nat.Z()
    # @show fuel
    @dice_ite if flip(p)
        Nat.Z()
    else
        Nat.S(geom(fuel-1; p=p))
    end
end

make_nat(n) = if n == 0; Nat.Z(); else Nat.S(make_nat(n-1)); end
make_list(l) = if isempty(l); Dice.Nil(Nat.t); else Dice.Cons(Nat.t, make_nat(l[1]), make_list(l[2:end])); end

dicetype(::Type{Int}) = Nat.t
dicetype(::Type{Nothing}) = Unit.t
dicetype(::Type{Vector{T}}) where T = List{dicetype(T)}

asdice(xs::Vector{T}) where T = if isempty(xs); Dice.Nil(dicetype(T)); else Dice.Cons(dicetype(T), asdice(xs[1]), asdice(xs[2:end])); end
asdice(x::Int) = if x == 0; Nat.Z(); else Nat.S(asdice(x-1)); end
asdice(::Nothing) = Unit.U()


# @define "+" "int -> int -> int" "(Y (λrec x y -> (case y of O => x | S => (λy2 -> (S (rec x y2))))))"
function Base.:(+)(x::Nat.t, y::Nat.t)
    match(y, [
        :Z => () -> x
        :S => y′ -> Nat.S(x) + y′
    ])
end

# saturating subtraction
# @define "-" "int -> int -> int" "(Y (λrec x y -> (case y of O => x | S => (λy2 -> (case x of O => (O) | S => (λx2 -> (rec x2 y2)))))))"
function Base.:(-)(x::Nat.t, y::Nat.t)
    match(y, [
        :Z => () -> x
        :S => (y′) -> match(x, [:Z => () -> Nat.Z(), :S => (x′) -> x′ - y′])
    ])
end

# @define "==" "int -> int -> bool" "(Y (λ rec x y -> (case x of O => (case y of O => true | S => (λ _ -> false)) | S => (λ x2 -> (case y of O => false | S => (λ y2 -> (rec x2 y2)))))))"
function Base.:(==)(n1::Nat.t, n2::Nat.t)
    match(n1, [
        :Z => () -> match(n2, [:Z => () -> true, :S => (n2pred) -> false]),
        :S => (n1pred) -> match(n2, [:S => (n2pred) -> n1pred == n2pred, :Z => () -> false]),
    ])
end

# @define iseven "int -> bool" "(Y (λ rec x -> (case x of O => true | S => (λ x2 -> (not (rec x2))))))"
function iseven(n::Nat.t)
    match(n, [
        :Z => () -> true,
        :S => (npred) -> !iseven(npred)
    ])
end

# @define ">" "int -> int -> bool" "(Y (λ rec x y -> (case x of O => false | S => (λ x2 -> (case y of O => true | S => (λ y2 -> (rec x2 y2)))))))"
function Base.:(>)(n1::Nat.t, n2::Nat.t)
    match(n1, [
        :Z => () -> false,
        :S => (n1pred) -> match(n2, [:Z => () -> true, :S => (n2pred) -> n1pred > n2pred]),
    ])
end


# @define "old_list_eq" "(Y (λ rec xs ys -> (case xs of Nil => (case ys of Nil => true | Cons => (λ _ _ -> false)) | Cons => (λ xhd xtl -> (case ys of Nil => false | Cons => (λ yhd ytl -> (my_and (eq_nat xhd yhd) (rec xtl ytl))))))))"
# here we use if-statments to do the short circuiting my_and
function Base.:(==)(l1::List{T}, l2::List{T}) where T
    match(l1, [
        :Nil => () -> match(l2, [:Nil => () -> true, :Cons => (hd, tl) -> false]),
        :Cons => (x, xs) -> match(l2, [:Cons => (y, ys) -> (@dice_ite if (x == y); (xs == ys); else; false; end), :Nil => () -> false]),
    ])
end

# @define map "(int -> int) -> list -> list" "(Y (λ rec f xs -> (case xs of Nil => (Nil) | Cons => (λhd tl -> (Cons (f hd) (rec f tl))))))"
# this is specific to any -> nat
function map_impl(f, l::List)
    match(l, [
        :Nil => () -> Dice.Nil(Nat.t),
        :Cons => (hd, tl) -> Dice.Cons(Nat.t, f(hd), map_impl(f, tl)),
    ])
end


# @define scanl "(int -> int -> int) -> int -> list -> list" """
# (Y (λrec f acc xs ->
#     (case xs of Nil => (Nil)
#             | Cons => (λhd tl ->
#                         (let (acc' (f acc hd))
#                             (Cons acc' (rec f acc' tl))
#                         ))
#     )
# ))
# """
# this is specific to (any, any) -> nat
function scanl_impl(f, acc, l::List)
    match(l, [
        :Nil => () -> Dice.Nil(Nat.t),
        :Cons => (hd, tl) -> begin
            acc′ = f(acc)(hd)
            # state.stats.hit_limit && return Unit.U()
            rec = scanl_impl(f, acc′, tl)
            # state.stats.hit_limit && return Unit.U()
            Dice.Cons(Nat.t, acc′, rec)
        end
    ])
end

function take_impl(n, l::List)
    match(n, [
        :Z => () -> Dice.Nil(Nat.t),
        :S => (npred) -> match(l, [:Cons => (hd, tl) -> Dice.Cons(Nat.t, hd, take_impl(npred, tl)), :Nil => () -> Dice.Nil(Nat.t)]),
    ])
end


function fillunit_impl(n)
    match(n, [
        :Z => () -> Dice.Nil(Unit.t),
        :S => (pred) -> Dice.Cons(Unit.t, Unit.U(), fillunit_impl(pred))
    ])
end


function fromdice(x::Nat.t)
    match(x, [
        :Z => () -> 0
        :S => (pred) -> 1 + fromdice(pred)
    ])
end

# @define mapunit "(unit -> int) -> int -> list" "(λ f n -> (map f (fill n (Unit))))"
function mapunit_impl(f, n)
    map_impl(f, fillunit_impl(n))
end

# @define scanlunit "(int -> unit -> int) -> int -> int -> list" "(λf init n -> (scanl f init (fill n (Unit))))"
function scanlunit_impl(f, init, n)
    scanl_impl(f, init, fillunit_impl(n))
end


Base.@kwdef mutable struct DiceConfig
    # fuel::Int = 0
    time_limit::Float64 = 0.
    max_depth::Union{Int, Nothing} = nothing
    state_vars::StateVars = StateVars()
end

Base.@kwdef mutable struct DiceStats
    time::Float64 = 0.
    hit_limit::Bool = false
    hit_limit_time::Bool = false
    cudd_limit_inconsistency::Float64 = 0.
end

Base.:(+)(a::DiceStats, b::DiceStats) = DiceStats(time=a.time+b.time, hit_limit=a.hit_limit || b.hit_limit, hit_limit_time=a.hit_limit_time || b.hit_limit_time, cudd_limit_inconsistency=a.cudd_limit_inconsistency + b.cudd_limit_inconsistency)


Pluck.get_time_limit(cfg::DiceConfig) = cfg.time_limit
Pluck.set_time_limit!(cfg::DiceConfig, time_limit::Float64) = (cfg.time_limit = time_limit)


mutable struct DiceState
    cfg::DiceConfig
    start_time::Float64
    depth::Int
    stats::DiceStats
    DiceState(cfg::DiceConfig) = new(cfg, 0., 0, DiceStats())
end

@inline function get_time_limit(state::DiceState)
    return state.cfg.time_limit
end
@inline function get_max_depth(state::DiceState)
    return state.cfg.max_depth
end
@inline function get_depth(state::DiceState)
    return state.depth
end
@inline function get_start_time(state::DiceState)
    return state.start_time
end
@inline function elapsed_time(state)
    return time() - get_start_time(state)
end
@inline function check_time_limit(state)
    if get_time_limit(state) > 0. && elapsed_time(state) > get_time_limit(state)
        state.stats.hit_limit = true
        state.stats.hit_limit_time = true
        return true
    else
        return false
    end
end
@inline function check_max_depth(state)
    return !isnothing(get_max_depth(state)) && get_depth(state) > get_max_depth(state)
end
@inline function exception_on_timeout(state)
    if check_time_limit(state) || check_max_depth(state)
        throw(TimeoutException())
    end
end

function dice_forward(e::String; cfg=nothing, return_state=false, kwargs...)
    !isnothing(cfg) && @assert isempty(kwargs)
    cfg = isnothing(cfg) ? DiceConfig(;kwargs...) : cfg

    state = DiceState(cfg)
    parsed = parse_expr(e)
    env = Vector{Any}()

    state.start_time = time()
    res = try
        val = traced_dice_forward(parsed, env, state)
        pr(val; time_limit=get_time_limit(state), time_start=get_start_time(state))
    catch e
        if e isa TimeoutException || e isa Dice.DiceTimeoutException
            state.stats.hit_limit = true
            state.stats.hit_limit_time = true
            res = pr(Unit.U())

            # check that we actually hit the time limit – especially important for the DiceTimeoutException
            # @assert get_time_limit(state) - elapsed_time(state) < 0.010 "expected to hit time limit within 10ms, got $(elapsed_time(state)) when limit was $(get_time_limit(state)) for $(parsed) with fuel $(state.cfg.state_vars.fuel) and e.c.time_limit=$(e.c.time_limit), time-e.c.time_start=$(time()-e.c.time_start), e.c.cudd_limit=$(e.c.cudd_limit) elapsed=$(Dice.Cudd_ReadElapsedTime(e.c.mgr)) start=$(Dice.Cudd_ReadStartTime(e.c.mgr)) limit=$(Dice.Cudd_ReadTimeLimit(e.c.mgr)) cudd_limit_after=$(Dice.set_cudd_limit(e.c))" # 5ms wiggle room, though expect its more like 1ms


            if get_time_limit(state) - elapsed_time(state) > 0.010
                # println("hit time limit inconsitency with $(get_time_limit(state)) - $(elapsed_time(state)) > 0.010")
                state.stats.cudd_limit_inconsistency = get_time_limit(state) - elapsed_time(state)
            end
            
            # if e isa Dice.DiceTimeoutException
            #     # 
            # end

            # check_time_limit(state) # to make sure .hit_limit is set even if we hit the time limit during pr()
            # @assert state.stats.hit_limit
            res
        elseif e isa StackOverflowError
            # println("Stack overflow from: ", parsed)
            # println()
            state.stats.hit_limit = true
            res = pr(Unit.U())
        else
            rethrow()
        end
    end
    
    check_time_limit(state) # to make sure .hit_limit is set even if we hit the time limit during pr()

    state.stats.time = elapsed_time(state)

    return_state && return res, state
    return res
end

struct TimeoutException <: Exception end

function traced_dice_forward(e::PExpr, env::Vector{Any}, state::DiceState)
    # @show e
    state.depth += 1
    exception_on_timeout(state)
    res = dice_forward(e, env, state)
    exception_on_timeout(state)
    state.depth -= 1
    return res
end



function dice_forward(e::App, env::Vector{Any}, state::DiceState)
    f = traced_dice_forward(e.f, env, state)
    # state.stats.hit_limit && return Unit.U()
    x = traced_dice_forward(e.x, env, state)
    # state.stats.hit_limit && return Unit.U()
    f(x)
end

function eval_dice_forward(expr, input=true, output=true; equality_fn="==", warmstart_time_limit=0.05, kwargs...)
    # if autofuel && !haskey(kwargs, :fuel)
    #     kwargs = (;kwargs..., fuel=maximum(from_value(output); init=0) + 1)
    # end

    expr = io_equality_expr(expr, [input], output; equality_fn)
    # @show expr
    dice_forward(expr; time_limit=warmstart_time_limit, kwargs...) # warmstart
    time = (@timed ((res, state) = dice_forward(expr; return_state=true, kwargs...))).time
    # @show res
    loglikelihood = log(Pluck.get_true_result(res))
    # @show loglikelihood, state.stats.hit_limit
    Dict("time" => time, "loglikelihood" => loglikelihood, "hit_limit" => state.stats.hit_limit)
end


dice_defs::Dict{Symbol, Function} = Dict()

dice_defs[:(==)] = state -> x -> y -> (x == y)
dice_defs[:+] = state -> x -> y -> (x + y)
dice_defs[:-] = state -> x -> y -> (x - y)
dice_defs[:iseven] = state -> x -> iseven(x)
dice_defs[:>] = state -> x -> y -> (x > y)
# dice_defs[:geom] = state -> p -> geom(state.cfg.fuel; p)
dice_defs[:geom_get_fuel] = state -> p -> geom(state.cfg.state_vars.fuel-1; p)


# dice_defs[:geom_fuel] = state -> p -> fuel -> geom(fromdice(fuel); p)


# dice_defs[:geom_fuel] = state -> p -> fuel -> geom(fromdice(fuel); p)
dice_defs[:map] = state -> f -> xs -> map_impl(f, xs)
dice_defs[:mapunit] = state -> f -> n -> mapunit_impl(f, n)
dice_defs[:scanl] = state -> f -> init -> xs -> scanl_impl(f, init, xs)
dice_defs[:scanlunit] = state -> f -> init -> n -> scanlunit_impl(f, init, n)
dice_defs[:take] = state -> n -> xs -> take_impl(n, xs)
# dice_defs[:randnat] = state -> geom(state.cfg.fuel; p=0.5)


function dice_forward(e::Defined, env::Vector{Any}, state::DiceState)
    if haskey(dice_defs, e.name)
        dice_defs[e.name](state)
    else
        traced_dice_forward(DEFINITIONS[e.name].expr, Any[], state)
    end
end

function dice_forward(e::PrimOp, env::Vector{Any}, state::DiceState)
    dice_prim_forward(e.op, e.args, env, state)
end

function dice_prim_forward(e::FlipOp, args::Vector{PExpr}, env::Vector{Any}, state::DiceState)
    p = traced_dice_forward(args[1], env, state)
    flip(p)
end

function dice_prim_forward(op::GetConfig, args, env::Vector{Any}, state::DiceState)
    sym = traced_dice_forward(args[1], env, state)
    getfield(state.cfg.state_vars, sym)
end


# function dice_prim_forward(e::ConstructorEqOp, args::Vector{Any}, env::Vector{Any}, state::DiceState)

# end

function dice_forward(e::CaseOf, env::Vector{Any}, state::DiceState)
    scrutinee = traced_dice_forward(e.scrutinee, env, state)
    if isa(scrutinee, Dice.AnyBool)
        return @dice_ite if scrutinee; traced_dice_forward(e.cases[:True], env, state); else; traced_dice_forward(e.cases[:False], env, state); end
    end
    match(scrutinee,[
        dice_constructors[constructor] => uncurry(traced_dice_forward(e.cases[constructor], env, state))
        for constructor in e.constructors
    ])
end

# take a function `f` thats is called like f(x)(y)(z) and return a function f(x,y,z)
# – also works if f is a constant and args will be empty
function uncurry(f)
    (args...) -> begin
        for arg in args
            f = f(arg)
        end
        f
    end
end

dice_constructors::Dict{Symbol, Symbol} = Dict()
dice_constructors[:Nil] = :Nil
dice_constructors[:Cons] = :Cons
dice_constructors[:S] = :S
dice_constructors[:O] = :Z
dice_constructors[:Unit] = :Unit
dice_constructors[:True] = :True
dice_constructors[:False] = :False


function dice_forward(e::Abs, env::Vector{Any}, state::DiceState)
    x -> begin
        new_env = copy(env)
        pushfirst!(new_env, x)
        traced_dice_forward(e.body, new_env, state)
    end
end

function dice_forward(e::Pluck.Var, env::Vector{Any}, state::DiceState)
    env[e.idx]
end



function dice_forward(e::Construct, env::Vector{Any}, state::DiceState)
    args = [traced_dice_forward(arg, env, state) for arg in e.args]
    # state.stats.hit_limit && return Unit.U()
    if e.constructor === :Nil
        return Dice.Nil(Nat.t)
    elseif e.constructor === :Cons
        # TODO for now Construct can only produce Nat lists
        return Dice.Cons(Nat.t, args[1], args[2])
    elseif e.constructor === :S
        return Nat.S(args[1])
    elseif e.constructor === :O
        return Nat.Z()
    elseif e.constructor === :Unit
        return Unit.U()
    elseif e.constructor === :True
        return true
    elseif e.constructor === :False
        return false
    else
        throw("unimplemented constructor: $(e.constructor)")
    end
end


function dice_forward(e::ConstReal, env::Vector{Any}, state::DiceState)
    return e.val
end
function dice_forward(e::ConstSymbol, env::Vector{Any}, state::DiceState)
    return e.name
end





function Pluck.io_constrain(expr, io, cfg::DiceConfig)
    expr = io_equality_expr(expr, io.inputs, io.output; equality_fn = "==")
    res, eval_state = dice_forward(expr; cfg, return_state = true)
    # @show res
    p = Pluck.get_true_result(res) # could alternatively bdd_normalize this btw
    # @show p
    return Pluck.IOConstrainResult(log(p), eval_state.stats)
    # return log(p), eval_state
end