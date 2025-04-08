export Closure,
    YClosure,
    List,
    Nil,
    Cons,
    int_nan,
    scm_list,
    out_of_range,
    scm_nat,
    peano_str,
    peano,
    Thunk,
    to_snoc

export to_value, from_value, string_repr

# result of evaluating a lambda. Takes 1 argument.
mutable struct Closure
    expr::PExpr
    env::Vector{Any}
    # linear :: Bool

    function Closure(expr, env)
        new(expr, env)
    end
end

function make_self_loop(body, env)
    new_env = copy(env)
    pushfirst!(new_env, missing) # placeholder for the self-reference
    closure = Closure(body, new_env)
    # pushfirst!(closure.env, missing) # placeholder for the self-reference
    # now put in the actual self reference – if it was used (ie set to Nothing)
    if ismissing(closure.env[1])
        closure.env[1] = closure
    end
    closure
end

is_self_loop(x::Closure) = !isempty(x.env) && x.env[1] === x

function Base.:(==)(x::Closure, y::Closure)
    x.expr == y.expr || return false
    is_self_loop(x) && is_self_loop(y) && return @views x.env[2:end] == y.env[2:end]
    x.env == y.env
end
function Base.hash(x::Closure, h::UInt)
    h = hash(x.expr, h)
    # start = is_self_loop(x) ? 2 : 1
    # for i in start:length(x.env)
    h = hash(length(x.env), h) # bleh having trouble stopping the self loops
    # for v in x.env
    #     h = v isa Closure ? hash(:closure,h) :
    #     v isa Thunk ? hash(v.expr,h) : hash(v, h)
    # end
    return h
end

function Base.show(io::IO, c::Closure)
    print(io, "Closure((λ ", c.expr, "), env=[#arg")
    for v in c.env
        if v === c
            print(io, ", [recursive reference to this closure]")
        else
            print(io, ", ", v)
        end
    end
    print(io, ")")
end

function JSON.lower(x::Closure)
    is_ycombinator = !isempty(x.env) && x.env[1] === x
    env =
        is_ycombinator ? vcat(["[recursive reference to this closure]"], x.env[2:end]) :
        x.env
    Dict(
        "type" => "Closure",
        "expr" => x.expr,
        "env" => [var_is_free(x.expr, i + 1) ? v : "unused" for (i, v) in enumerate(env)], # +1 bc of shifting when prepending the closure arg
    )
end

# A lazily evaluated expression. Takes zero arguments. May yield more than one
# actual value, so this is not itself a value – it's a construct that can only
# appear within an env or under a constructor, and will be enumerated or logprob'd 
# when pulled from the env or constructor as necessary.
# Currently not stateful: independent uses of a variable that points to the thunk,
# e.g., are not tied to take the same value.
struct Thunk
    expr::PExpr
    env::Vector{Any}
    callstack::Vector{Symbol} # if empty: not memoizing this expression.
    name::Symbol
    memoizing::Bool
    function Thunk(expr::PExpr, env::Vector, callstack, name, memoizing)
        # remove a layer of thunk if the expr is a var pointing to a thunk
        # (this helps caching and makes things less convoluted)
        if expr isa Var && env[expr.idx] isa Thunk
            return env[expr.idx]
        end
        new(expr, env, copy(callstack), name, memoizing)
    end
end

Base.:(==)(x::Thunk, y::Thunk) =
    x.expr == y.expr &&
    x.callstack == y.callstack &&
    x.env == y.env &&
    x.name == y.name &&
    x.memoizing == y.memoizing
# dont hash the env just its length for speed
Base.hash(x::Thunk, h::UInt) =
    hash(x.expr, hash(length(x.env), hash(x.callstack, hash(x.name, hash(x.memoizing, h)))))

JSON.lower(x::Thunk) = Dict(
    "type" => "Thunk",
    "expr" => x.expr,
    "env" => [var_is_free(x.expr, i) ? v : "unused" for (i, v) in enumerate(x.env)],
    "callstack" => x.callstack,
    "name" => x.name,
    "memoizing" => x.memoizing,
)


abstract type List end
struct Nil <: List end
struct Cons <: List
    head::Any
    tail::List
end


const int_nan::Int = 500000
const int_range::UnitRange{Int} = 0:9
const int_range_and_nan::Vector{Int} = [int_range; int_nan]

# identity for x in 0:9 or whatever the defined range of ints is, and returns the int_nan constant otherwise
nan_if_oob(x) = x in int_range ? x : int_nan
assert_valid_int(x) = @assert x in int_range || x == int_nan "invalid int: $x"

abstract type Nat end
struct Zero <: Nat end
struct Succ <: Nat
    pred::Any # can be a thunk
end


# this is more of a generic "parse into value" now lol
scm_list(x) = x
scm_list(vals::Vector) =
    isempty(vals) ? Nil() : Cons(scm_list(vals[1]), scm_list(vals[2:end]))

function scm_nat(n)
    if n == 0
        return Pluck.Zero()
    else
        return Pluck.Succ(scm_nat(n - 1))
    end
end


Base.show(io::IO, x::Nil) = print(io, "[]")
Base.show(io::IO, x::Cons) = begin
    print(io, "[")
    print(io, x.head)
    while x.tail isa Cons
        print(io, ", ")
        print(io, x.tail.head)
        x = x.tail
    end
    # @assert x.tail isa Nil x.tail
    print(io, x.tail, "]")
end

type_of_val(::Int) = BaseType(:int)
type_of_val(::Float64) = BaseType(:float)
type_of_val(::Bool) = BaseType(:bool)
type_of_val(::Vector) = BaseType(:list)
type_of_val(::Cons) = BaseType(:list)
type_of_val(::Nil) = BaseType(:list)





# mutable struct Constructor
#     type::Symbol
#     constructor::Symbol
#     args::Vector{Symbol}
# end
# Constructor(name) = Constructor(name, Symbol[])
# Base.(==)(x::Constructor, y::Constructor) = x.name === y.name

# (x::Constructor)(args...) = Value(x.name, args)


# const natS = Constructor(:S, [:nat])
# const natO = Constructor(:O)
# const nat = SumProductType(:nat, [natO, natS])

# const listNil = Constructor(:Nil)
# const listCons = Constructor(:Cons, [:nat, :list])
# const list = SumProductType(:list, [listNil, listCons])



# const lookup_constructor = Dict{Symbol, Constructor}(
#     :S => natS,
#     :O => natO,
#     :Nil => listNil,
#     :Cons => listCons,
# )
# const lookup_type = Dict{Symbol, SumProductType}(
#     :nat => nat,
#     :list => list,
# )

struct Value
    spt::SumProductType
    constructor::Symbol
    args::Vector{Any}
end
Value(type, constructor) = Value(type, constructor, [])
Base.hash(x::Value, h::UInt) = hash(x.spt.name, hash(x.constructor, hash(x.args, h)))
# Base.hash(x::Value, h::UInt) = hash(x.spt,hash(x.constructor, h))
Base.:(==)(x::Value, y::Value) =
    x.spt.name === y.spt.name && x.constructor === y.constructor && x.args == y.args

(spt::SumProductType)(constructor::Symbol)::Value = Value(spt, constructor, [])
(spt::SumProductType)(constructor::Symbol, args...)::Value =
    Value(spt, constructor, collect(args))


function to_value(n::Int)
    @assert n >= 0
    n == 0 && return nat(:O)
    nat(:S, to_value(n - 1))
end

to_value(u::Tuple{}) = unit(:Unit)
to_value(x::Bool) = x ? bool(:True) : bool(:False)
to_value(x::Value) = x

function to_value(xs::Vector)
    isempty(xs) && return list(:Nil)
    return list(:Cons, to_value(xs[1]), to_value(xs[2:end]))
end


digit_values::Vector{Value} = Value[to_value(i) for i ∈ 0:9]
TRUE_VALUE::Value = to_value(true) # careful - wont update
FALSE_VALUE::Value = to_value(false) # careful - wont update
function make_digits_values()
    global digit_values
    digit_values = Value[to_value(i) for i ∈ 0:9]
end



from_value(x) = x
function from_value(x::Value)
    if x.constructor === :True
        return true
    elseif x.constructor === :False
        return false
    elseif x.constructor == :O
        return 0
    elseif x.constructor == :S
        (x.args[1] isa Thunk || x.args[1] isa LazyEnumeratorThunk || x.args[1] isa BDDThunk) && return x
        return 1 + from_value(x.args[1])
    elseif x.constructor == :Nil || x.constructor == :SNil
        return []
    elseif x.constructor == :Cons
        (x.args[1] isa Thunk || x.args[2] isa Thunk || x.args[1] isa BDDThunk || x.args[2] isa BDDThunk) && return x
        (x.args[1] isa Nothing || x.args[2] isa Nothing) && return nothing # aaack my temp fix for neg nats
        return [from_value(x.args[1]); from_value(x.args[2])]
    elseif x.constructor == :Snoc
        (x.args[1] isa Thunk || x.args[2] isa Thunk || x.args[1] isa BDDThunk || x.args[2] isa BDDThunk) && return x
        (x.args[1] isa Nothing || x.args[2] isa Nothing) && return nothing # aaack my temp fix for neg nats
        head_list = from_value(x.args[1])
        tail_elem = from_value(x.args[2])
        return vcat(head_list, [tail_elem])
    end
    return x
end


peano_str(n) = foldr((_, acc) -> "(S " * acc * ")", 1:n; init = "(O)")

convert(::Type{Value}, x) = value(x)
function Base.show(io::IO, x::Value)
    (x.constructor === :Nil || x.constructor === :SNil) && return print(io, "[]") # prettier than "Any[]"
    v = from_value(x)
    if !(v isa Value)
        print(io, v)
    else
        print(io, "(", x.constructor)
        for arg in x.args
            print(io, " ")
            print(io, arg)
        end
        print(io, ")")
    end
end

function JSON.lower(x::Value)
    v = from_value(x)
    !(v isa Value) && return string(v)
    Dict("type" => "Value", "constructor" => x.constructor, "args" => x.args)
end


function string_repr(x::Value)
    res = "(" * string(x.constructor)
    for arg in x.args
        res *= " " * string_repr(arg)
    end
    return res * ")"
end


out_of_range(x::Int) = x < 0
out_of_range(x::Cons) = out_of_range(x.head) || out_of_range(x.tail)
out_of_range(x::Nil) = false
out_of_range(x::Value) = out_of_range(from_value(x))
out_of_range(x::Vector) = any(out_of_range, x)
out_of_range(x::Bool) = false
