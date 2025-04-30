export SubExpr,
    subexpr,
    subexpr!,
    undo_subexpr!,
    subexpr_inner!,
    IterDescendants,
    descendants_inplace,
    descendants_copied,
    same_expr,
    search_step,
    descendants_untyped

"""
Information about a subexpression of another expression
"""
mutable struct SubExpr
    child::PExpr
    type::PType # of child
    env::Vector{PType} # of child
    env_names::Vector{Symbol} # of child
    path::Vector{Int} # to child
end

Base.copy(se::SubExpr) =
    SubExpr(se.child, se.type, copy(se.env), copy(se.env_names), copy(se.path))
SubExpr(e::PExpr, t::PType, env) = SubExpr(e, t, env, fill(:noname, length(env)), Int[])
SubExpr(e::String, t::String, env) = SubExpr(parse_expr(e), parse_type(t), env)

"""
modifies `se` in place to be the `i`th child of `se`.
Note that if `se` is an Abs, it will descend through all
the whole chain of Abs.
"""
# subexpr_inner!(e::PExpr, se::SubExpr, i::Int) = error("not implemented")

function subexpr_inner!(::Abs, se::SubExpr, i::Int)
    insert!(se.env, 1, arg_types(se.type)[1])
    insert!(se.env_names, 1, se.child.name)
    se.type = getchildtype(se.child, i, se.type, se.env)
    se.child = getchild(se.child, i)
    se
end

function subexpr_inner!(::If, se::SubExpr, i::Int)
    se.type = getchildtype(se.child, i, se.type, se.env)
    se.child = getchild(se.child, i)
    se
end

function subexpr_inner!(::Construct, se::SubExpr, i::Int)
    se.type = getchildtype(se.child, i, se.type, se.env)
    se.child = getchild(se.child, i)
    se
end

function subexpr_inner!(::CaseOf, se::SubExpr, i::Int)
    se.type = getchildtype(se.child, i, se.type, se.env)
    se.child = getchild(se.child, i)
    # note that we don't descend pass the lambdas of the branches
    # just as we don't descend past the lambda of higher order args
    se
end


function subexpr_inner!(::App, se::SubExpr, i::Int)
    se.type = getchildtype(se.child, i, se.type, se.env)
    se.child = getchild(se.child, i)
    se
end

function subexpr_inner!(y::Y, se::SubExpr, i::Int)
    se.type = getchildtype(se.child, i, se.type, se.env)
    se.child = getchild(se.child, i)
    se
end

function subexpr_inner!(::PrimOp, se::SubExpr, i::Int)
    se.type = getchildtype(se.child, i, se.type, se.env)
    se.child = getchild(se.child, i)
    se
end

function subexpr!(se::SubExpr, i::Int)
    backtrack = (se.child, se.type, length(se.env))
    subexpr_inner!(se.child, se, i) # "e" is just for dispatch ugh
    push!(se.path, i)
    backtrack
end

function subexpr!(se::SubExpr, path::Vector{Int})
    backtrack = (se.child, se.type, length(se.env))
    for i in path
        subexpr!(se, i)
    end
    backtrack
end

function undo_subexpr!(se::SubExpr, backtrack)
    se.child, se.type, env_len = backtrack
    while env_len < length(se.env)
        deleteat!(se.env, 1)
        deleteat!(se.env_names, 1)
    end
    pop!(se.path)
    se
end



mutable struct ChildrenIter
    e::PExpr
end
Base.length(iter::ChildrenIter) = num_children(iter.e)
iter_children(e::PExpr) = ChildrenIter(e)

function Base.iterate(iter::ChildrenIter, state = 1)
    if state > num_children(iter.e)
        return nothing
    end
    (getchild(iter.e, state), state + 1)
end



mutable struct IterDescendants{F}
    se::SubExpr
    allow_descend::F
end

Base.IteratorSize(::Type{IterDescendants}) = Base.SizeUnknown()

"""
takes an expr `e` 
"""
descendants_inplace(se::SubExpr, allow_descend = x -> true) =
    Iterators.flatten(((se,), IterDescendants(copy(se), allow_descend)))
descendants_inplace(e::PExpr, t, env, allow_descend = x -> true) =
    descendants_inplace(SubExpr(e, t, env), allow_descend)

descendants_copied(se) = (copy(se) for se in descendants_inplace(se))
descendants_copied(e::PExpr, t, env) = descendants_copied(SubExpr(e, t, env))


const BacktrackData = Tuple{PExpr, PType, Int}

struct IterState
    se::SubExpr
    stack::Vector{BacktrackData}
end

function Base.iterate(
    iter::IterDescendants{F},
    state = IterState(iter.se, Vector{Tuple{PExpr, PType}}[]),
) where {F}
    # invariant: each time iterate it called, the last thing we yielded
    # was state.se. That means the next thing to do is yield any children it has

    i = 1
    while !haschild(state.se.child, i) || !iter.allow_descend(state.se)
        if isempty(state.stack)
            return nothing
        end
        # backtrack
        i = state.se.path[end] + 1
        undo_subexpr!(state.se, pop!(state.stack))
    end

    backtrack = subexpr!(state.se, i) # this will push to the path for us
    push!(state.stack, backtrack)
    return (state.se, state)
end
mutable struct UntypedIterDescendants{F}
    e::PExpr
    path::Vector{Int}
    allow_descend::F
end

Base.IteratorSize(::Type{UntypedIterDescendants}) = Base.SizeUnknown()

"""
like `descendants_inplace` but for untyped expressions
"""
descendants_untyped(e::PExpr, path::Vector{Int} = Int[], allow_descend = x -> true) =
    Iterators.flatten((((e,path),), UntypedIterDescendants(copy(e), copy(path), allow_descend)))

mutable struct UntypedIterState
    e::PExpr
    path::Vector{Int}
    stack::Vector{PExpr}
end

function Base.iterate(
    iter::UntypedIterDescendants{F},
    state = UntypedIterState(iter.e, iter.path, PExpr[]),
) where {F}
    # invariant: each time iterate it called, the last thing we yielded
    # was (state.e, state.path). That means the next thing to do is yield any children it has

    i = 1
    while !haschild(state.e, i) || !iter.allow_descend(state.e)
        isempty(state.stack) && return nothing
        # state.e has no children! Lets backtrack, setting both state.e and state.path
        # to those of our parent, and setting `i` to our next sibling
        state.e = pop!(state.stack)
        i = pop!(state.path) + 1
    end
    # we have a child to yield
    push!(state.path, i)
    push!(state.stack, state.e)
    state.e = getchild(state.e, i)
    return ((state.e, copy(state.path)), state)
end


Base.show(io::IO, se::SubExpr) =
    print(io, "SubExpr(", se.child, "::", se.type, " @ ", se.path, " w ", se.env, ")")
