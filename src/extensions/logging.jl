const VERBOSE = Ref{Bool}(false)
setlog!(verbose::Bool) = (VERBOSE[] = verbose)
getlog()::Bool = VERBOSE[]

function pretty_callstack(callstack, strict_order_index=nothing)
    if !isnothing(strict_order_index)
        callstack = vcat(callstack, strict_order_index)
    end
    return "." *join(callstack, ".")
end

function print_enter(expr, env, state)
    getlog() || return
    cs = pretty_callstack(state.callstack)
    printstyled("$cs $expr :: $(typeof(expr))\n", color=:yellow)
end

function pretty_worlds(worlds::Vector; weights=false)
    res = "["
    for (i, (val, bdd)) in enumerate(worlds)
        res *= string(val)
        weights && (res *= " (P=" * @sprintf("%.1e", bdd_wmc(bdd)) * ")")
        i < length(worlds) && (res *= ", ")
    end
    return res * "]"
end

function pretty_result(result; weights=false)
    if result isa Vector
        return "-> " * pretty_worlds(result; weights=weights)
    else
        return "-> $result :: $(typeof(result))"
    end
end

function print_exit(expr, result, env, state)
    getlog() || return
    cs = pretty_callstack(state.callstack)
    green = "$cs $expr :: $(typeof(expr)) "
    blue = pretty_result(result; weights=true)
    printstyled(green, color=:green)
    length(green) + length(blue) > 80 && print("\n")
    printstyled(blue * "\n", color=:blue)
end


function pretty_thunk(thunk::LazyKCThunk)
    return "Thunk $(thunk.expr)"
end

function print_thunk_enter(thunk::LazyKCThunk, state)
    getlog() || return
    cs = pretty_callstack(state.callstack)
    thunk_cs = pretty_callstack(thunk.callstack, thunk.strict_order_index)
    printstyled("$cs $(pretty_thunk(thunk)) ", color=:yellow)
    printstyled("@ $thunk_cs\n", color=:magenta)
end

function print_thunk_exit(thunk::LazyKCThunk, result, state)
    getlog() || return
    cs = pretty_callstack(state.callstack)
    thunk_cs = pretty_callstack(thunk.callstack, thunk.strict_order_index)
    printstyled("$thunk_cs $(pretty_thunk(thunk)) ", color=:green)
    result = pretty_result(result; weights=true)
    printstyled(result, color=:blue)
    printstyled(" @ $cs\n", color=:magenta)
end

function print_make_thunk(thunk::LazyKCThunk, state)
    getlog() || return
    cs = pretty_callstack(thunk.callstack, thunk.strict_order_index)
    printstyled("$cs Make $(pretty_thunk(thunk))\n", color=:cyan)
end