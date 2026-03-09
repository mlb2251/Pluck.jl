function pluck_error(state, msg)
    # printstyled("Pluck Error from $(typeof(state)): ", color=:red)
    # println(msg)

    # if !isempty(state.stacktrace)
    #     print_stacktrace(state)
    # else
    #     println("Compile with stacktrace=true to see the full Pluck stacktrace")
    # end

    # println()
    throw(PluckError(state, msg))
end


struct PluckError <: Exception
    state
    msg::String
end

function Base.showerror(io::IO, e::PluckError)
    print(io, "PluckError in $(typeof(e.state)): $(e.msg)\n")
    print_stacktrace(io, e.state)
    println(io)
end

function print_stacktrace(io::IO, state)
    frame = 1

    for (i, e) in enumerate(reverse(state.stacktrace))
        ty = typeof(e).parameters[1]
        # if ty == Abs || ty == Defined || i == 1 || i == length(state.stacktrace)
        print(io, "  [$frame] ")
        if ty == Defined
            body = Pluck.DEFINITIONS[e.head.name].expr
            print(io, "$e : $body")
        else
            print(io, "$e")
        end
        println(io)
        frame += 1
        # end
    end
end