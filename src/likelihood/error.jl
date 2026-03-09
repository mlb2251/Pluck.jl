function pluck_error(state, msg)
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
        print(io, "  [$frame] ")
        if ty == Defined
            body = Pluck.DEFINITIONS[e.head.name].expr
            print(io, "$e : $body")
        else
            print(io, "$e")
        end
        println(io)
        frame += 1
    end
end