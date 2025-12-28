
function pluck_error(state, msg)
    printstyled("Pluck Error from $(typeof(state)): ", color=:red)
    println(msg)

    if !isempty(state.stacktrace)
        print_stacktrace(state)
    else
        println("Compile with stacktrace=true to see the full Pluck stacktrace")
    end

    println()
    throw(PluckError(state, msg))
end


struct PluckError <: Exception
    state
    msg::String
end

function print_stacktrace(state)
    println("Stacktrace:")
    frame = 1

    for (i, e) in enumerate(reverse(state.stacktrace))
        ty = typeof(e).parameters[1]
        if ty == Abs || ty == Defined || i == 1 || i == length(state.stacktrace)
            print("  [$frame] ")
            if ty == Defined
                body = Pluck.lookup(e.head.name).expr
                print("$e : $body")
            else
                print("$e")
            end
            println()
            frame += 1
        end
    end
end