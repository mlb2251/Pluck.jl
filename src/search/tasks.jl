export PTask,
    IOExample,
    io_logprob,
    task_logprob,
    task_constrain,
    io_constrain,
    load_tasks,
    filter_tasks,
    make_list_from_julia_list

struct IOExample
    inputs::Vector{Value}
    output::Value
end
Base.:(==)(x::IOExample, y::IOExample) = x.inputs == y.inputs && x.output == y.output

function Base.hash(x::IOExample, h::UInt)
    hash((x.inputs, x.output), h)
end



# parses from normal vectors to scheme lists
# parse_io(inputs, output) = !adt_mode() ? IOExample([scm_list(i) for i in inputs], scm_list(output)) : IOExample([to_value(i) for i in inputs], to_value(output))
parse_io(inputs, output) = IOExample([to_value(i) for i in inputs], to_value(output))
# parse_io(inputs, output) = IOExample([to_snoc(i) for i in inputs], to_snoc(output))


mutable struct PTask
    name::Symbol
    type::PType
    solution::Union{Nothing, PExpr}
    ios::Vector{IOExample}
end

PTask(name::Symbol, solution::String, type::String, ios) =
    PTask(name, parse_expr(solution), parse_type(type), ios)
function PTask(name::Symbol, solution::PExpr, type::PType, ios)
    # for ex in ios[2:end]
    #     @assert Arrow([type_of_val(i) for i in ex.inputs], type_of_val(ex.output)) == type
    # end
    name = Symbol(replace(string(name), " " => "_"))
    task = PTask(name, type, solution, ios)
    if solution !== nothing
        # @show solution
        @assert exp(task_constrain(solution, task)) ≈ 1.0 "non-1.0 probability for solution $solution to task $(task.name)"
    end
    task
end


# "name": "sort-and-deduplicate",
# "request": "(list int) -> (list int)",
# "examples": 

getname_default(json) = json["name"]
gettype_default(json) =
    if haskey(json, "type")
        json["type"]
    else
        json["request"]
    end
getsolution_default(json) =
    if haskey(json, "solution")
        json["solution"]
    else
        nothing
    end
getios_default(json) =
    if haskey(json, "ios")
        json["ios"]
    else
        json["examples"]
    end
function skip_default(json, getios)
    for (i, o) in getios(json)
        if out_of_range(o) || any(i -> out_of_range(i), i)
            return true
        end
    end
    false
end

function load_tasks(
    file::String,
    solutions = Dict();
    skip = skip_default,
    getname = getname_default,
    gettype = gettype_default,
    getsolution = getsolution_default,
    getios = getios_default,
)
    json = open(file) do f
        JSON.parse(f)
    end

    if !(json isa Vector)
        json = [json]
    end

    tasks = PTask[]
    for json_task in json
        if skip(json_task, getios)
            println("skipping $(getname(json_task)): out of range examples")
            continue
        end
        push!(
            tasks,
            from_json(
                PTask,
                json_task;
                getname = getname,
                gettype = gettype,
                getsolution = getsolution,
                getios = getios,
            ),
        )
    end

    for task in tasks
        if isnothing(task.solution) && haskey(solutions, task.name)
            task.solution = solutions[task.name]
        end
    end
    tasks
end

function json_value(v)
    replace(string(from_value(v)), "Any" => "")
end

function JSON.lower(x::PTask)
    Dict(
        :name => string(x.name),
        :type => string(x.type),
        :solution => x.solution === nothing ? nothing : string(x.solution),
        :ios =>
            [[[json_value(i) for i in ex.inputs], json_value(ex.output)] for ex in x.ios],
    )
end


function Base.show(io::IO, ex::IOExample)
    for i in ex.inputs
        print(io, i, " -> ")
    end
    print(io, ex.output)
end

function Base.show(io::IO, task::PTask)
    if !isnothing(task.solution)
        print(io, task.name, " = ", task.solution, " :: ", task.type)
    else
        print(io, task.name, " :: ", task.type)
    end
end

# function io_logprob(expr, io)
#     @assert trace_depth == 0
#     bounded_evaluate_logprob(expr, io.inputs, io.output)
# end

# function task_logprob(expr, task)
#     logprobs = io_logprob.(Ref(expr), task.ios)
#     if any(isnothing, logprobs)
#         return nothing
#     end
#     sum(logprobs)
# end

function io_logprob(expr, io)
    @assert trace_depth == 0
    bounded_evaluate_logprob(expr, io.inputs, io.output)
end

function io_constrain(expr, io, eval_state = nothing)
    (spn, eval_state) = constrain(expr, io.inputs, io.output, eval_state)
    w = weight(eval_state.spn_hash, spn)
    return w, eval_state
end

function make_list_from_julia_list(l)
    if isempty(l)
        return "(Nil)"
    else
        return "(Cons $(l[1]) $(make_list_from_julia_list(l[2:end])))"
    end
end


function task_constrain(expr, task, eval_state = nothing)
    return TaskConstrain(task, eval_state)(expr)
end

function filter_tasks(tasks; verbose = false, N = 3)
    tasks = filter(tasks) do task
        ty = string(task.type)
        ty = replace(
            ty,
            "(list int)" => "list",
            # "(list bool)" => "list",
            "(list (list int))" => "list",
        )
        task.type = parse_type(ty)

        # if isnothing(task.solution)
        #     verbose && println("skipping $(task.name): no solution")
        #     return false
        # end
        filter!(task.ios) do io
            !out_of_range(io.output) && !any(i -> out_of_range(i), io.inputs)
        end
        unique!(task.ios)
        if length(task.ios) < N
            verbose && println("skipping $(task.name): not enough in-range examples")
            return false
        end

        task.ios = task.ios[1:N] # only look at first 3 io examples

        verbose && !isnothing(task.solution) && @show task.solution
        if !isnothing(task.solution) &&
           !isapprox(task_constrain(task.solution, task)[1], 0.0)
            verbose && printstyled("skipping $(task.name): bad solution\n"; color = :red)
        end

        return true
    end
    sort!(tasks, by = t -> length(string(t.solution)))
    verbose && println("accepted $(length(tasks)) tasks")
    tasks
end
