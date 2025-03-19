export PTask,
    IOExample,
    io_logprob,
    task_logprob,
    task_constrain,
    io_constrain,
    load_tasks,
    filter_tasks,
    io_equality_expr

struct IOExample
    inputs::Vector{Value}
    output::Value
end
Base.:(==)(x::IOExample, y::IOExample) = x.inputs == y.inputs && x.output == y.output

function Base.hash(x::IOExample, h::UInt)
    hash((x.inputs, x.output), h)
end


function parse_value(v)
    if v isa String
        return to_value(eval(Meta.parse(v)))
    else
        return to_value(v)
    end
end

# parses from normal vectors to scheme lists
# parse_io(inputs, output) = !adt_mode() ? IOExample([scm_list(i) for i in inputs], scm_list(output)) : IOExample([to_value(i) for i in inputs], to_value(output))
function parse_io(inputs, output)
    IOExample([parse_value(i) for i in inputs], parse_value(output))
end
# parse_io(inputs, output) = IOExample([to_snoc(i) for i in inputs], to_snoc(output))


mutable struct PTask
    name::Symbol
    type::PType
    solution::Union{Nothing, PExpr}
    ios::Vector{IOExample}
    num_train::Int
    definitions::Vector{String}

    function PTask(name::Symbol, type::PType, ios::Vector{IOExample}; solution=nothing, num_train=length(ios), definitions=String[])
        @assert !occursin(" ", string(name)) "task names cannot contain spaces since they're used in filenames"
        new(name, type, solution, ios, num_train, definitions)
    end
end

# PTask(name::Symbol, solution::String, type::String, ios) =
#     PTask(name, parse_expr(solution), parse_type(type), ios)
# function PTask(name::Symbol, solution::PExpr, type::PType, ios)
#     # for ex in ios[2:end]
#     #     @assert Arrow([type_of_val(i) for i in ex.inputs], type_of_val(ex.output)) == type
#     # end
#     name = Symbol(replace(string(name), " " => "_"))
#     task = PTask(name, type, solution, ios)
#     if solution !== nothing
#         # @show solution
#         @assert exp(task_constrain(solution, task)) ≈ 1.0 "non-1.0 probability for solution $solution to task $(task.name)"
#     end
#     task
# end

# autofuel is 2+ double the max output in any output list 
autofuel(output::PTask) = maximum(io -> autofuel(io.output), output.ios)
autofuel(output::Value) = autofuel(from_value(output))
function autofuel(output::Vector{Any})
    output = Int.(output)
    # max(maximum(from_value(output); init=0), length(from_value(output))) + 2
    max(maximum(output; init=0), length(output)) * 2 + 2
    # 1000
end

# function autofuel(output::Any)
#     @show typeof(output[1])
#     error("autofuel not implemented for type $(typeof(output))")
#     return 0
# end


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
        :num_train => x.num_train,
        :definitions => [string(d) for d in x.definitions],
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


function task_constrain(expr, task, eval_state = nothing)
    return TaskConstrain(task, eval_state)(expr)
end


mutable struct IOConstrainResult
    logweight::Float64
    stats
end

mutable struct TaskConstrainResult
    logweight::Float64
    stats
    ios_results::Vector{IOConstrainResult}
end

struct TaskConstrain
    task::PTask
    config
    cache::Dict{PExpr, TaskConstrainResult}
    use_cache::Bool
    temperature::Float64
    train_only::Bool
end
TaskConstrain(task, cfg; temperature = 1.0, use_cache=true, train_only=false) = TaskConstrain(task, cfg, Dict{PExpr, TaskConstrainResult}(), use_cache, temperature, train_only)
# TaskConstrain(task, eval_states::Vector{E}; temperature = 1.0) where {E} = TaskConstrain(task, eval_states, Dict{PExpr, Tuple{Float64, Any}}(), true, temperature)

JSON.lower(tc::TaskConstrain) = Dict(:task => tc.task, :temperature => tc.temperature, :cache => map(kv -> (kv[1], exp(kv[2].logweight), kv[2].stats), collect(tc.cache)))
total_time(tc::TaskConstrain) = sum(kv -> kv[2].stats.time, tc.cache; init=0.0)

(tc::TaskConstrain)(expr::String) = tc(parse_expr(expr))

function (tc::TaskConstrain)(exprs::Vector{PExpr})
    # single thread: filter to the unique exprs that are not in the cache
    worklist = unique(exprs)
    filter!(expr -> !haskey(tc.cache, expr), worklist)

    # parallel: run eval
    results = Vector{Any}(undef, length(worklist))
    launch_workers(worklist) do i_expr, worker_id, _
        # for (i,expr) in enumerate(worklist)
        i = i_expr[1]::Int
        results[i] = eval_task(i_expr[2], tc)
    end

    # single thread: add to cache
    for (expr, res) in zip(worklist, results)
        tc.cache[expr] = res
    end

    # single thread: construct output (undoing the unique!())
    res = [tc.cache[expr] for expr in exprs]
    return res
end

function (tc::TaskConstrain)(expr::PExpr; cache=true, kwargs...)
    cache ? cached_eval_task(expr, tc; kwargs...) : eval_task(expr, tc; kwargs...)
end

function cached_eval_task(expr::PExpr, tc; test=false, kwargs...)
    tc.use_cache && !test && haskey(tc.cache, expr) && return tc.cache[expr]
    res = eval_task(expr, tc; test, kwargs...)
    tc.use_cache && !test && (tc.cache[expr] = res)
    return res
end

function eval_task(expr::PExpr, tc::TaskConstrain; test=false, temperature=true)
    @assert !tc.train_only "TEMP assertion for debugging"
    test = tc.train_only ? false : test
    total = 0.0
    all_stats = []
    ios_results = IOConstrainResult[]

    ios = test ? tc.task.ios[tc.task.num_train+1:end] : tc.task.ios[1:tc.task.num_train]
    @assert !isempty(ios) "no examples to evaluate test=$test"
    # @show test
    # @show length(ios)
    string(typeof(tc.config)) == "DiceConfig" && @assert tc.config.state_vars.fuel != 0 "TEMP assertion for debugging"
    # tc.config.state_vars.fuel = autofuel(tc.task)

    original_time_limit = get_time_limit(tc.config)
    total_time_limit = original_time_limit * length(ios)
    tstart = time()

    for io in ios
        # state_vars = StateVars(;fuel=autofuel(output))
        # tc.config.state_vars.fuel = autofuel(io.output)

        # set the limit to the remaining time
        set_time_limit!(tc.config, max(0.001, total_time_limit - (time() - tstart)))

        io_res = io_constrain(expr, io, tc.config)
        total += io_res.logweight

        push!(all_stats, io_res.stats)
        push!(ios_results, io_res)
        total == -Inf && break
    end



    set_time_limit!(tc.config, original_time_limit)

    if temperature
        total /= tc.temperature
    end
    stats = merge_stats(all_stats)
    return TaskConstrainResult(total, stats, ios_results)
end

function io_equality_expr(expr, inputs, output; equality_fn = "old_list_eq")::String
    inputs = make_list_from_julia_list.(from_value.(inputs))
    output = make_list_from_julia_list(from_value(output))

    # wrap in lambdas
    for _ = 1:length(inputs)
        expr = "(λx -> $(expr))"
    end

    # now apply the inputs
    for i in reverse(inputs)
        expr = "($expr $i)"
    end

    return "($equality_fn $output $expr)"
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
