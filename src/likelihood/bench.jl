export ConstrainTask,
    ConstrainTasks,
    ConstrainTaskResult,
    ConstrainTasksResult,
    from_json,
    eval_tasks,
    num_exprs

using BenchmarkTools
mutable struct ConstrainTask
    task::PTask
    exprs::Vector{PExpr}
end

mutable struct ConstrainTasks
    tasks::Vector{ConstrainTask}
    name::Symbol
end

# ConstrainTask(g::Graph) = ConstrainTask(g.task, [g.expr.child for g in nodes(g)])
# ConstrainTasks(g::Graph, name) = ConstrainTasks([ConstrainTask(g)], name)
# ConstrainTasks(g::Graph) = ConstrainTasks(g, g.task.name)
# ConstrainTasks(gs::Vector{Graph}, name) = ConstrainTasks(ConstrainTask.(gs), name)

struct ConstrainTaskResult
    stats
    weights::Vector{Float64}
    stats_total
    weight_total::Float64
end
function ConstrainTaskResult(stats, weights::Vector{Float64})
    stats_total = merge_stats(stats)
    weight_total = sum(weights)
    ConstrainTaskResult(stats, weights, stats_total, weight_total)
end

struct ConstrainTasksResult
    config
    stats_total
    weight_total::Float64
    results::Vector{ConstrainTaskResult}
end
function ConstrainTasksResult(config, results::Vector{ConstrainTaskResult})
    stats_total = merge_stats([result.stats_total for result in results])
    weight_total = sum(result.weight_total for result in results)
    ConstrainTasksResult(config, stats_total, weight_total, results)
end

from_json(::Type{PExpr}, json::String) = parse_expr(json)
from_json(::Type{Float64}, json::Float64) = json
from_json(::Type{Int}, json::Int) = json
from_json(::Type{String}, json::String) = json
from_json(::Type{Symbol}, json::String) = Symbol(json)
from_json(::Type{Bool}, json::Bool) = json
from_json(::Type{Nothing}, json::Nothing) = json

from_json(::Type{ConstrainTasks}, json::Dict{String, Any}) =
    ConstrainTasks(from_json.(ConstrainTask, json["tasks"]), Symbol(json["name"]))

function from_json(::Type{Vector{T}}, json::Vector{Any}) where {T}
    T[from_json(T, x) for x in json]
end

function from_json(
    ::Type{PTask},
    json_task::Dict{String, Any};
    getname = getname_default,
    gettype = gettype_default,
    getsolution = getsolution_default,
    getios = getios_default,
)
    PTask(
        Symbol(getname(json_task)),
        parse_type(gettype(json_task)),
        [parse_io(io[1], io[2]) for io in getios(json_task)];
        solution=!isnothing(getsolution(json_task)) ? parse_expr(getsolution(json_task)) : nothing,
        num_train = get(json_task, "num_train", length(getios(json_task))),
    )
end

function from_json(::Type{ConstrainTask}, json::Dict{String, Any})
    ConstrainTask(from_json(PTask, json["task"]), parse_expr.(json["exprs"]))
end

function from_json(::Type{ConstrainTaskResult}, json::Dict{String, Any})
    ConstrainTaskResult(
        from_json(Vector{StatsEval}, json["stats"]),
        json["weights"],
        from_json(StatsEval, json["stats_total"]),
        json["weight_total"],
    )
end

function from_json(::Type{ConstrainTasksResult}, json::Dict{String, Any})
    ConstrainTasksResult(
        from_json(EvalConfig, json["config"]),
        from_json(StatsEval, json["stats_total"]),
        json["weight_total"],
        from_json(Vector{ConstrainTaskResult}, json["results"]),
    )
end

function from_json(::Type{EvalConfig}, json::Dict{String, Any})
    EvalConfig(; Dict(Symbol(k) => v for (k, v) in json)...)
end
function from_json(::Type{StatsEval}, json::Dict{String, Any})
    StatsEval(; Dict(Symbol(k) => v for (k, v) in json)...)
end

function eval_task(constrain_task::ConstrainTask, eval_state)::ConstrainTaskResult
    stats_task = []
    weights_task = Vector{Float64}()
    for expr in constrain_task.exprs
        weight, stats = task_constrain(expr, constrain_task.task, eval_state)
        push!(stats_task, stats)
        push!(weights_task, exp(weight))
    end
    ConstrainTaskResult(stats_task, weights_task)
end

# num_nodes(g::Graph) = length(nodes(g))

num_exprs(task::ConstrainTask) = length(task.exprs)
num_exprs(tasks::ConstrainTasks) = sum(num_exprs(task) for task in tasks.tasks)
num_exprs(result::ConstrainTaskResult) = length(result.stats)
num_exprs(result::ConstrainTasksResult) =
    sum(num_exprs(result) for result in result.results)

exprs(task::ConstrainTask) = task.exprs
exprs(tasks::ConstrainTasks) = reduce(vcat, exprs(task) for task in tasks.tasks)

stats(result::ConstrainTaskResult) = result.stats
stats(result::ConstrainTasksResult) =
    reduce(vcat, stats(result) for result in result.results)

weights(result::ConstrainTaskResult) = result.weights
weights(result::ConstrainTasksResult) =
    reduce(vcat, weights(result) for result in result.results)

zip_results(tasks, result) = zip(exprs(tasks), stats(result), weights(result))

terminating_stats(result) = collect(filter(s -> !hit_limit(s), stats(result)))
num_terminating(result) = length(terminating_stats(result))

function eval_tasks(
    constrain_tasks::ConstrainTasks,
    config;
    verbose = true,
    verbose_term = false,
    benchmark = false,
    warmstart = true,
)::ConstrainTasksResult
    verbose && print(
        "\n",
        uppercase(string(constrain_tasks.name)),
        " (",
        num_exprs(constrain_tasks),
        "): ",
    )

    # warmstart (not needed for bench mode but yes for timing mode)
    if warmstart
        eval_state = make_state(config)
        for constrain_task in constrain_tasks.tasks
            eval_task(constrain_task, eval_state)
        end
    end

    if benchmark
        bench = @benchmark begin
            eval_state = make_state($config)
            for constrain_task in $(constrain_tasks).tasks
                eval_task(constrain_task, eval_state)
            end
        end
        show_trial(stdout, bench)
    end

    results = Vector{ConstrainTaskResult}()
    eval_state = make_state(config) # need a new state separate from warmstart
    @time for constrain_task in constrain_tasks.tasks
        push!(results, eval_task(constrain_task, eval_state))
    end

    # perm = sortperm(results, by = result -> result.stats_total.time; rev = true)
    # terminating_idxs = filter!(i -> !hit_limit(results[i].stats_total), perm)
    # results = results[terminating_idxs]
    # tasks = constrain_tasks.tasks[terminating_idxs]
    # @show tasks[1]



    res = ConstrainTasksResult(eval_state.config, results)

    term_stats = terminating_stats(res)
    # dumb hacky way to handle empty when we want to support multiple types
    term_merged_stats = merge_stats(vcat(term_stats,make_state(config).stats))

    verbose_term && println(
        "TERM (",
        round(length(term_stats) / num_exprs(constrain_tasks), sigdigits = 2),
        "): ",
        round(term_merged_stats.time, sigdigits = 3),
        "s",
    )
    # show slowest



    verbose_term && println("term stats: ", term_merged_stats)
    verbose && println(res)

    res
end

Base.show(io::IO, task::ConstrainTask) =
    print(io, "ConstrainTask(", num_exprs(task), " exprs for ", task.task)
Base.show(io::IO, tasks::ConstrainTasks) =
    print(io, "ConstrainTasks(", num_exprs(tasks), " exprs for ", tasks.name)
Base.show(io::IO, res::ConstrainTaskResult) = print(
    io,
    "ConstrainTaskResult(",
    round(num_terminating(res) / num_exprs(res), sigdigits = 2),
    " P=",
    round(res.weight_total, sigdigits = 3),
    " ",
    res.stats_total,
)
Base.show(io::IO, res::ConstrainTasksResult) = print(
    io,
    "ConstrainTasksResult(",
    round(num_terminating(res) / num_exprs(res), sigdigits = 2),
    " P=",
    round(res.weight_total, sigdigits = 3),
    " ",
    res.stats_total,
)
