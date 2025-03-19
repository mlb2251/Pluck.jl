using Pluck

# include("../evaluation_utils.jl")
include("../../examples.jl")
include("dice.jl")


struct TaskDist
    grammar::Grammar
    input_type::String
    output_type::String
    input_dist::String
    valid_expr::Function
    valid_io::Function
end

JSON.lower(task_dist::TaskDist) = Dict(
    :grammar => string(task_dist.grammar),
    :input_type => task_dist.input_type,
    :output_type => task_dist.output_type,
    :input_dist => task_dist.input_dist,
)

function default_equality_fn(type::String)
    Dict(
        "list" => "old_list_eq",
        "unit" => "constructors_equal",
        "bool" => "constructors_equal",
        "int" => "nat_eq",
    )[type]
end

struct Dataset
    task_dist::TaskDist
    tasks::Vector{PTask}
    task_info::Vector{Dict}
    path::String
end

Dataset(task_dist) = Dataset(task_dist, [], [], joinpath(timestamp_dir(; base="out/fuzz-datasets/"), "dataset.json"))

function make_fuzzing_dataset(; N=100, M=4, E=4, task_dist=map_unit_grammar())

    input_types = PType[parse_type(task_dist.input_type)]
    output_type = parse_type(task_dist.output_type)
    # @show task_dist.grammar
    # @show task_dist.grammar.start_expr_of_type[output_type]
    start = parsed_expr(task_dist.grammar, task_dist.grammar.start_expr_of_type[output_type], output_type, input_types)

    dataset = Dataset(task_dist)

    seen = Set{String}()

    progress = ProgressBar(; total=N)
    set_description(progress, "Generating dataset")

    while length(dataset.tasks) < N
        # expr = Pluck.random(pcfg_dist, pcfg, Pluck.from_lhs_detached(start))

        # Sample expr
        size_dist = Pluck.Uniform(0, 10)
        size = Pluck.random(size_dist)
        expr = Pluck.random(Pluck.fixed_size_dist, task_dist.grammar, size, Pluck.from_lhs_detached(start))

        q_expr = Pluck.logprob(Pluck.fixed_size_dist, task_dist.grammar, size, expr) + Pluck.logprob(size_dist, size)

        # reject invalid exprs and duplicates
        !task_dist.valid_expr(string(expr)) && continue
        string(expr) in seen && continue
        push!(seen, string(expr))

        # sample input output examples
        ios = IOExample[]
        p_inputs = []
        for i in 1:M+E
            input = sample_output(task_dist.input_dist)
            # @show input
            p_input, stats = bdd_constrain(task_dist.input_dist, [to_value(nothing)], input; root_equality_fn=default_equality_fn(task_dist.input_type))
            @assert p_input > -Inf
            output = nothing
            for j in 1:20
                output = sample_output(string(expr); env=Any[input])
                !isnothing(output) && break
            end
            isnothing(output) && break
            !task_dist.valid_io(from_value(input), from_value(output)) && break
            push!(ios, IOExample(Value[input], output))
            push!(p_inputs, p_input)
        end

        length(ios) < M + E && continue # means we hit one of the break statements

        name = lpad(length(dataset.tasks), 3, '0')

        push!(dataset.tasks, PTask(Symbol(name), parse_type("$(task_dist.input_type) -> $(task_dist.output_type)"), ios; solution=expr.expr.child, num_train=M))
        push!(dataset.task_info, Dict(:size => size, :q_expr => q_expr, :p_inputs => p_inputs))
        update(progress)
    end

    # write to file
    write_out(dataset, dataset.path)
    return dataset.path
end

function make_tc(mode::Symbol; temperature=1.0, train_only=false, kwargs_of_task)

    if mode == :bdd
        return task -> TaskConstrain(task, BDDEvalStateConfig(; kwargs_of_task(task)...); temperature, train_only)
    elseif mode == :lazy
        return task -> TaskConstrain(task, LazyEnumeratorConfig(; kwargs_of_task(task)...); temperature, train_only)
    elseif mode == :strict
        return task -> TaskConstrain(task, LazyEnumeratorConfig(; strict=true, disable_traces=true, disable_cache=true, kwargs_of_task(task)...); temperature, train_only)
    elseif mode == :smc
        return task -> TaskConstrain(task, BDDEvalStateConfig(; bdd_forward_fn=bdd_forward_with_suspension, root_equality_fn="suspended_list_eq ==", kwargs_of_task(task)...); temperature, train_only)
    elseif mode == :dice
        return task -> TaskConstrain(task, DiceConfig(; kwargs_of_task(task)...); temperature, train_only)
    else
        error("Unknown mode $mode")
    end
end


function get_historical_data()
    res = Vector{Dict}()
    target_dir = "data/figure5"
    open(joinpath(target_dir, "historical_nov14.json")) do f
        data = JSON.parse(f)
        for group in data["groups"]
            if haskey(group, "gen_file") && haskey(group, "eval_file")
                task = group["config"]["task"]
                gen_file = joinpath(target_dir, group["gen_file"])
                eval_file = joinpath(target_dir, group["eval_file"])
                push!(res, Dict(:task => task, :gen_file => gen_file, :eval_file => eval_file))
            end
        end
    end
    return res
end


function figure5_left_single(mode; truncate=10, time_limit=1.0, max_depth=1000)
    more_defs()
    historical_data = get_historical_data()
    for data in historical_data
        println("Fuzzing task: ", data[:task])
        eval_file = fuzz(data[:gen_file], mode; truncate, time_limit, max_depth)
        write_figure5_left_single(mode, data[:task], eval_file)
    end
end

function write_figure5_left_single(mode, task, eval_file)
    file = "data_to_plot/figure5-left/$(mode)/$(task).json"
    mkpath(dirname(file))
    open(file, "w") do f
        JSON.print(f, Dict(:eval_file => eval_file), 2)
    end
    println("Wrote $file")
end

function figure5_right_single(mode; truncate=8, time_limit=0.05, max_depth=1000, mcmc_steps=500)
    more_defs()
    historical_data = get_historical_data()
    for data in historical_data
        println("Synthesizing task: ", data[:task])
        out_dir = synth(data[:eval_file], mode, data[:task]; truncate, time_limit, max_depth, mcmc_steps)
        write_figure5_right_single(mode, data[:task], out_dir)
    end
end

function write_figure5_right_single(mode, task, out_dir)
    file = "data_to_plot/figure5-right/$(mode)/$(task).json"
    mkpath(dirname(file))
    open(file, "w") do f
        JSON.print(f, Dict(:synth_file => out_dir), 2)
    end
    println("Wrote $file")
end

all_tasks = [
    "cIID-Gen",
    "cIID-IO",
    "Markov-Gen",
    "Markov-IO",
    "HMM-Gen",
    "HMM-Gen-IO"
]
all_modes = [:bdd, :dice, :lazy, :smc]

function build_figure5_right()
    data = open("data_to_plot/figure5-right/synthesis_result_template.json") do f
        JSON.parse(f)
    end
    for task in all_tasks
        group = findfirst(g -> g["config"]["task"] == task, data["groups"])
        @assert !isnothing(group)
        group = data["groups"][group]
        @assert isempty(group["runs"])
        for mode in all_modes
            res = open("data_to_plot/figure5-right/$(mode)/$(task).json") do f
                JSON.parse(f)
            end
            path = res["synth_file"]
            push!(group["runs"], Dict(:mode => mode, :path => path * "/summary.json"))
        end
    end
    open("data_to_plot/figure5-right/synthesis_result.json", "w") do f
        JSON.print(f, data, 2)
    end
    println("Wrote data_to_plot/figure5-right/synthesis_result.json")
end

function build_figure5_left()
    data = open("data_to_plot/figure5-left/fuzzing_result_template.json") do f
        JSON.parse(f)
    end
    for task in all_tasks
        group = findfirst(g -> g["config"]["task"] == task, data["groups"])
        @assert !isnothing(group)
        group = data["groups"][group]
        @assert !haskey(group, "eval_file")

        # initialize with first mode
        first_mode = all_modes[1]
        eval_file = open("data_to_plot/figure5-left/$(first_mode)/$(task).json") do f
            JSON.parse(f)["eval_file"]
        end
        merged = open(eval_file) do f
            JSON.parse(f)
        end

        group["eval_file"] = merged
        for mode in all_modes[2:end]
            eval_file = open("data_to_plot/figure5-left/$(mode)/$(task).json") do f
                JSON.parse(f)["eval_file"]
            end
            to_add = open(eval_file) do f
                JSON.parse(f)
            end
            mode_str = String(mode)
            for i in 1:length(merged["task_info"])
                merged["task_info"][i]["res"][mode_str] = to_add["task_info"][i]["res"][mode_str]
            end
        end
        # write out the combined eval_file
        dir = "data_to_plot/figure5-left/combined"
        mkpath(dir)
        open(joinpath(dir, "$(task).json"), "w") do f
            JSON.print(f, merged, 2)
        end
        println("Wrote $dir/$(task).json")
        group["eval_file"] = joinpath(dir, "$(task).json")
    end
    open("data_to_plot/figure5-left/fuzzing_result.json", "w") do f
        JSON.print(f, data, 2)
    end
    println("Wrote data_to_plot/figure5-left/fuzzing_result.json")
end


function fuzz(gen_file, mode; truncate=10, time_limit=1.0, max_depth=1000)
    dataset_json = open(gen_file) do f
        JSON.parse(f)
    end

    # TEMPORARY
    if !isnothing(truncate)
        dataset_json["tasks"] = dataset_json["tasks"][1:truncate]
        dataset_json["task_info"] = dataset_json["task_info"][1:truncate]
    end

    tasks = [from_json(PTask, task) for task in dataset_json["tasks"]]
    task_info = dataset_json["task_info"]

    dataset_json["time_limit"] = time_limit

    progress = collect(1:length(tasks))
    progress = ProgressBar(progress)
    set_description(progress, "Evaluating")
    GC.gc()
    Threads.@threads :greedy for i in progress
        task = tasks[i]
        task_info[i]["res"] = Dict()

        kwargs_of_task = task -> (; time_limit, max_depth, state_vars=StateVars(; fuel=autofuel(task)))
        eval_builder = make_tc(mode; kwargs_of_task)
        task_constrain_fn = eval_builder(task)
        train_res = task_constrain_fn(task.solution; cache=false, test=false)
        test_res = task_constrain_fn(task.solution; cache=false, test=true)
        task_info[i]["res"][mode] = Dict("train_res" => train_res, "test_res" => test_res)

    end

    dir = timestamp_dir(; base="out/fuzzing-evaluation/")
    file = joinpath(dir, "results.json")
    write_out(dataset_json, file)
    return file
end

function grammar_of_task(task)
    Dict(
        "cIID-Gen" => map_unit_grammar_any_length,
        "cIID-IO" => map_int_grammar_anylength,
        "Markov-Gen" => scanl_unit_grammar_any_length,
        "Markov-IO" => scanl_int_grammar_anylength,
        "HMM-Gen" => map_scanl_unit_grammar_any_length,
        "HMM-Gen-IO" => map_scanl_int_grammar_anylength,
    )[task](;nats=true, lets=true)
end


function synth(eval_file, mode, task; max_depth=1000, temperature=1.0, mcmc_steps=1000, repetitions=1, time_limit=0.05, truncate=8)
    task_dist = grammar_of_task(task)
    evaluate_solution = full_evaluate_solution
    results = Dict()

    kwargs_of_task = task -> (; time_limit, max_depth, state_vars=StateVars(; fuel=autofuel(task)))
    eval_builder = make_tc(mode; kwargs_of_task, temperature, )
    cfg = MCMCConfig(; steps=mcmc_steps, pcfg=task_dist.grammar, eval_builder, evaluate_solution)
    println("Running MCMC with $mode")
    GC.gc()
    println("Memory usage before MCMC: $(mem_usage_mb()) MB")
    summary = mcmc_eval(cfg, eval_file; repetitions, truncate)
    addr = summary_address(summary)
    printstyled("  $mode: $addr\n", color=:green)
    results[mode] = addr

    # outpath = joinpath(summary[:out], "summary.json")

    # printstyled("""
    # {
    #     "mode": "$mode",
    #     "path": "$outpath"
    # },
    # """, color=:yellow)

    # summary = nothing # for GC

    return summary[:out]
end




function fuzzing_evaluation(dataset_path; time_limit=3.0, truncate=nothing, max_depth=1000, modes=[:bdd, :dice, :lazy, :smc])
    dataset_json = open(dataset_path) do f
        JSON.parse(f)
    end

    # TEMPORARY
    if !isnothing(truncate)
        dataset_json["tasks"] = dataset_json["tasks"][1:truncate]
        dataset_json["task_info"] = dataset_json["task_info"][1:truncate]
    end

    tasks = [from_json(PTask, task) for task in dataset_json["tasks"]]
    task_info = dataset_json["task_info"]

    dataset_json["time_limit"] = time_limit

    progress = collect(1:length(tasks))
    progress = ProgressBar(progress)
    set_description(progress, "Evaluating")
    GC.gc()
    Threads.@threads :greedy for i in progress
        task = tasks[i]
        # res = Dict()
        # raw_expr = string(task.solution)
        task_info[i]["res"] = Dict()
        # @show i
        # @show task.solution
        # @show task.ios
        for mode in modes
            # @show mode
            kwargs_of_task = task -> (; time_limit, max_depth, state_vars=StateVars(; fuel=autofuel(task)))
            eval_builder = make_tc(mode; kwargs_of_task)
            task_constrain_fn = eval_builder(task)
            train_res = task_constrain_fn(task.solution; cache=false, test=false)
            test_res = task_constrain_fn(task.solution; cache=false, test=true)
            task_info[i]["res"][mode] = Dict("train_res" => train_res, "test_res" => test_res)
        end

    end

    dir = timestamp_dir(; base="out/fuzzing-evaluation/")
    file = joinpath(dir, "results.json")
    write_out(dataset_json, file)
    addr = webaddress("html/fuzzing.html", file, false)
    println(addr)
    return file
end




function test_mcmc(eval_file, task_dist; modes=[:bdd, :lazy, :smc, :dice], max_depth=1000, temperature=1.0, mcmc_steps=1000, repetitions=3, time_limit=0.05, truncate=nothing)
    evaluate_solution = full_evaluate_solution
    results = Dict()
    for mode in modes
        kwargs_of_task = task -> (; time_limit, max_depth, state_vars=StateVars(; fuel=autofuel(task)))
        eval_builder = make_tc(mode; kwargs_of_task, temperature, )
        cfg = MCMCConfig(; steps=mcmc_steps, pcfg=task_dist.grammar, eval_builder, evaluate_solution)
        println("Running MCMC with $mode")
        GC.gc()
        println("Memory usage before MCMC: $(mem_usage_mb()) MB")
        summary = mcmc_eval(cfg, eval_file; repetitions, truncate)
        addr = summary_address(summary)
        printstyled("  $mode: $addr\n", color=:green)
        results[mode] = addr

        outpath = joinpath(summary[:out], "summary.json")

        printstyled("""
        {
            "mode": "$mode",
            "path": "$outpath"
        },
        """, color=:yellow)

        summary = nothing # for GC
    end
    return results
end

function mem_usage_mb()
    pid = getpid()
    if Sys.isunix()
        # Get RSS and VSZ for the current process
        cmd = `ps -o rss=,vsz= -p $pid`
        output = read(cmd, String)
        rss, vsz = parse.(Int, split(strip(output)))
        return rss ÷ 1024
    else
        # Fallback for non-Unix systems
        # return Base.gc_num()
        # @warn "Memory usage not supported on non-Unix systems"
        return 0
    end
end

function mcmc_eval(cfg, dataset_path; repetitions=3, warmstart=true, truncate=nothing)
    # Pluck.SINGLE_THREAD = true
    dataset_json = open(dataset_path) do f
        JSON.parse(f)
    end
    tasks = [from_json(PTask, task) for task in dataset_json["tasks"]]
    task_info = dataset_json["task_info"]

    if !isnothing(truncate)
        tasks = tasks[1:truncate]
        task_info = task_info[1:truncate]
    end

    gcfg = GroupConfig(; tasks, task_info, config=cfg, repetitions, warmstart)
    GC.gc()
    solve_tasks(gcfg)
end

function full_evaluate_solution(expr, task)
    time_limit = 3.0
    max_depth = 1000
    state_vars = StateVars(; fuel=autofuel(task))
    configs = [
        BDDEvalStateConfig(; time_limit, max_depth, state_vars),
        DiceConfig(; time_limit, max_depth, state_vars),
        LazyEnumeratorConfig(; time_limit, max_depth, state_vars),
    ]
    train_res = test_res = nothing
    for config in configs
        tc = TaskConstrain(task, config; temperature=1.0)
        if isnothing(train_res)
            try_train_res = tc(expr; cache=false, test=false)
            if !try_train_res.stats.hit_limit
                train_res = try_train_res
            end
        end
        if isnothing(test_res)
            try_test_res = tc(expr; cache=false, test=true)
            if !try_test_res.stats.hit_limit
                test_res = try_test_res
            end
        end
    end
    return train_res, test_res
end


function nov13()
    M = 4
    E = 4
    N = 100
    fuzz_time_limit = 1.0 # submission: 3.0
    fuzz_truncate = 10 # submission: nothing overnight: 20 artifact: 10
    mcmc_repetitions = 1 # submission: 3
    mcmc_truncate = 8 # submission: nothing overnight: 20 artifact: 10

    nats = true
    lets = true
    modes = [:dice, :bdd, :lazy, :smc]
    # modes = [:strict]
    # modes = [:dice, :bdd, :lazy]
    # modes = [:bdd, :lazy]
    # modes = [:smc]
    dists = [
        Dict(
            :name => :cIID,
            :func => map_unit_grammar_any_length,
            # :gen_file => "out/fuzz-datasets/2025-03-18/16-09-26-000/dataset.json",
            :gen_file => "out/fuzz-datasets/2024-11-13/04-07-10/dataset.json",
            # :eval_file => "out/fuzzing-evaluation/2025-03-15/11-56-13-000/results.json",
            :eval_file => "out/fuzzing-evaluation/2025-03-18/17-38-46-000/results.json", #"out/fuzzing-evaluation/2024-11-13/04-14-52/results.json",
            :mcmc_addrs => Dict{Any,Any}(
                :dice => nothing, # "http://localhost:8000/out/results/2024-11-13/15-52-18/expt/html/summary.html?path=summary.json",
                :bdd => nothing, # "http://localhost:8000/out/results/2024-11-13/16-31-38/expt/html/summary.html?path=summary.json",
                :lazy => nothing, # "http://localhost:8000/out/results/2024-11-13/16-55-41/expt/html/summary.html?path=summary.json",
                :smc => nothing, # "http://localhost:8000/out/results/2024-11-14/04-56-54/expt/html/summary.html?path=summary.json",
            ),
        ),
        Dict(
            :name => :cIID_IO,
            :func => map_int_grammar_anylength,
            # :gen_file => "out/fuzz-datasets/2025-03-18/16-09-31-000/dataset.json",
            :gen_file => "out/fuzz-datasets/2024-11-13/14-36-57/dataset.json",
            # :eval_file => "out/fuzzing-evaluation/2025-03-15/11-58-39-000/results.json",
            :eval_file => nothing, #"out/fuzzing-evaluation/2024-11-13/14-45-33/results.json",
            :mcmc_addrs => Dict{Any,Any}(
                :dice => nothing, # "http://localhost:8000/out/results/2024-11-13/18-11-31/expt/html/summary.html?path=summary.json",
                :bdd => nothing, # "http://localhost:8000/out/results/2024-11-13/18-49-06/expt/html/summary.html?path=summary.json",
                :lazy => nothing, # "http://localhost:8000/out/results/2024-11-13/19-12-09/expt/html/summary.html?path=summary.json",
                :smc => nothing, # "http://localhost:8000/out/results/2024-11-14/05-19-26/expt/html/summary.html?path=summary.json",
            )
        ),
        Dict(:name => :Markov,
            :func => scanl_unit_grammar_any_length,
            # :gen_file => nothing,
            :gen_file => "out/fuzz-datasets/2024-11-13/04-07-20/dataset.json",
            # :eval_file => "out/fuzzing-evaluation/2025-03-15/12-00-41-000/results.json",
            :eval_file => nothing, #"out/fuzzing-evaluation/2024-11-13/13-12-32/results.json",
            :mcmc_addrs => Dict{Any,Any}(
                :dice => nothing, # "http://localhost:8000/out/results/2024-11-13/19-38-24/expt/html/summary.html?path=summary.json",
                :bdd => nothing, # "http://localhost:8000/out/results/2024-11-13/21-09-17/expt/html/summary.html?path=summary.json",
                :lazy => nothing, # "http://localhost:8000/out/results/2024-11-13/21-41-40/expt/html/summary.html?path=summary.json",
                :smc => nothing, # "http://localhost:8000/out/results/2024-11-14/03-18-34/expt/html/summary.html?path=summary.json",
            )
        ),
        Dict(:name => :Markov_IO,
            :func => scanl_int_grammar_anylength,
            :gen_file => "out/fuzz-datasets/2024-11-13/14-37-19/dataset.json",
            # :eval_file => "out/fuzzing-evaluation/2025-03-15/12-02-54-000/results.json",
            :eval_file => nothing, #"out/fuzzing-evaluation/2024-11-13/15-41-10/results.json",
            :mcmc_addrs => Dict{Any,Any}(
                :bdd => nothing, # "http://localhost:8000/out/results/2024-11-14/01-42-18/expt/html/summary.html?path=summary.json",
                :dice => nothing, # "http://localhost:8000/out/results/2024-11-14/00-51-39/expt/html/summary.html?path=summary.json",
                :lazy => nothing, # "http://localhost:8000/out/results/2024-11-14/02-10-32/expt/html/summary.html?path=summary.json",
                :smc => nothing, # "http://localhost:8000/out/results/2024-11-14/03-50-49/expt/html/summary.html?path=summary.json",
            )
        ),
        Dict(
            :name => :HMM,
            :func => map_scanl_unit_grammar_any_length,
            :gen_file => "out/fuzz-datasets/2024-11-13/04-07-50/dataset.json",
            # :eval_file => "out/fuzzing-evaluation/2025-03-15/12-04-55-000/results.json",
            :eval_file => nothing, #"out/fuzzing-evaluation/2024-11-13/13-51-45/results.json",
            :mcmc_addrs => Dict{Any,Any}(
                :bdd => nothing, # "http://localhost:8000/out/results/2024-11-14/06-38-38/expt/html/summary.html?path=summary.json",
                :dice => nothing, # "http://localhost:8000/out/results/2024-11-14/05-41-56/expt/html/summary.html?path=summary.json",
                :lazy => nothing, # "http://localhost:8000/out/results/2024-11-14/07-07-38/expt/html/summary.html?path=summary.json",
                :smc => nothing, # "http://localhost:8000/out/results/2024-11-14/07-38-51/expt/html/summary.html?path=summary.json",
            )
        ),
        Dict(
            :name => :HMM_IO,
            :func => map_scanl_int_grammar_anylength,
            :gen_file => "out/fuzz-datasets/2024-11-14/13-34-18/dataset.json",
            # :eval_file => "out/fuzzing-evaluation/2025-03-15/12-06-44-000/results.json",
            :eval_file => "out/fuzzing-evaluation/2024-11-14/13-45-02/results.json",
            :mcmc_addrs => Dict{Any,Any}(
                :bdd => nothing, # "http://localhost:8000/out/results/2024-11-14/15-47-40/expt/html/summary.html?path=summary.json",
                :dice => nothing, # "http://localhost:8000/out/results/2024-11-14/13-45-03/expt/html/summary.html?path=summary.json",
                :lazy => nothing, # "http://localhost:8000/out/results/2024-11-14/18-25-02/expt/html/summary.html?path=summary.json",
                :smc => nothing, # "http://localhost:8000/out/results/2024-11-14/18-56-13/expt/html/summary.html?path=summary.json",
            )
        ),

        # Dict(
        #     :name => :cIID_strict,
        #     :func => map_unit_grammar_any_length,
        #     :gen_file => "out/fuzz-datasets/2024-11-13/04-07-10/dataset.json",
        #     :eval_file => nothing,
        # ),

        # Dict(
        #     :name => :cIID_fuel4,
        #     :func => map_unit_grammar_any_length,
        #     :gen_file => "out/fuzz-datasets/2024-11-13/04-07-10/dataset.json",
        #     :eval_file => nothing,
        # ),
        # Dict(
        #     :name => :cIID_IO,
        #     :func => map_int_grammar_anylength,
        #     :gen_file => "out/fuzz-datasets/2024-11-13/14-36-57/dataset.json",
        #     :eval_file => nothing,
        # ),
        # Dict(:name => :Markov_fuel4,
        #     :func => scanl_unit_grammar_any_length,
        #     :gen_file => "out/fuzz-datasets/2024-11-13/04-07-20/dataset.json",
        #     :eval_file => nothing,
        # ),
        # Dict(:name => :Markov_IO,
        #     :func => scanl_int_grammar_anylength,
        #     :gen_file => "out/fuzz-datasets/2024-11-13/14-37-19/dataset.json",
        #     :eval_file => nothing,
        # ),
        # Dict(
        #     :name => :HMM,
        #     :func => map_scanl_unit_grammar_any_length,
        #     :gen_file => "out/fuzz-datasets/2024-11-13/04-07-50/dataset.json",
        #     :eval_file => nothing,
        # ),
        # Dict(
        #     :name => :HMM_IO,
        #     :func => map_scanl_int_grammar_anylength,
        #     :gen_file => "out/fuzz-datasets/2024-11-14/13-34-18/dataset.json",
        #     :eval_file => nothing,
        # ),



    ]

    println("Generating datasets")
    for dist in dists
        if !isnothing(dist[:gen_file])
            println("Skipping $(dist[:name]) because it already has a generated dataset")
            continue
        end
        println("Generating $(dist[:name])")
        task_dist = dist[:func](; nats, lets)
        println("Memory usage before generating dataset: $(mem_usage_mb()) MB")
        gen_file = make_fuzzing_dataset(; N, M, E, task_dist)
        dist[:gen_file] = gen_file
        printstyled("Generated $(dist[:name]) as $gen_file\n", color=:green)
        # println(dist)
    end
    println("Memory usage: $(mem_usage_mb()) MB")

    println("Fuzzing datasets")
    for dist in dists
        if !isnothing(dist[:eval_file])
            println("Skipping $(dist[:name]) because it already has a fuzzed dataset")
            continue
        end
        println("Memory usage before fuzzing: $(mem_usage_mb()) MB")
        println("Fuzzing $(dist[:name]) from $(dist[:gen_file])")
        eval_file = fuzzing_evaluation(dist[:gen_file]; modes, time_limit=fuzz_time_limit, truncate=fuzz_truncate)
        dist[:eval_file] = eval_file
        printstyled("Fuzzed $(dist[:name]) as $eval_file\n", color=:green)
        # println(dist)
    end


    println("Running MCMC on datasets")
    for dist in dists
        if !haskey(dist, :mcmc_addrs)
            println("Skipping $(dist[:name]) because it doesn't have a :mcmc_addrs key")
            continue
        end
        # if !isnothing(dist[:mcmc_addrs])
        #     println("Skipping $(dist[:name]) because it already has been run with MCMC")
        #     continue
        # end
        println("Running MCMC on $(dist[:name]) from $(dist[:eval_file])")

        mcmc_modes = filter(mode -> haskey(dist[:mcmc_addrs], mode) && isnothing(dist[:mcmc_addrs][mode]), modes)

        if isempty(mcmc_modes)
            println("Skipping $(dist[:name]) because it already has all MCMC results")
            continue
        end

        results = test_mcmc(dist[:eval_file], dist[:func](; nats, lets); modes=mcmc_modes, repetitions=mcmc_repetitions, truncate=mcmc_truncate)
        printstyled("Evaluated MCMC for $(dist[:name])\n", color=:green)
        for (mode, addr) in results
            dist[:mcmc_addrs][mode] = addr
            printstyled("  $mode: $addr\n", color=:green)
        end
        # println(dist)
    end
    println("Memory usage at end: $(mem_usage_mb()) MB")
    println(dists)
    nothing
end


function simplify_json(json_path)
    summary = JSON.parsefile(json_path)
    for task_stubs in ProgressBar(summary["init_stubs_of_task"])
        for stub in task_stubs
            stub["result"] = nothing
            stub_path = stub["out"] * "/" * stub["stub_path"]
            stub_data = JSON.parsefile(stub_path)
            for log_step in stub_data["result"][1]["state_log"]
                log_step["proposals"] = nothing
            end
            open(stub_path, "w") do f
                JSON.print(f, stub_data)
            end
        end
    end
    open(json_path, "w") do f
        JSON.print(f, summary)
    end
end


function run_specific()
    # dist = Dict(:name => :map_int_grammar,
    #      :func => map_int_grammar,
    #      :eval_file => "out/fuzzing-evaluation/2024-11-12/01-34-24/results.json"
    #      )

    dist = Dict(
        :name => :scanl_unit_grammar_any_length,
        :func => scanl_unit_grammar_any_length,
        :eval_file => "out/fuzzing-evaluation/2024-11-12/01-35-24/results.json"
    )
    modes = [:dice, :bdd, :smc, :lazy]

    nats = lets = true
    @show modes
    results = test_mcmc(dist[:eval_file], dist[:func](; nats, lets); modes)
    println(results)
end

"""

There are two url formats that could happen, and you can detect the difference by whether they contain "?path=/out"
http://localhost:8000/out/results/2024-11-12/01-36-35/expt/html/summary.html?path=summary.json
http://localhost:8000/html/summary.html?path=/out/results/2024-11-12/01-36-35/expt/summary.json

for either one we want to extract "path=/out/results/2024-11-12/01-36-35/expt/summary.json"

We want to do this for every url that's given (each of which could be in either format) and then
join them with "&"s and prepend "http://localhost:8000/html/summary.html?" to the front.

"""
function synth_url(urls...)
    url = "http://localhost:8000/html/synthesis.html?"
    for path in urls
        if occursin("path=/out", path)
            # http://localhost:8000/html/summary.html?path=/out/results/2024-11-12/01-36-35/expt/summary.json
            start_idx = findfirst("/out", path)[1]
            path_str = "path=" * path[start_idx:end]
        else
            # http://localhost:8000/out/results/2024-11-12/01-36-35/expt/html/summary.html?path=summary.json
            start_idx = findfirst("/out", path)[1]
            end_idx = findfirst("/html/", path)[1]
            path_str = "path=" * path[start_idx:end_idx] * "summary.json"
        end
        url *= path_str * "&"
    end
    return url[1:end-1] # remove trailing "&"
end










function eval_bdd_forward(expr, input=true, output=true; equality_fn="old_list_eq", warmstart_time_limit=0.05, kwargs...)
    expr = io_equality_expr(expr, [input], output; equality_fn)
    bdd_forward(expr; time_limit=warmstart_time_limit, kwargs...) # warmstart
    time = (@timed ((res, state) = bdd_forward(expr; return_state=true, kwargs...))).time
    loglikelihood = log(Pluck.get_true_result(res))
    Dict("time" => time, "loglikelihood" => loglikelihood, "hit_limit" => state.hit_limit)
end

function eval_smc_forward(expr, input=true, output=true; equality_fn="suspended_list_eq ==", warmstart_time_limit=0.05, kwargs...)
    expr = io_equality_expr(expr, [input], output; equality_fn)
    bdd_forward_with_suspension(expr; time_limit=warmstart_time_limit, kwargs...) # warmstart
    time = (@timed ((res, state) = bdd_forward_with_suspension(expr; return_state=true, kwargs...))).time
    loglikelihood = log(Pluck.get_true_result(res))
    Dict("time" => time, "loglikelihood" => loglikelihood, "hit_limit" => state.hit_limit)
end

function eval_lazy_enumeration(expr, input=true, output=true; equality_fn="old_list_eq", warmstart_time_limit=0.05, kwargs...)
    expr = io_equality_expr(expr, [input], output; equality_fn)
    lazy_enumerate(expr; time_limit=warmstart_time_limit, kwargs...) # warmstart
    time = (@timed ((res, state) = lazy_enumerate(expr; return_state=true, kwargs...))).time
    loglikelihood = log(Pluck.get_true_result(res))
    Dict("time" => time, "loglikelihood" => loglikelihood, "hit_limit" => state.hit_limit)
end

function eval_strict_enumeration(expr, input=true, output=true; equality_fn="old_list_eq", warmstart_time_limit=0.05, kwargs...)
    kwargs = (strict=true, disable_traces=true, disable_cache=true, kwargs...)
    return eval_lazy_enumeration(expr, input, output; equality_fn, warmstart_time_limit, kwargs...)
end



function compare(expr, input=true, output=true; equality_fn="old_list_eq", bdd=true, lazy=true, strict=true, smc=true, no_thunkunions=false, kwargs...)
    if bdd
        bdd = eval_bdd_forward(expr, input, output; equality_fn, kwargs...)
        @show bdd
    end
    if lazy
        lazy = eval_lazy_enumeration(expr, input, output; equality_fn, kwargs...)
        @show lazy
    end
    if strict
        strict = eval_strict_enumeration(expr, input, output; equality_fn, kwargs...)
        @show strict
    end
    if smc
        smc = eval_smc_forward(expr, input, output; equality_fn="suspended_list_eq ==", kwargs...)
        @show smc
    end
    if no_thunkunions
        no_thunk_unions = eval_bdd_forward(expr, input, output; equality_fn, use_thunk_unions=false, kwargs...)
        @show no_thunk_unions
    end
    nothing
end


# function ttt()
#     # @define "geom_bounded" "(Y (λ rec n -> (case n of O => (O) | S => (λp -> (if (flip 0.5) (O) (S (rec p)))))))"

#     # @define "Yn" "(Y (λ rec n init f -> (case n of O => init | S => (λp -> (f (rec p init f))))))"

#     # @define "Yn" "(Y (λ rec f fuel -> (case fuel of S => (λfuel -> (f (rec f fuel))))))"

#     # @define "geom_bounded" "(Yn (λ rec n -> (case n of O => (O) | S => (λp -> (if (flip 0.5) (O) (S (rec p)))))))"

#     # @define alt_geom_bounded "(λn -> (Yn n (O) (λres -> (if (flip 0.5) res (S res)))))"


#     @define "bool_and" "bool -> bool -> bool" "(λ x y -> (case x of True => y | False => false))"
#     @define "bool_or" "bool -> bool -> bool" "(λ x y -> (case x of True => true | False => y))"
#     @define "bool_xor" "bool -> bool -> bool" "(λ x y -> (case x of True => (not y) | False => y))"

#     # compare("(bool_or (flip 0.5) (flip 0.5))", true, true; equality_fn = "constructors_equal")




#     # @define "geom_bounded" "(Y (λ rec fuel -> (case fuel of S => (λfuel -> (if (flip 0.5) (O) (S (rec fuel)))))))"



#     # @show sample_output("(flip_tree 10)")

#     # @define Yn "(Y (λ rec n  -> (if x (False) x)))"


#     @define "flip_tree" "(Y (λ rec fuel -> (case fuel of O => (flip 0.5) | S => (λfuel -> (bool_xor (rec fuel) (rec fuel))))))"

#     @define "leaning_flip_tree" "(Y (λ rec fuel branchfuel -> (case fuel of O => (flip 0.5) | S => (λfuel -> (bool_xor (flip_tree branchfuel) (rec fuel branchfuel))))))"

#     @define "structured_flip_tree" "(Y (λ rec fuel -> (case fuel of O => (flip 0.5) | S => (λfuel -> (if (flip 0.5) (flip 0.5) (bool_xor (rec fuel) (rec fuel)))))))"


#     # compare("(leaning_flip_tree 100 2)", true, true; equality_fn = "constructors_equal")
#     # compare("(flip_tree 8)", true, true; equality_fn = "constructors_equal", lazy=false, strict=false)




#     compare("(map (λx -> (if (flip 0.5) 0 0)) (fill 14 0))", true, fill(0, 2); equality_fn="old_list_eq")

# end

# function ladder()
#     @define "ladder_network" """

#     (lambda i1 i2 -> 
#       (let (output (flip 0.5)
#             result (Cons output (not output))
#             fail_result (Cons false false))
#         (if i1 (if (flip 0.001) fail_result result)
#           (if i2 result fail_result))))

#     """

#     @define "run_ladder_network" """
#       (lambda m -> (case ((Y (lambda run_ladder_network n -> (case n of O => (Cons true false) | S m => (case (run_ladder_network m) of Cons i1 i2 => (ladder_network i1 i2))))) m) of Cons i1 i2 => i1))
#     """

#     bdd_forward("(run_ladder_network 1)")
# end


function default_input_dist(input_type::String)
    Dict(
        "list" => "(fillrand $(make_uniform_nat(6)))",
        "int" => "(make_random_digit)",
        "bool" => "(flip 0.5)",
        "unit" => "(Unit)",
    )[input_type]
end


function map_unit_grammar(; length=10, nats=true, kwargs...)
    start = "(mapunit (λx -> $(nats ? "randnat" : "make_random_digit")) $length)"
    grammar_start = "(mapunit (λx -> ?int) $length)"

    TaskDist(
        seq_grammar(start, grammar_start; nats, kwargs...),
        "unit",
        "list",
        "(Unit)",
        (_) -> true,
        (_, o) -> any(x -> x != o[1], o) # not all the same
    )
end

function map_int_grammar(; length=10, nats=true, kwargs...)
    start = "(map (λx -> $(nats ? "randnat" : "make_random_digit")) #1)"
    grammar_start = "(map (λx -> ?int) #1)"

    TaskDist(
        seq_grammar(start, grammar_start; nats, kwargs...),
        "list",
        "list",
        "(fillrand $length)",
        (e) -> occursin("x#", e),
        (_, o) -> any(x -> x != o[1], o) # not all the same
    )
end

function map_int_grammar_anylength(; nats=true, kwargs...)
    randint = nats ? "randnat" : "make_random_digit"
    start = "(map (λact -> $randint) (take $randint #1))"
    grammar_start = "(map (λact -> ?int) (take ?int #1))"

    TaskDist(
        seq_grammar(start, grammar_start; nats, kwargs...),
        "list",
        "list",
        "(fillrand 30)",
        (e) -> occursin("act#", e),
        (_, o) -> any(x -> x != o[1], o) # not all the same
    )
end



function scanl_unit_grammar(; length=10, nats=true, kwargs...)
    start = "(scanlunit (λacc x -> $(nats ? "randnat" : "make_random_digit")) 0 $length)"
    grammar_start = "(scanlunit (λacc x -> ?int) 0 $length)"

    TaskDist(
        seq_grammar(start, grammar_start; nats, kwargs...),
        "unit",
        "list",
        "(Unit)",
        (e) -> occursin("acc#", e),
        (_, o) -> any(x -> x != o[1], o) # not all the same
    )
end

function scanl_unit_grammar_any_length(; nats=true, kwargs...)
    randint = nats ? "randnat" : "make_random_digit"
    start = "(scanlunit (λacc x -> $randint) 0 $randint)"
    grammar_start = "(scanlunit (λacc x -> ?int) 0 ?int)"

    TaskDist(
        seq_grammar(start, grammar_start; nats, kwargs...),
        "unit",
        "list",
        "(Unit)",
        (e) -> occursin("acc#", e),
        (_, o) -> any(x -> x != o[1], o) # not all the same
    )
end


function map_unit_grammar_any_length(; nats=true, kwargs...)
    randint = nats ? "randnat" : "make_random_digit"
    start = "(mapunit (λx -> $randint) $randint)"
    grammar_core = "(mapunit (λx -> ?int) ?int)"

    TaskDist(
        seq_grammar(start, grammar_core; nats, kwargs...),
        "unit",
        "list",
        "(Unit)",
        (e) -> true,
        (_, o) -> any(x -> x != o[1], o) # not all the same
    )
end



function scanl_int_grammar(; length=10, nats=true, kwargs...)
    start = "(scanl (λacc x -> $(nats ? "randnat" : "make_random_digit")) 0 #1)"
    grammar_start = "(scanl (λacc x -> ?int) 0 #1)"

    TaskDist(
        seq_grammar(start, grammar_start; nats, kwargs...),
        "list",
        "list",
        "(fillrand $length)",
        (e) -> occursin("acc#", e) && occursin("x#", e),
        (_, o) -> any(x -> x != o[1], o) # not all the same
    )
end

function scanl_int_grammar_anylength(; nats=true, kwargs...)
    randint = nats ? "randnat" : "make_random_digit"
    start = "(scanl (λacc act -> $randint) 0 (take $randint #1))"
    grammar_start = "(scanl (λacc act -> ?int) 0 (take ?int #1))"

    TaskDist(
        seq_grammar(start, grammar_start; nats, kwargs...),
        "list",
        "list",
        "(fillrand 30)",
        (e) -> occursin("acc#", e) && occursin("act#", e),
        (_, o) -> any(x -> x != o[1], o) # not all the same
    )
end






function map_scanl_unit_grammar(; length=10, nats=true, kwargs...)
    start = "(map (λstate -> $(nats ? "randnat" : "make_random_digit")) (scanlunit (λacc x -> $(nats ? "randnat" : "make_random_digit")) 0 $length))"
    grammar_start = "(map (λstate -> ?int) (scanlunit (λacc x -> ?int) 0 $length))"

    TaskDist(
        seq_grammar(start, grammar_start; nats, kwargs...),
        "unit",
        "list",
        "(Unit)",
        (e) -> occursin("state#", e) && occursin("acc#", e),
        (_, o) -> any(x -> x != o[1], o) # not all the same
    )
end


# anylength + geom noise
function hmm_simple(; nats=true, kwargs...)
    randint = nats ? "randnat" : "make_random_digit"
    # noise = "(geom_fuel 0.5 5)" # "$randint"
    noise = "$randint"

    start = "(map (λstate -> (+ state $noise)) (scanlunit (λacc x -> $randint) 0 $randint))"
    grammar_start = "(map (λstate -> (+ ?int $noise)) (scanlunit (λacc x -> ?int) 0 ?int))"

    TaskDist(
        seq_grammar(start, grammar_start; nats, kwargs...),
        "unit",
        "list",
        "(Unit)",
        (e) -> occursin("state#", e) && occursin("acc#", e),
        (_, o) -> any(x -> x != o[1], o) # not all the same
    )
end


function map_scanl_unit_grammar_any_length(; nats=true, kwargs...)
    randint = nats ? "randnat" : "make_random_digit"
    start = "(map (λstate -> $randint) (scanlunit (λacc x -> $randint) 0 $randint))"
    grammar_core = "(map (λstate -> ?int) (scanlunit (λacc x -> ?int) 0 ?int))"

    TaskDist(
        seq_grammar(start, grammar_core; nats, kwargs...),
        "unit",
        "list",
        "(Unit)",
        (e) -> occursin("state#", e) && occursin("acc#", e),
        (_, o) -> any(x -> x != o[1], o) # not all the same
    )
end



function map_scanl_int_grammar(; length=10, nats=true, kwargs...)
    randint = nats ? "randnat" : "make_random_digit"
    start = "(map (λstate -> $randint) (scanl (λacc act -> $randint) 0 #1))"
    grammar_start = "(map (λstate -> ?int) (scanl (λacc act -> ?int) 0 #1))"

    TaskDist(
        seq_grammar(start, grammar_start; nats, kwargs...),
        "list",
        "list",
        "(fillrand $length)",
        (e) -> occursin("state#", e) && occursin("acc#", e) && occursin("act#", e),
        (_, o) -> any(x -> x != o[1], o) # not all the same
    )
end



function map_scanl_int_grammar_anylength(; nats=true, kwargs...)
    randint = nats ? "randnat" : "make_random_digit"
    start = "(map (λstate -> $randint) (scanl (λacc x -> $randint) 0 (take $randint #1)))"
    grammar_start = "(map (λstate -> ?int) (scanl (λacc x -> ?int) 0 (take ?int #1)))"

    TaskDist(
        seq_grammar(start, grammar_start; nats, kwargs...),
        "list",
        "list",
        "(fillrand 30)",
        (e) -> occursin("state#", e) && occursin("acc#", e) && occursin("x#", e),
        (_, o) -> any(x -> x != o[1], o) # not all the same
    )
end





function seq_grammar(start::String, grammar_core::String; nats=true, lets=true, size_dist=Geometric(0.5))

    # BAD BAD BAD
    start = lets ? replace(start, "#1" => "#2") : start
    grammar_core = lets ? replace(grammar_core, "#1" => "#2") : grammar_core


    Pluck.synthesis_defs()
    @define map "(int -> int) -> list -> list" "(Y (λ rec f xs -> (case xs of Nil => (Nil) | Cons => (λhd tl -> (Cons (f hd) (rec f tl))))))"
    @define mapunit "(unit -> int) -> int -> list" "(λ f n -> (map f (fill n (Unit))))"
    @define "bool_and" "bool -> bool -> bool" "(λ x y -> (case x of True => y | False => false))"
    @define "bool_or" "bool -> bool -> bool" "(λ x y -> (case x of True => true | False => y))"
    @define "bool_xor" "bool -> bool -> bool" "(λ x y -> (case x of True => (not y) | False => y))"


    # @define fold "(Y (λrec xs init f -> (case xs of Nil => init | Cons => (λhd tl -> (f hd (rec tl init f))))))"
    @define foldl "(int -> int -> int) -> int -> list -> int" """
        (Y (λrec f acc xs ->
            (case xs of Nil => acc
                      | Cons => (λhd tl ->
                                (let (acc' (f acc hd))
                                    (rec f acc' tl)
                                ))
            )
        ))
    """
    @define scanl "(int -> int -> int) -> int -> list -> list" """
        (Y (λrec f acc xs ->
            (case xs of Nil => (Nil)
                    | Cons => (λhd tl ->
                                (let (acc' (f acc hd))
                                    (Cons acc' (rec f acc' tl))
                                ))
            )
        ))
    """

    @define scanlunit "(int -> unit -> int) -> int -> int -> list" "(λf init n -> (scanl f init (fill n (Unit))))"

    @define app_int_int "(int -> int) -> int -> int" "(λ f x -> (f x))"
    @define letII "int -> (int -> int) -> int" "(λ x f -> (f x))"

    prods = [
        # "?list" => ["(map (λx -> ?int) (fill $length 0))"],
        # "?list" => ["(mapunit (λx -> ?int) $length)"],

        "?core" => [grammar_core],
        "?lets" => ["(letII ?int (λk -> ?core))"],
        "?int" => ["?int_term" => 8, "?int_nonterm" => 2],
        "?int_term" => [
            (nats ? "randnat" : "make_random_digit"),
            "?const_or_var",
            "(letII ?int (λx -> ?int_nonterm))" => 0.2
            # "(app_int_int (λx -> ?int_nonterm) ?int)" => 0.2
        ],
        "?const_or_var" => [
            "#int",
            "?constint" => 0.3
        ],
        "?constint" => [("$i" for i ∈ 0:9)...],
        "?int_nonterm" => [
            "(inc ?int)",
            "(+ ?int ?int)",
            "(- ?int ?int)",
            "(case ?int of O => ?int | S => (λn -> ?int))",
            "(if ?bool ?int ?int)",
        ],
        "?bool" => ["?bool_term" => 8, "?bool_nonterm" => 2],
        "?bool_term" => [
            "#bool",
            ["(flip 0.$i)" for i in 1:9]...,
            # "true",
            # "false"
        ],
        "?bool_nonterm" => [
            # "(bool_and ?bool ?bool)",
            # "(bool_or ?bool ?bool)",
            # "(bool_xor ?bool ?bool)",
            # "(not ?bool)",
            # "(if ?bool ?bool ?bool)",
            "(iseven ?int)",
            "(== ?int ?int)",
            "(> ?int ?int)",
            # "(case ?int of O => ?bool | S => (λn -> ?bool))",
        ],
    ]

    sym_of_type = [
        "list" => lets ? "?lets" : "?core",
        "int" => "?int",
        "bool" => "?bool",
    ]
    start_expr_of_type = [
        # "list" => "(mapunit (λx -> make_random_digit) $length)",
        "list" => lets ? "(letII $(nats ? "randnat" : "make_random_digit") (λk -> $start))" : start,
        # "list" => "(map (λx -> make_random_digit) (fill $length 0))",
    ]
    return Grammar(prods, sym_of_type, start_expr_of_type; size_dist=size_dist)
end

# sample_output("(scanlunit (λacc _ -> (if (flip 0.5) acc (+ acc (if (flip 0.5) 2 10)))) 0 10)")[1]
# sample_output("(scanlunit (λacc _ -> (if (flip 0.5) acc (+ acc acc))) 0 10)")[1]

function all_fuzzers(; kwargs...)
    N = 200
    time_limit = 1.0
    max_depth = 1000
    length = 8

    res = []
    println("map_unit_grammar")
    push!(res, ("map_unit_grammar", fuzzing_evaluation(make_fuzzing_dataset(; N, task_dist=map_unit_grammar(; length)); time_limit, max_depth, kwargs...)))
    println("map_int_grammar")
    push!(res, ("map_int_grammar", fuzzing_evaluation(make_fuzzing_dataset(; N, task_dist=map_int_grammar(; length)); time_limit, max_depth, kwargs...)))

    length = 8
    time_limit = 3.0
    println("scanl_unit_grammar")
    push!(res, ("scanl_unit_grammar", fuzzing_evaluation(make_fuzzing_dataset(; N, task_dist=scanl_unit_grammar(; length)); time_limit, max_depth, kwargs...)))
    println("scanl_int_grammar")
    push!(res, ("scanl_int_grammar", fuzzing_evaluation(make_fuzzing_dataset(; N, task_dist=scanl_int_grammar(; length)); time_limit, max_depth, kwargs...)))
    println("map_scanl_unit_grammar")
    push!(res, ("map_scanl_unit_grammar", fuzzing_evaluation(make_fuzzing_dataset(; N, task_dist=map_scanl_unit_grammar(; length)); time_limit, max_depth, kwargs...)))
    println("map_scanl_int_grammar")
    push!(res, ("map_scanl_int_grammar", fuzzing_evaluation(make_fuzzing_dataset(; N, task_dist=map_scanl_int_grammar(; length)); time_limit, max_depth, kwargs...)))

    for (k, v) in res
        println(k, ": ", v)
    end
    nothing
end




# function bool_grammar(; size_dist=Geometric(0.5))

#     @define "app_bool_bool" "(bool -> bool) -> bool -> bool" "(λ f x -> (f x))"

#     prods = [
#         # "?int" => ["(O)" => .01, "#int", "(S ?int)" => .01],
#         "?bool" => ["?bool_term" => 8, "?bool_nonterm" => 2],
#         "?bool_term" => [
#             "#bool",
#             ["(flip 0.$i)" for i in (1, 2, 3, 4, 5, 6, 7, 8, 9)]...,
#             "false",
#             "true",
#         ],
#         "?bool_nonterm" => [
#             "(bool_and ?bool ?bool)",
#             "(bool_or ?bool ?bool)",
#             "(bool_xor ?bool ?bool)",
#             "(not ?bool)",
#             # "(if ?bool ?bool ?bool)",
#             # "(app_bool_bool (λx -> ?bool) ?bool)",
#             # "(case ?int of O => ?bool | S => (λn -> ?bool))",
#             # "(Y{int,bool} (λrec xs -> ?bool) ?int)",
#             # "(Y{int,bool} (λrec xs -> ?bool) ?int)",
#         ],
#     ]

#     sym_of_type = [
#         # "list" => "?list",
#         # "int" => "?int",
#         "bool" => "?bool",
#     ]
#     start_expr_of_type = [
#         # "list" => "make_random_list",
#         # "int" => "make_random_digit",
#         "bool" => "(flip 0.5)",
#     ]
#     return Grammar(prods, sym_of_type, start_expr_of_type; size_dist=size_dist)
# end


# function make_sorted_list_task(; N=4)
#     sorted_list_program = "(scanlunit (λacc _ -> (+ (geometric 0.5) acc)) 0 8)"
#     examples = []
#     for i in 1:N
#         input = to_value(nothing) # input doesnt matter, just make it an empty list
#         output = sample_output(sorted_list_program)
#         push!(examples, IOExample([input], output))
#     end

#     task = PTask(:sorted_list, parse_type("unit -> list"), nothing, examples)

#     task_constrain = TaskConstrain(task, BDDEvalStateConfig(); temperature = 1.0)
#     max_ll = exp(task_constrain(sorted_list_program)[1])
#     @show max_ll
#     return task
# end

# function task_of_program(name::String, program::String, input_type::String, output_type::String; N=4)::Union{PTask, Nothing}
#     examples = []
#     for i in 1:N
#         input = to_value(nothing) # input doesnt matter, just make it an empty list
#         output = sample_output(program)
#         push!(examples, IOExample([input], output))
#     end

#     task = PTask(Symbol(name), parse_type("$input_type -> $output_type"), examples; solution=parse_expr(program))

#     task_constrain = TaskConstrain(task, BDDEvalStateConfig(); temperature = 1.0)

#     max_ll, stats = task_constrain(program)
#     hit_limit(pro)
#     # task.solution_loglikelihood = max_ll
#     return task
# end



function dots_defs()


    @define "float_of_int" "int -> float" "(Y (λ rec n -> (case n of O => 0.0 | S => (λn -> (fadd 1.0 (rec n))))))"
    @define "fround" "float -> int" "(Y (λ rec x -> (if (fless x 0.5) 0 (S (rec (fsub x 1.0))))))"

    # @define "discrete_noise" "(float -> float -> int)" """
    #     (λ x p resolution ->
    #         (let (noise (geom (fpow p (fdiv (float_of_int resolution) 2.))))
    #             (if (flip 0.5)
    #                 (+ (fround (fmul x (float_of_int resolution))) noise)
    #                 (- (fround (fmul x (float_of_int resolution))) noise)
    #             )
    #         )
    #     )
    # """

    # upscale [0, 1] floats to [0, resolution] ints
    @define "upscale" "float -> int -> int" "(λ x resolution -> (fround (fmul x (float_of_int resolution))))"

    @define "bidir_geom" "(float -> int -> int)" "(λ p x -> (if (flip 0.5) (+ (geom p) x) (- x (geom p))))"


    # (State x y angle speed time)
    define_type!(:state, Dict(:State => [:float, :float, :float, :float, :nat]))
    # (Action new_angle new_speed)
    define_type!(:action, Dict(:Action => [:float, :float]))
    define_type!(:observation, Dict(:Observation => [:int, :int]))


    # Streams

    # StreamResult = Stop | (Next Action k)
    define_type!(:sm_res, Dict(:Stop => Symbol[], :Next => [:action, :function]))

    @define sm_stop "(λs -> (Stop))"
    @define sm_once "(state -> action) -> (state -> sm_res)" "(λf -> (λs -> (Next (f s) sm_stop)))"
    @define sm_then "(Y (λrec sm1 sm2 -> (λs -> (case (sm1 s) of Stop => (sm2 s) | Next => (λa k1 -> (Next a (rec k1 sm2)))))))"
    @define sm_continue "(Y (λrec sm -> (sm_then sm (rec sm))))"
    @define sm_for "(Y (λrec sm n -> (λs -> (case n of O => (Stop) | S => (λn -> (sm_then sm (rec sm n)))))))"

    # Takes a dynamics function (state -> action -> state)
    # and a stream (state -> (Stop) | (Next action sm))
    # and returns a list of states
    @define sm_make """
        (Y (λrec dyn sm s -> (Cons s (case (sm s) of
                Stop => (Nil)
                Next => (λa next_sm -> (rec dyn next_sm (dyn s a)))
        ))))
    """


    # @define dynamics "(λstate action -> (State (fadd (fget_x state) action) (fadd (fget_y state) action) (fget_vx state) (fget_vy state) (fget_theta state)))"


    @define get_x "(λstate -> (case state of State => (λx y angle speed time -> x)))"
    @define get_y "(λstate -> (case state of State => (λx y angle speed time -> y)))"
    @define get_angle "(λstate -> (case state of State => (λx y angle speed time -> angle)))"
    @define get_speed "(λstate -> (case state of State => (λx y angle speed time -> speed)))"
    @define get_time "(λstate -> (case state of State => (λx y angle speed time -> time)))"

    @define obs_x "(λobs -> (case obs of Observation => (λx y -> x)))"
    @define obs_y "(λobs -> (case obs of Observation => (λx y -> y)))"

    @define stream """
        (λ init f -> (Cons init 
            ((Y (λrec acc ->
                (let (acc' (f acc))
                    (Cons acc' (rec acc'))
        ))) init)))
    """
    @define flatten "(Y (λrec xs -> (case xs of Nil => (Nil) | Cons => (λhd tl -> (append hd (rec tl))))))"



    # steps = 1

    @define dynamics "(λstate action -> (case state of State => (λx y _ _ time -> (case action of Action => (λnew_angle new_speed -> (State (fadd x (fmul new_speed (fcos new_angle))) (fadd y (fmul new_speed (fsin new_angle))) new_angle new_speed (S time)))))))"
    # @define run "(λpolicy init_state -> (Cons init_state (scanlunit (λstate _ -> (dynamics state (policy state))) init_state 20)))"
    @define run "(state -> action) -> State -> int -> list" "(λpolicy init_state T -> (take T (stream init_state (λstate -> (dynamics state (policy state))))))"

    @define sm_run "(state -> sm_res) -> State -> int -> list" "(λsm init_state T -> (take T (sm_make dynamics (sm_continue sm) init_state)))"

    # @define run_flatten "(λpolicy init_state -> (take 20 (flatten (stream init_state (λstate -> (dynamics state (policy state)))))))"





    @define tau "6.283185307179586"
    @define angles "(λn -> (map (λi -> (fdiv (fmul tau (float_of_int i)) (float_of_int n))) (range n)))"
    # uniform nat from 0 to n inclusive
    @define uniform_nat "(Y (λrec max -> (case max of O => 0 | S => (λn -> (if (flip (fdiv 1.0 (float_of_int (S max)))) 0 (S (rec n)))))))"

    @define uniform_index "(λxs -> (uniform_nat (dec (length xs))))"
    @define uniform_elem "(λxs -> (index (uniform_index xs) xs))"
    @define uniform_angle "(λn -> (uniform_elem (angles n)))"


    @define "angle" "int -> int -> float" "(λnum denom -> (fdiv (fmul tau (float_of_int num)) (float_of_int denom)))"
    @define "right" "(angle 0 1)"
    @define "left" "(angle 1 2)"
    @define "down" "(angle 1 4)"
    @define "up" "(angle 3 4)"

    @define "delta_y" "(λangle speed -> (fmul speed (fsin angle)))"
    @define "delta_x" "(λangle speed -> (fmul speed (fcos angle)))"


    @define observe_state "(λstate -> (Observation (fround (get_x state)) (fround (get_y state))))"
    @define observe_trajectory "list -> list" "(λtrajectory -> (map observe_state trajectory))"

    @define obs_eq "(λobs1 obs2 -> (and (== (obs_x obs1) (obs_x obs2)) (== (obs_y obs1) (obs_y obs2))))"

    # @define finally_and "(λx y -> (case x of FinallyTrue => y | FinallyFalse => (FinallyFalse) | Suspend => (λt -> (Suspend (finally_and t y))))))"

    @define suspended_and "(λx y -> (if x (Suspend y) false))"


    @define zip_with "(Y (λrec f xs ys -> (case xs of Nil => (Nil) | Cons => (λhd tl -> (case ys of Nil => (Nil) | Cons => (λhd2 tl2 -> (Cons (f hd hd2) (rec f tl tl2))))))))"
    @define all "(Y (λrec xs -> (case xs of Nil => true | Cons => (λhd tl -> (and hd (rec tl))))))"
    @define all_sus "(Y (λrec xs -> (case xs of Nil => true | Cons => (λhd tl -> (suspended_and hd (rec tl))))))"

    @define trajectory_obs_eq "(λt1 t2 -> (all (zip_with obs_eq t1 t2)))"
    @define trajectory_obs_eq_sus "(λt1 t2 -> (all_sus (zip_with obs_eq t1 t2)))"
    # @define trajectory_obs_eq "(λt1 t2 -> (all (zip_with obs_eq t1 t2)))"

    @define divisible "int -> int -> bool" "(λn m -> (== (mod n m) 0))"
    # @define affine "float -> float -> int -> float" "(λa b x -> (fadd a (fmul b (float_of_int x))))"
    @define uniform_range "int -> int -> int" "(λlo hi -> (+ (uniform_nat (hi - lo)) lo))"


    @define randspeed "float" "(float_of_int (uniform_nat 6))"
    # @define randangle "float" "((λn -> (angle (uniform_nat n) n)) (S (S (uniform_nat 3))))"
    # @define randangle "float" "(angle (uniform_nat 4) (S (uniform_nat 3)))"
    # @define randangle "float" "(angle $(make_uniform_nat_fast(16)) 16)"
    @define randangle "float" "(angle (uniform_nat 24) 24)"

    

    nothing
end



function dec7()

    dots_defs()


    # sample_output("(dynamics (State .5 .5 0. 0. 0) (Action 0. 4.))")




    # move on a grid or triangular grid
    # O(n):
    # program = "(run (λstate -> (Action (fadd (get_angle state) 0.25) 4.)) (State 0. 0. 0. 0. 0))"
    # O(n):
    # program = "(run (λstate -> (Action (if (flip 0.5) .5 0.) 4.)) (State 0. 0. 0. 0. 0))"

    # program = "(run (λstate -> (Action (if (flip 0.5) (fadd (get_angle state) .5) 0.) 4.)) (State 0. 0. 0. 0. 0))"


    square_triangle_mix = "(λstate -> (Action (if (flip 0.5) (uniform_angle (if (flip 0.5) 4 3)) (get_angle state)) 4.))"
    turning_right = "(λstate -> (Action (fadd (get_angle state) (if (flip 0.5) 0.5 0.)) 4.))"

    spider = """
        (let (dir (if (flip 0.5) .5 -.5))
            (λstate -> (Action (fadd (get_angle state) (if (flip 0.5) dir 0.)) (if (flip 0.5) 3. 5.))))"""

    # draw a box
    # program = """
    #     (run
    #         (λstate -> (Action
    #             (if (== (mod (get_time state) 6) 0) (fadd (fdiv tau 4.) (get_angle state)) (get_angle state))
    #                 4.))
    #         (State 32. 32. 0. 0. 0))"""

    box0 = """
        (λstate -> (Action
            (uniform_angle 4)
                1.))"""

    box1 = """
        (λstate -> (Action
            (if (flip 0.17) (uniform_angle 4) (get_angle state))
                1.))"""

    box2 = """
        (λstate -> (Action
            (if (flip 0.17) (fadd (fdiv tau 4.) (get_angle state)) (get_angle state))
                1.))"""

    # final box
    box3 = """
        (λstate -> (Action
            (if (== (mod (get_time state) 3) 0) (fadd (fdiv tau 4.) (get_angle state)) (get_angle state))
                2.))"""



    dots_programs = [
        # back and forth between two points
        """
        (λstate -> (Action
            (fadd (angle 1 2) (get_angle state))
            10.
        ))""",
        # vertical waves. We need to do some trig to get the speed right
        """
        (λstate ->
        (let (tt (mod (get_time state) 4))
        (Action
            (if (== tt 1) up
                (if (== tt 3) down
                    (angle 5 6)))
            (if (== tt 3) (fadd 4. (fmul -2. (delta_y (angle 5 6) 4.))) 4.)
        )))""",
        # left right zigzag
        """
        (λstate -> (Action
            (if (flip 0.2) (angle 5 12) (angle 1 12))
            4.
        ))""",

    ]

    randwalk = "(λstate -> (Action randangle randspeed))"

    straight = "(let (ang randangle) (λstate -> (Action ang 2.)))"

    # program = dots_programs[3]
    program = randwalk

    
    hypotheses = [box0, box1, box2, program]

    # program = "(λstate -> (Action randangle 2.))"
    # program = "(λstate -> (Action (if_float (flip 0.7) randangle (get_angle #1)) 2.))"
    # program = "(λstate -> (Action (if_float (divisible (get_time #1) 3) randangle (get_angle #1)) 2.0))"
    # program = "(λstate -> (Action (if_float (divisible (get_time #1) 3) (fadd (angle 1 4) (get_angle #1)) (get_angle #1)) 2.))"


    # program = "(λstate -> (Action (if_float (flip 0.3) (angle (uniform_nat 9) 4) (get_angle #1)) 2.0))"


    samples = []
    for i in 1:3
        # @time trajectory = sample_output_lazy("(run $program (State 8. 8. 0. 0. 0) 10)")

        # program = "(λstate -> (Action (fadd (get_angle state) 0.25) 4.))"

        @time trajectory = sample_output_lazy("(sm_run (sm_once $(program)) (State 8. 8. 0. 0. 0) 10)")

        # @time p = Pluck.get_true_result(bdd_forward("(trajectory_obs_eq (observe_trajectory $hypothesis) (observe_trajectory #1))"; env=Any[trajectory], show_bdd_size=false, record_json=false))


        # for (i, hypothesis) in enumerate(hypotheses)
        #     @time p = Pluck.get_true_result(bdd_forward("(trajectory_obs_eq (observe_trajectory $hypothesis) (observe_trajectory #1))"; env=Any[trajectory], show_bdd_size=false, record_json=false))
        #     println("hypothesis $i: $p")
        # end
        # @show bdd_forward("(obs_eq (car (observe_trajectory #1)) (car (observe_trajectory #1)))"; env=Any[trajectory])

        states = from_value(trajectory)
        res = []
        for state in states
            @assert state isa Value && state.constructor === :State
            push!(res, from_value.(state.args))
        end
        push!(samples, res)
    end

    json = Dict(
        "fields" => ["x", "y", "angle", "speed", "time"],
        "program" => program,
        "samples" => from_value.(samples),
        "width" => 16.,
        "height" => 16.,
    )

    # write to json
    dir = timestamp_dir()
    path = joinpath(dir, "samples.json")
    open(path, "w") do f
        JSON.print(f, json)
    end
    println("wrote samples to $path")
    println(webaddress("html/dots.html", path, false))
    # sample_output("(uniform_angle 3)")
end



function load_dots(path::String)
    open(path, "r") do f
        json = JSON.parse(f)
        program = json["program"]
        width = json["width"]
        height = json["height"]
        fields = json["fields"]
        get_field(state, field) = state[findfirst(x -> x == field, fields)]

        all_observations = []

        for trajectory in json["samples"]
            observations = []
            for state in trajectory
                x = to_value(round(Int, get_field(state, "x")))
                y = to_value(round(Int, get_field(state, "y")))
                push!(observations, Value(:Observation, x, y))
            end
            push!(all_observations, to_value(observations))
        end

        return all_observations
    end
end

function dec23()
    dots_defs()
    dots_grammar()

    all_observations = load_dots("out/results/2024-12-23/15-11-25/samples.json")
    observations = all_observations[1]
    jl_observations = from_value(observations)

    x0 = jl_observations[1].args[1]
    y0 = jl_observations[1].args[2]
    T = length(jl_observations)
    program = "(λstate -> (Action randangle randspeed))"


    program = "(observe_trajectory (run $program (State $x0. $y0. 0. 0. 0) $T))"

    # program = """
    # (observe_trajectory (run
    #     (λstate -> (Action
    #         (if (divisible (get_time state) 6) (fadd (angle 1 4) (get_angle state)) (get_angle state))
    #             4.))
    #     (State 32. 32. 0. 0. 0)))"""

    # @time println(Pluck.get_true_result(bdd_forward("(trajectory_obs_eq $program #1)"; env=Any[observations], show_bdd_size=true, record_json=false)))


    cfg = BDDEvalStateConfig()
    state = BDDEvalState(cfg)
    @time results, _, bdd = bdd_forward("(trajectory_obs_eq $program #1)"; env=Any[observations], show_bdd_size=true, return_bdd=true, manual_state=state)
    @show get_true_result(results)
    new_state = BDDEvalState(cfg)
    # swap them so we dont accidentally free the old weights and so we dont double-free either
    new_state.manager, state.manager = state.manager, new_state.manager
    new_state.weights, state.weights = state.weights, new_state.weights
    new_state.var_of_callstack = state.var_of_callstack
    new_state.sorted_callstacks = state.sorted_callstacks
    new_state.sorted_var_labels = state.sorted_var_labels
    new_state.BDD_TRUE = state.BDD_TRUE
    new_state.BDD_FALSE = state.BDD_FALSE

    # bdd = new_state.BDD_TRUE
    @time results, _, bdd = bdd_forward("(trajectory_obs_eq $program #1)";available_information = bdd, env=Any[observations], show_bdd_size=true, return_bdd=true, manual_state=new_state)
    @show get_true_result(results)


    # @define "finally" "(λb -> (if b (FinallyTrue) (FinallyFalse)))"

    # @time println(Pluck.get_true_result(bdd_forward_with_suspension("(trajectory_obs_eq_sus $program #1)" ; env=Any[observations])))

end

function swap_bdd_data!(dst, src)
    for field in [:manager, :weights, :var_of_callstack, :sorted_callstacks, :sorted_var_labels, :BDD_TRUE, :BDD_FALSE]
        dst_field = getfield(dst, field)
        src_field = getfield(src, field)
        setfield!(dst, field, src_field)
        setfield!(src, field, dst_field)
    end
end


function rerun(expr; kwargs...)
    cfg = BDDEvalStateConfig(; kwargs...)


    println("EMPTY")
    empty_state = BDDEvalState(cfg)
    @time results, _, bdd = bdd_forward(expr; show_bdd_size=true, return_bdd=true, manual_state=empty_state)
    p_empty = get_true_result(results)
    @show p_empty

    primed_state = BDDEvalState(cfg)
    swap_bdd_data!(primed_state, empty_state)
    println("PRIMED")
    @time results, _, bdd = bdd_forward(expr; show_bdd_size=true, return_bdd=true, manual_state=primed_state)
    p_primed = get_true_result(results)
    @show p_primed

    constrained_state = BDDEvalState(cfg)
    swap_bdd_data!(constrained_state, primed_state)
    println("PRIMED + CONSTRAINED")
    @time results, _, bdd = bdd_forward(expr; available_information=bdd, show_bdd_size=true, return_bdd=true, manual_state=constrained_state)
    p_constrained = get_true_result(results)
    @show p_constrained


    @assert isapprox(p_empty, p_primed)
    @assert isapprox(p_primed, p_constrained)
end




function dec24(mode=:mcmc)

    dots_defs()

    all_observations = load_dots("out/results/2024-12-23/15-11-25/samples.json")
    observations = all_observations[1]

    task = PTask(:box, parse_type("unit -> list"), [IOExample([Value(:Unit)], observations)])
    tasks = [task]
    # @show task.ios

    jl_observations = from_value(observations)
    x0 = from_value(jl_observations[1].args[1])
    y0 = from_value(jl_observations[1].args[2])
    T = length(jl_observations)


    max_depth=1000
    temperature=1.0
    mcmc_steps=2000
    repetitions=1
    time_limit=1.
    grammar = dots_grammar(;x0, y0, T)
    evaluate_solution = Pluck.train_only_evaluate_solution
    root_equality_fn = "trajectory_obs_eq"
    # root_equality_fn = "(observe_trajectory (run $program (State $x0. $y0. 0. 0. 0) $T))"
    kwargs_of_task = task -> (; time_limit, max_depth, root_equality_fn)
    eval_builder = make_tc(:bdd; kwargs_of_task, temperature, train_only=true)
    if mode === :mcmc
        cfg = MCMCConfig(; steps=mcmc_steps, pcfg=grammar, eval_builder, evaluate_solution)
    elseif mode === :smc
        cfg = SMCConfig(;pcfg=grammar, eval_builder, num_steps=8, num_particles=300)
    else
        error("invalid mode $mode")
    end



    # tc = eval_builder(task)
    # @show tc("(observe_trajectory (run (λstate -> (Action randangle randspeed)) (State 8.0 8.0 0.0 0.0 0) 10))"; cache=false)




    task_info = [Dict() for _ in tasks]

    gcfg = GroupConfig(; tasks, task_info, config=cfg, repetitions)
    GC.gc()
    res = solve_tasks(gcfg)

    addr = summary_address(res)
    printstyled("$addr\n", color=:yellow)
end



function dots_grammar(; x0=32.0, y0=32.0, T=20)
    x0 = Float64(x0)
    y0 = Float64(y0)

    dots_defs()

    # target = """
    # (run
    #     (λstate -> (Action
    #         (if (divisible (get_time state) 6)) (fadd (fdiv tau 4.) (get_angle state)) (get_angle state))
    #             4.))
    #     (State 32. 32. 0. 0. 0))"""

    @define if_float "bool -> float -> float -> float" "(λb x y -> (if b x y))"
    @define if_int "bool -> int -> int -> int" "(λb x y -> (if b x y))"

    wrap_policy(policy) = "(observe_trajectory (sm_run (sm_once $policy) (State $x0 $y0 0. 0. 0) $T))"


    prods = [
        "?program" => [wrap_policy("(λstate -> (Action ?float ?float))")],
        "?float" => ["?float_term" => 8, "?float_nonterm" => 2],
        "?float_term" => [
            "?constfloat",
            "(get_angle #1)",
            # "(get_speed state)",
            # "(get_x state)",
            # "(get_y state)",
            "randspeed",
            "randangle",
            "#float"
        ],
        "?constfloat" => [
            ["$f" for f in 0.0:1.0:10.0]...
        ],
        "?float_nonterm" => [
            "(angle ?int ?int)",
            # "(affine ?float ?float ?int)", # a + bx
            "(fadd ?float ?float)",
            # "(fadd (angle ?int ?int) (get_angle #1))", # "turn"
            # "(fmul ?float ?float)",
            # "(fdiv ?float ?float)",
            # "(fsub ?float ?float)",
            # "(fcos ?float)",
            # "(fsin ?float)",
            "(if_float ?bool ?float ?float)",
        ],
        "?int" => ["?int_term" => 8, "?int_nonterm" => 2],
        "?int_term" => [
            "#int",
            "?constint",
            "(get_time #1)",
            "?randint"
        ],
        "?randint" => [
            ["(uniform_nat $i)" for i in 0:9]...
            # ["(uniform_range $j $i)" for i in 0:9 for j in 0:i]...
        ],
        "?constint" => [
            ["$i" for i in 0:9]...
        ],
        "?int_nonterm" => [
            # "(inc ?int)",
            # "(dec ?int)",
            "(mod ?int ?int)",
            # "(if_int ?bool ?int ?int)",
        ],
        "?bool" => ["?bool_term" => 8, "?bool_nonterm" => 2],
        "?bool_term" => [
            "#bool",
            ["(flip 0.$i)" for i in 1:9]...,
            "true",
            "false"
        ],
        "?bool_nonterm" => [
            # "(fless ?float ?float)",
            # "(== ?int ?int)",
            # "(> ?int ?int)",
            "(divisible ?int ?int)",
        ],
    ]

    sym_of_type = [
        "float" => "?float",
        "int" => "?int",
        "bool" => "?bool",
        "list" => "?program"
    ]
    start_expr_of_type = [
        "list" => wrap_policy("(λstate -> (Action randangle randspeed))"),
        # "list" => "(mapunit (λx -> make_random_digit) $length)",
        # "list" => lets ? "(letII $(ints ? "randint" : "make_random_digit") (λk -> $start))" : start,
        # "list" => "(map (λx -> make_random_digit) (fill $length 0))",
    ]
    return Grammar(prods, sym_of_type, start_expr_of_type)
end





Pluck.synthesis_defs()
# map_scanl_int_grammar();
map_unit_grammar();

function more_defs()
    Pluck.synthesis_defs()
    @define map "(int -> int) -> list -> list" "(Y (λ rec f xs -> (case xs of Nil => (Nil) | Cons => (λhd tl -> (Cons (f hd) (rec f tl))))))"
    @define mapunit "(unit -> int) -> int -> list" "(λ f n -> (map f (fill n (Unit))))"
    @define "bool_and" "bool -> bool -> bool" "(λ x y -> (case x of True => y | False => false))"
    @define "bool_or" "bool -> bool -> bool" "(λ x y -> (case x of True => true | False => y))"
    @define "bool_xor" "bool -> bool -> bool" "(λ x y -> (case x of True => (not y) | False => y))"


    # @define fold "(Y (λrec xs init f -> (case xs of Nil => init | Cons => (λhd tl -> (f hd (rec tl init f))))))"
    @define foldl "(int -> int -> int) -> int -> list -> int" """
        (Y (λrec f acc xs ->
            (case xs of Nil => acc
                    | Cons => (λhd tl ->
                                (let (acc' (f acc hd))
                                    (rec f acc' tl)
                                ))
            )
        ))
    """
    @define scanl "(int -> int -> int) -> int -> list -> list" """
        (Y (λrec f acc xs ->
            (case xs of Nil => (Nil)
                    | Cons => (λhd tl ->
                                (let (acc' (f acc hd))
                                    (Cons acc' (rec f acc' tl))
                                ))
            )
        ))
    """

    @define scanlunit "(int -> unit -> int) -> int -> int -> list" "(λf init n -> (scanl f init (fill n (Unit))))"

    @define app_int_int "(int -> int) -> int -> int" "(λ f x -> (f x))"
    @define letII "int -> (int -> int) -> int" "(λ x f -> (f x))"

end