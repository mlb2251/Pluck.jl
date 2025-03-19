using Pluck
using JSON: JSON
using Dates: Dates
using BenchmarkTools
using ProgressBars
using Random

include("example_grammars.jl")

function load_joshrule(; path = "data/list_function_250/json")
    tasks = PTask[]
    for i ∈ 1:250
        id = 'c' * lpad(i, 3, '0') # 4 => "c004"
        task = load_tasks(
            "$path/$(id)_1.json";
            getios = j -> (([io["i"]], io["o"]) for io in j["data"][1:4]),
            getname = _ -> id,
            gettype = _ -> "list -> list",
            getsolution = _ -> nothing,
        )
        @assert length(task) <= 1
        isempty(task) && continue
        push!(tasks, task[1])
    end
    tasks
end

origami_graph_root(type::String) = origami_graph_root(parse_type(type))
function origami_graph_root(type)
    ret_ty = return_type(type)
    last_arg_ty = arg_types(type)[end] # ie what will be bound to #1 at the top level
    if ret_ty == BaseType(:list)
        return parse_expr("(Y{$last_arg_ty,$ret_ty} (λ_->(λ_->make_random_list)) #1)")
    elseif ret_ty == BaseType(:int)
        return parse_expr("(Y{$last_arg_ty,$ret_ty} (λ_->(λ_->make_random_digit)) #1)")
    end
    error("unexpected type for ret_ty: $ret_ty")
end


mcmc_alex_list_ppcfg(; kwargs...) = MCMCConfig(
    cfg = alex_list_ppcfg(),
    kwargs...,
)

mcmc_rational_rules(; kwargs...) = MCMCConfig(
    cfg = rational_rules_ppcfg(),
    check_solved = e -> getchild(e, 2),
    kwargs...,
)


smc_alex_list_ppcfg(; kwargs...) = SMCConfig(;
    pcfg = alex_list_ppcfg(),
    temperature = 1.0,
    kwargs...,
)

Base.@kwdef struct GroupConfig
    config = smc_alex_list_ppcfg()
    tasks::Vector{PTask} = load_joshrule()[1:80]
    task_info::Vector{Dict} = []
    repetitions::Int = 1
    # temperatures::Vector{Float64} = [1.0]
    out::String = joinpath(timestamp_dir(), "expt")
    verbose::Bool = false
    publish::Bool = false
    warmstart::Bool = true
    warmstart_only::Bool = false
    is_warmstart::Bool = false
end
JSON.lower(x::GroupConfig) = Dict(:num_tasks => length(x.tasks), :repetitions => x.repetitions, :config => x.config)
Base.show(io::IO, x::GroupConfig) = print(io, "GroupConfig($(length(x.tasks)), $(x.repetitions), $(x.config))")

function Pluck.warmstart_config(x::GroupConfig)
    GroupConfig(
        warmstart_config(x.config),
        x.tasks[1:min(3, length(x.tasks))],
        x.task_info[1:min(3, length(x.task_info))],
        1, # repetitions
        joinpath("out/warmstart/", x.out),
        false,
        false,
        false,
        false,
        true,
    )
end

function solve_tasks(config::GroupConfig)

    if config.warmstart
        printstyled("WARMSTARTING\n", color = :yellow)
        solve_tasks(warmstart_config(config))
        printstyled("WARMSTARTING DONE\n", color = :yellow)
        config.warmstart_only && return
    end

    config.is_warmstart || printstyled("STARTING\n", color = :green)

    summary = new_summary(config)
    config.is_warmstart || printstyled("Solving $(length(config.tasks)) tasks $(config.repetitions) times each with $(Threads.nthreads()) threads\n", color = :blue)
    config.is_warmstart || printstyled(summary_address(summary); color = :yellow)
    config.is_warmstart || println("")

    # shuffle workloads for hopes of more even distribution over cpus
    num_workloads = length(config.tasks) * config.repetitions
    # workloads::Vector{Int} = Random.shuffle!(collect(1:num_workloads))
    workloads::Vector{Tuple{Int, Int}} = collect(enumerate(1:num_workloads))
    progress = ProgressBar(workloads)
    # progress = workloads

    tstart = time()

    # task_constrains = TaskConstrain[]

    tdds = [TimeDataDict() for _ in 1:length(workloads)]
    # @maybethreads for i_j in progress
    function process(idx, i_j)
        task_idx = (i_j - 1) ÷ config.repetitions + 1
        rep_idx = (i_j - 1) % config.repetitions + 1
        task = config.tasks[task_idx]
        # task_info = config.task_info[task_idx]
        # println("Start $(Threads.threadid()) $(task.name) $rep_idx")
        try
            stub = copy(summary[:init_stubs_of_task][task_idx][rep_idx])
            config.verbose && println("[$(task.name) $rep_idx] Starting")
            res = solve_task(config.config, task)
            config.verbose && println("[$(task.name) $rep_idx] Done")
            tdd = tdds[idx]
            for r in res
                add_timing_data!(tdd, r.tdd)
            end
            # config.verbose && println(config.out)
            config.verbose && is_solved(res) && printstyled("[$(task.name) $rep_idx] solved\n", color = :green)
            write_out(res, joinpath(stub[:out], stub[:path]); browser_path = html_path(config.config), verbose = config.verbose)
            # write_out(get_task_constrain_fn(res), stub[:evaltime_path]; browser_path="html/evaltime.html", verbose=config.verbose)
            write_stub(finish_stub!(res, stub); publish = config.publish, verbose = config.verbose)
            config.verbose && println(summary_address(summary))
            config.verbose && println("") # necessary bc the next printed line will get eaten by the progress bar
        catch e
            print("[$(task.name) $rep_idx] ERROR: ")
            showerror(stdout, e)
            println()
            println()
            Pluck.SINGLE_THREAD && rethrow()
            e isa InterruptException && rethrow()
        end
        # println("End $(Threads.threadid()) $(task.name) $rep_idx")
    end


    if !Pluck.SINGLE_THREAD && config.config isa MCMCConfig
        Threads.@threads :greedy for idx__i_j in progress
            process(idx__i_j[1], idx__i_j[2])
        end
    else
        for (idx, i_j) in progress
            process(idx, i_j)
        end
    end

    # launch_workers(workloads) do idx__i_j, worker_id, worker_state
    #     process(idx__i_j[1], idx__i_j[2])
    # end

    tdd = TimeDataDict()
    for tdd_inner in tdds
        add_timing_data!(tdd, tdd_inner)
    end


    dt = time() - tstart
    println("dt: ", round(Int, dt), "s")
    println(tdd)
    summary[:tdd] = string(tdd)
    summary[:dt] = dt
    write_out(summary, joinpath(config.out, summary[:summary_path]); browser_path = "html/summary.html", publish = config.publish, verbose = config.verbose)
    # config.publish && sync_html_folder()
    config.is_warmstart || !config.publish || println("View results at ", summary_address(summary))


    # comparison = Vector{@NamedTuple{expr, task, constrain_ll, bdd_ll, constrain_stats, bdd_stats, abs_diff, rel_diff}}()

    # for tc_constrain in task_constrains
    #     task = tc_constrain.task
    #     println(task.name)
    #     # tc_bdd = TaskConstrain(task, BDDEvalState(; time_limit = 0.))
    #     for (expr, (ll, stats)) in tc_constrain.cache
    #         hit_limit(stats) && continue
    #         # rerun the constrain to be more fair to it, since we'll be warmstarting bdd
    #         print(expr)
    #         print(".")
    #         constrain_ll, constrain_stats = task_constrain(expr, task, EvalState(config.config.eval_config))
    #         hit_limit(constrain_stats) && continue
    #         # warmstart bdd
    #         print(".")
    #         task_constrain(expr, task, BDDEvalState(; time_limit = 0., use_strict_order=false))
    #         # run bdd
    #         print(".")
    #         bdd_ll, bdd_stats = task_constrain(expr, task, BDDEvalState(; time_limit = 0., use_strict_order=false))
    #         abs_diff = bdd_stats.time - constrain_stats.time
    #         rel_diff = bdd_stats.time / constrain_stats.time
    #         push!(comparison, (expr = expr, task = task, constrain_ll = constrain_ll, bdd_ll = bdd_ll, constrain_stats = constrain_stats, bdd_stats = bdd_stats, abs_diff = abs_diff, rel_diff = rel_diff))
    #         println()
    #     end
    # end

    # filter!(c -> c.bdd_stats.time > .01, comparison)
    # filter!(c -> c.abs_diff > .001, comparison)
    # filter!(c -> c.rel_diff > 1.2, comparison)

    # println("rel diff")
    # sort!(comparison, rev=true, by = c -> c.rel_diff)
    # for c in comparison[1:min(40, length(comparison))]
    #     println("$(round(c.rel_diff, sigdigits = 2)) $(round(c.abs_diff, sigdigits = 2)) $(c.expr) $(c.task.name)")
    # end
    # println("abs diff")
    # sort!(comparison, rev=true, by = c -> c.abs_diff)
    # for c in comparison[1:min(40, length(comparison))]
    #     println("$(round(c.abs_diff, sigdigits = 2)) $(round(c.rel_diff, sigdigits = 2)) $(c.expr) $(c.task.name)")
    # end
    

    # return comparison




    return summary
end

function tt()
    Pluck.synthesis_defs()
    task = load_joshrule()[24]

    jl_output = [6, 5, 7, 1, 3, 5, 6, 9, 0, 4, 3, 6, 5, 7, 1, 3, 5, 6, 9, 0, 4, 3]
    output = Pluck.make_list_from_julia_list(jl_output)
    # program = "make_random_list"
    program = "(append make_random_list make_random_list)"


    # program = "(append make_random_list (Nil))"
    # program = "(case (flip 0.2) of True => make_random_list | False => make_random_list)"
    # program = "(append make_random_list (append_one make_random_list make_random_digit))"

    println("bdd")
    for i in 1:1
        # (res, stats) = task_constrain("make_random_list", task)
        @btime bdd_forward("(old_list_eq $($program) $($output))"; state = BDDEvalState(;use_thunk_unions=true, use_thunk_cache=false, use_strict_order=false))
        # println(stats.time)
        #   5.153 ms (63520 allocations: 4.98 MiB)
    end

    for i in 1:1
        # (res, stats) = task_constrain("make_random_list", task, EvalState())
        @assert !hit_limit(constrain("(old_list_eq $program $output)", [], true, EvalState(;eval_limit=1000000000))[2].stats)
        
        println("spe")
        @btime constrain("$($program)", [], $jl_output)
        println("spe with old_list_eq")
        @btime constrain("(old_list_eq $($program) $($output))", [], true, EvalState(;eval_limit=1000000000))

        # @assert !hit_limit(stats)
        # println(stats.time)

        #   359.583 μs (10608 allocations: 373.64 KiB)
    end

end


# function sweep_configs_smc(;
#     base_reps=4, exponent=7,
#     start=parse_expr("make_random_list"),
#     pcfg=alex_list_ppcfg(),
#     tasks=load_joshrule()[1:80]
# )
#     rejuv_steps = 0
#     time_limit = 0.01
#     num_steps = 12
#     configs = GroupConfig[]
#     for i in 1:exponent
#         num_particles = base_reps * 2^i
#         repetitions = base_reps * 2^(exponent - i)
#         println("num_particles: ", num_particles, " repetitions: ", repetitions, " num_steps: ", num_steps, " -> evals: ", num_steps * num_particles * repetitions)
#         cfg = GroupConfig(tasks=tasks, repetitions=repetitions, config=SMCConfig(; pcfg=pcfg, start=start, num_particles=num_particles, num_steps=num_steps, rejuv_steps=rejuv_steps, eval_config=EvalConfig(; time_limit=time_limit)))
#         push!(configs, cfg)
#     end
#     configs
# end

# function sweep_configs_mcmc(;
#     base_reps=4, exponent=7,
#     start=parse_expr("make_random_list"),
#     pcfg=alex_list_ppcfg(),
#     tasks=load_joshrule()[1:80]
# )
#     rejuv_steps = 0
#     time_limit = 0.01
#     configs = GroupConfig[]
#     for i in 1:exponent
#         steps = 12 * base_reps * 2^i
#         repetitions = base_reps * 2^(exponent - i)
#         println("steps: ", steps, " repetitions: ", repetitions, " -> evals: ", steps * repetitions)
#         cfg = GroupConfig(tasks=tasks, repetitions=repetitions, config=MCMCConfig(; cfg=pcfg, start=start, steps=steps, eval_config=EvalConfig(; time_limit=time_limit)))
#         push!(configs, cfg)
#     end
#     configs
# end

function poster_configs(; divby::Int = 1, repetitions = 3)
    time_limit = 0.01
    tasks = load_joshrule()[1:80]
    smc_particles = div(300, divby)
    mcmc_steps = div(7000, divby)

    configs_base = GroupConfig[
        # rich SMC
        GroupConfig(
            tasks = tasks,
            repetitions = repetitions,
            config = SMCConfig(; pcfg = alex_list_ppcfg(), start = parse_expr("make_random_list"), num_particles = smc_particles, num_steps = 12, rejuv_steps = 0, eval_config = EvalConfig(; time_limit = time_limit)),
        ),
        # rich MCMC
        GroupConfig(tasks = tasks, repetitions = repetitions, config = MCMCConfig(; cfg = alex_list_ppcfg(), start = parse_expr("make_random_list"), steps = mcmc_steps, eval_config = EvalConfig(; time_limit = time_limit))),
    ]
    configs_output_noise = GroupConfig[
        # rational rules SMC
        GroupConfig(
            tasks = tasks,
            repetitions = repetitions,
            config = SMCConfig(;
                pcfg = rational_rules_ppcfg(),
                start = parse_expr("(perturb make_nil)"),
                num_particles = smc_particles,
                num_steps = 12,
                rejuv_steps = 0,
                eval_config = EvalConfig(; time_limit = time_limit),
                check_solved = e -> getchild(e, 2),
                proposal = rational_rules_ctf,
            ),
        ),
        # rational rules MCMC
        GroupConfig(
            tasks = tasks,
            repetitions = repetitions,
            config = MCMCConfig(; cfg = rational_rules_ppcfg(), start = parse_expr("(perturb make_nil)"), steps = mcmc_steps, eval_config = EvalConfig(; time_limit = time_limit), check_solved = e -> getchild(e, 2)),
        ),
    ]

    configs_core = GroupConfig[
        # core SMC
        GroupConfig(
            tasks = tasks,
            repetitions = repetitions,
            config = SMCConfig(; pcfg = joshrule_ppcfg(), start = parse_expr("make_random_list"), num_particles = smc_particles, num_steps = 12, rejuv_steps = 0, eval_config = EvalConfig(; time_limit = time_limit)),
        ),
        # ? rational rules SMC
        # core MCMC
        GroupConfig(tasks = tasks, repetitions = repetitions, config = MCMCConfig(; cfg = joshrule_ppcfg(), start = parse_expr("make_random_list"), steps = mcmc_steps, eval_config = EvalConfig(; time_limit = time_limit))),
        # ? rational rules MCMC
    ]
    (base = configs_base, noise = configs_output_noise, core = configs_core)
end



function sweep(configs::Vector{GroupConfig}; warmstart_only = false)
    sweep_path = joinpath(timestamp_dir(), "sweep.json")

    result = Dict(
        :sweep_path => sweep_path,
        :configs => configs,
        :summaries => [],
        :times => [],
        :pending => length(configs),
    )

    write_out(result, sweep_path; browser_path = "html/sweep.html", publish = false, verbose = false)
    println(sweep_path)

    for cfg in configs
        @show cfg
        GC.gc()
        tstart = time()
        summary = solve_tasks(cfg)
        push!(result[:summaries], summary)
        dt = time() - tstart
        push!(result[:times], dt)
        result[:pending] -= 1
        write_out(result, sweep_path; browser_path = "html/sweep.html", publish = false, verbose = false)
        println(sweep_path)
    end

    println("rsync -avz --mkpath  s5:/scratch/mlbowers/proj/julia/coarse-to-fine-synthesis/$sweep_path ~/proj/julia/coarse-to-fine-synthesis/$sweep_path")
    println("http://localhost:8001/html/sweep.html?path=$sweep_path")

    # for (i,summary) in enumerate(result[:summaries])
    #     println(i, " => ", summary_address(summary))
    # end

    result
end

function collect_results(; path = "out/results/2024-08-09/15-41-58/expt/summary.json")
    summary = open(f -> JSON.parse(f), path)

    solns_of_task = Dict{String, Vector{Dict}}()
    attempts_of_task = Dict{String, Int}()

    for task_stubs in ProgressBar(summary["init_stubs_of_task"])
        task = task_stubs[1]["task"]
        solns_of_task[task["name"]] = Vector{Dict}()
        attempts_of_task[task["name"]] = 0
        for stub in task_stubs
            path = joinpath(stub["out"], stub["stub_path"])
            stub = open(f -> JSON.parse(f), path)
            if stub["done"]
                @assert length(stub["result"]) == 1
                result = stub["result"][1]
                attempts_of_task[task["name"]] += 1
                if result["solved"]
                    push!(solns_of_task[task["name"]],
                        Dict(
                            :path => path,
                            :best_likelihood_expr => result["best_likelihood_expr"],
                            :best_posterior_expr => result["best_posterior_expr"],
                            :likelihood => result["best_likelihood"],
                            :posterior => result["best_posterior"],
                        ))
                end
            end
        end
    end
    collected_path = joinpath(dirname(path), "collected.json")
    write_out(Dict(:solns_of_task => solns_of_task, :attempts_of_task => attempts_of_task), collected_path; browser_path = "html/collected.html", publish = false, verbose = false)
    println(collected_path)
end



function stitch(; path = "out/results/2024-08-09/15-41-58/expt/collected.json")
    collected = open(f -> JSON.parse(f), path)

    solns_of_task = collected["solns_of_task"]
    attempts_of_task = collected["attempts_of_task"]

    for (task, solns) in solns_of_task
        num_solns = length(solns)
        solve_rate = num_solns / attempts_of_task[task]
        # fixed length string version
        task_padded = rpad(task, 20)
        println("$task_padded $(lpad(num_solns,2))/$(attempts_of_task[task]) ($(round3(solve_rate * 100))%)")
    end

    println("Recompiling stitch...")
    STITCH_DIR = "/Users/maddy/proj/rust/stitch"
    STITCH_BIN = joinpath(STITCH_DIR, "target/release/compress")
    run(Cmd(`cargo build --release`, dir = STITCH_DIR))

    # build an input file for stitch
    programs_by_task = []
    for (task, solns) in solns_of_task
        length(solns) == 0 && continue
        best_posterior = maximum([soln["posterior"] for soln in solns])
        solns = [soln for soln in solns if soln["posterior"] == best_posterior]
        push!(programs_by_task, Dict(
            :task => task,
            :programs => [replace(stitch_str(parse_expr(replace(soln["best_posterior_expr"]))), "Y{list,list}" => "Y") for soln in solns],
        ))
    end

    # pretend we solved "sum"
    # push!(programs_by_task, Dict(:task => "sum", :programs => [raw"((Y (lam (lam (case{Nil,Cons} $0 0 (lam (lam (+ $1 ($3 $0)))))))) $0)"]))
    push!(programs_by_task, Dict(:task => "length", :programs => [raw"((Y (lam (lam (case{Nil,Cons} $0 0 (lam (lam (+ 1 ($3 $0)))))))) $0)"]))
    # push!(programs_by_task, Dict(:task => "length2", :programs => [raw"((Y (lam (lam (case{Nil,Cons} $0 0 (lam (lam (+ 2 ($3 $0)))))))) $0)"]))
    # push!(programs_by_task, Dict(:task => "length3", :programs => [raw"((Y (lam (lam (case{Nil,Cons} $0 0 (lam (lam (- 2 ($3 $0)))))))) $0)"]))

    # filter!(programs_by_task) do x
    #     occursin("map", x[:task]) || occursin("append", x[:task]) || occursin("sum", x[:task]) || occursin("length", x[:task])
    # end
    @show programs_by_task


    input_path = joinpath(dirname(path), "stitch_input.json")
    open(f -> JSON.print(f, programs_by_task), input_path, "w")
    println(input_path)

    #  --eta-long
    run(Cmd(`$STITCH_BIN $input_path --show-rewritten -i1 --structure-penalty=1.5 --utility-by-rewrite -a4 --context-threading --fmt=programs-by-task`, env = ("RUST_BACKTRACE" => "1",)))

end




# function run_stitch()





# function test_prio(;
#     root=parse_expr("make_random_list"),
#     task=load_tasks("data/lafi_task.json")[1],
#     cfg=lafi_cfg(),
#     out=joinpath(timestamp_dir(), string(task.name) * ".json"),
#     stub_out=nothing,
#     eval_state=EvalState(; time_limit=0.005),
#     steps=50,
#     verbose=false,
#     save=true,
#     strat=:enum,
# )
#     # warmstart constrain
#     # constrain("make_random_list", [], [1,2,3,4])
#     task_constrain(parse_expr("make_random_list"), load_tasks("data/lafi_task.json")[1])

#     g = Graph(root, cfg, task, eval_state)
#     eval_node!(g.nodes[g.root.eid], g)
#     # @assert g.nodes[g.root.eid].likelihood > 0.0
#     strat = if strat === :enum
#         EnumerativeSearch(
#             g;
#             follow=false,
#             do_eval=true,
#             choose_fn=ChoosePosterior(g),
#             max_steps=steps,
#         )
#     elseif strat === :sample10
#         EnumerativeSearch(
#             g;
#             follow=false,
#             do_eval=true,
#             choose_fn=SamplePosterior(g, 10),
#             max_steps=steps,
#         )
#     elseif strat === :sample1
#         EnumerativeSearch(
#             g;
#             follow=false,
#             do_eval=true,
#             choose_fn=SamplePosterior(g, 1),
#             max_steps=steps,
#         )
#     elseif strat === :smc
#         SMCSearch(
#             (options, strategy, g) ->
#                 [exp(log(node.posterior) / 10) for (node, prod) in options],
#             g,
#             task,
#             steps,
#             15,
#             cfg,
#         )
#     else
#         error("unrecognized strat")
#     end

#     full_search(strat)

#     return strat
# end

# function test_sample()
#     env = PType[parse_type("list")]
#     pcfg = alex_list_pcfg()
#     for i = 1:200
#         e, logprob = sample_expr(pcfg, parse_type("list"), env, AuxCFGSymbol(:list))
#         marginal_logprob = logprior_expr(pcfg, e, parse_type("list"), env, AuxCFGSymbol(:list))
#         if !pcfg.ambiguous
#             # this check is already done internally by sample_expr btw but just
#             # written here to show off the equivalence
#             @assert !is_ambiguous(derivations(pcfg, e, parse_type("list"), env, AuxCFGSymbol(:list)))
#             @assert logprob ≈ marginal_logprob
#         end

#         @assert is_closed(e, parse_type("list"), env)

#         println(round3(exp(logprob)), " ", e)
#     end
# end

