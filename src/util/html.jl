export ADDR,
    PORT,
    PUBLISH_DIR,
    PUBLISH_SITE,
    can_publish,
    write_out,
    webaddress,
    summary_address,
    new_summary,
    sync_html_folder,
    build_summary_entry,
    write_stub,
    build_stub,
    rebuild_stub,
    rebuild_stubs,
    new_stub,
    finish_stub!

using LibGit2

ADDR::String = "http://localhost"
PORT::Int = 8000

PUBLISH_DIR::String = "/afs/csail.mit.edu/u/m/mlbowers/public_html/proj/ctf/"
PUBLISH_SITE::String = "https://people.csail.mit.edu/mlbowers/proj/ctf/"
can_publish() = isdir(PUBLISH_DIR)


function write_html_dir(outdir; publish = false, verbose=false)
    publish = publish && can_publish()
    mkpath(outdir)
    path = joinpath(outdir, "html")
    Base.Filesystem.cptree("html", path)
    verbose && println("wrote $path")

    if publish
        publish_path = joinpath(PUBLISH_DIR, outdir, "html")
        try
            mkpath(dirname(publish_path))
            Base.Filesystem.cptree("html", publish_path)
            verbose && println("wrote $publish_path")
        catch e
            printstyled("failed to publish to $publish_path because of error:")
            showerror(stdout, e)
        end
    end
end

function write_out(json_data, path; browser_path = "html/search.html", publish = false, verbose = true, copy_html = false)
    publish = publish && can_publish()
    !endswith(path, ".json") && (path *= ".json")
    mkpath(dirname(path))
    open(path, "w") do f
        JSON.print(f, json_data)
    end
    verbose && println("wrote $path [$(round(Int,filesize(path)/1000)) KB]")
    if publish
        publish_path = joinpath(PUBLISH_DIR, path)
        try
            mkpath(dirname(publish_path))
            # Base.Filesystem.cp(path, publish_path; force=true) # commenting this out since it errors sometimes on sketch5
            open(publish_path, "w") do f
                JSON.print(f, json_data)
            end
            verbose && println("wrote $publish_path [$(round(Int,filesize(path)/1000)) KB]")
        catch e
            printstyled("failed to publish to $publish_path because of error:")
            showerror(stdout, e)
        end
    end
    # verbose && !isnothing(browser_path) && println(webaddress(browser_path, path, publish))
end

function webaddress(html_path, data_path, published)
    published ? "$PUBLISH_SITE$html_path?path=$data_path" :
    "$ADDR:$PORT/$html_path?path=$data_path"
end


function sync_html_folder()
    can_publish() || return
    try
        @assert PUBLISH_DIR != "" &&
                PUBLISH_DIR != "/" &&
                PUBLISH_DIR != "~" &&
                PUBLISH_DIR != "~/" &&
                PUBLISH_DIR != "*" &&
                PUBLISH_DIR != "/*"
        html_dst = joinpath(PUBLISH_DIR, "html")
        isdir(html_dst) && Base.Filesystem.rm(html_dst; recursive = true)
        Base.Filesystem.cptree("html", joinpath(PUBLISH_DIR, "html"))
    catch e
        printstyled("failed to publish to sync_html_folder() because of error:")
        showerror(stdout, e)
    end
end


function new_summary(config)
    stubs_of_task = []
    for task in config.tasks
        stubs = []
        for repetition = 1:config.repetitions
            name = replace(string(task.name), " " => "_") * "_" * string(repetition)
            path = name * ".json"
            stub_path = name * "_stub.json"
            evaltime_path = name * "_evaltime.json"
            stub = new_stub(config.out, stub_path, path, evaltime_path, get_strat(config.config), task, repetition)
            write_stub(stub; publish=config.publish, verbose=config.verbose)
            push!(stubs, stub)
        end
        push!(stubs_of_task, stubs)
    end
    summary_path = joinpath(config.out, "summary.json")
    # repo = LibGit2.GitRepo(".")
    summary = Dict(
        :out => config.out,
        :cmd => "disabled this field", # last(Base.active_repl.mistate.current_mode.hist.history),
        :pwd => pwd(),
        :hostname => gethostname(),
        :summary_path => "summary.json",
        :summary_address => webaddress("$(config.out)/html/summary.html", summary_path, config.publish && can_publish()),
        :init_stubs_of_task => stubs_of_task,
        :task_info => config.task_info,
        :timestamp => Dates.format(Dates.now(), "yyyy-mm-dd HH:MM:SS"),
        # :branch => string(LibGit2.headname(repo)),
        # :commit => LibGit2.head(".")[1:10],
        # :dirty => string(LibGit2.isdirty(repo)),
        :config => config.config,
        :strat => get_strat(config.config)
    )
    write_out(summary, summary_path; browser_path = "html/summary.html", publish = config.publish, verbose = config.verbose)
    # write_html_dir(config.out; publish=config.publish, verbose = config.verbose)
    # config.publish && sync_html_folder()
    summary
end

function summary_address(summary)
    webaddress("$(summary[:out])/html/summary.html", "summary.json", can_publish())
end

function new_stub(out, stub_path, path, evaltime_path, strat, task, repetition)
    Dict{Any, Any}(
        :out => out,
        :stub_path => stub_path,
        :path => path,
        :evaltime_path => evaltime_path,
        :strat => strat,
        :task => task,
        :repetition => repetition,
        :done => false,
        :result => nothing,
    )
end

write_stub(stub; publish=true, verbose=true) = write_out(stub, joinpath(stub[:out], stub[:stub_path]); browser_path = nothing, publish = publish, verbose=verbose)

function finish_stub!(res, stub)
    stub[:done] = true
    stub[:result] = short_json(res)
    stub
end



# function finish_stub_specific!(stub, data)

#     idx_of_field =
#         Dict(field => i for (i, field) in enumerate(data["graph"]["node_fields"]))

#     graph = data["graph"]
#     nodes = collect(values(graph["nodes"]))
#     best_likelihood = 0
#     best_posterior = 0
#     for node in nodes
#         if (node[idx_of_field["likelihood"]] > best_likelihood)
#             best_likelihood = node[idx_of_field["likelihood"]]
#         end
#         if (node[idx_of_field["posterior"]] > best_posterior)
#             best_posterior = node[idx_of_field["posterior"]]
#         end
#     end
#     stub[:task] = graph["task"]
#     stub[:expanded] =
#         length([node for node in nodes if !isempty(node[idx_of_field["children"]])])
#     stub[:evaluated] = length(nodes)
#     stub[:nonterminating_evals] = round(
#         Int,
#         length([node for node in nodes if !node[idx_of_field["terminated"]]]) / stub[:evaluated] *
#         100,
#     )
#     stub[:eval_time] = sum([node[idx_of_field["time"]] for node in nodes])
#     stub[:nonterminating_eval_time] = round(
#         Int,
#         sum([
#             node[idx_of_field["time"]] for
#             node in nodes if !node[idx_of_field["terminated"]]
#         ]) / stub[:eval_time] * 100,
#     )
#     stub[:best_likelihood] = best_likelihood
#     stub[:best_posterior] = best_posterior

#     stub
# end
