using Profile
# using SnoopCompile
using FlameGraphs
using Dates
export @prof
using JSON

macro prof(ex)
    return quote
        Profile.clear()
        @time @profile $(esc(ex))
        data, ldata = Profile.retrieve()
        write_prof(data, ldata)
    end
end

# macro prof_inf(ex)
#     return quote
#         Profile.clear()
#         @time tinf = @snoopi_deep $(esc(ex))
#         data, ldata = Profile.retrieve()
#         write_prof(data, ldata)
#     end
# end

function write_prof(data, ldata; outdir = "out/flamegraphs")
    mkpath(outdir)
    timestamp = Dates.format(now(), "yyyy-mm-dd_HH-MM-SS")
    out = joinpath(outdir, "flamegraph_$timestamp.json")
    while isfile(out)
        timestamp *= "_"
        out = joinpath(outdir, "flamegraph_$timestamp.json")
    end

    print("Flamegraph: building from $(length(data)) samples... ")
    flame = flamegraph(
        data;
        lidict = ldata,
        C = true,
        combine = true,
        # recur = :flat,
        norepl = true,
        pruned = FlameGraphs.defaultpruned,
        filter = nothing,
        threads = nothing,
        tasks = nothing,
    )

    print("writing with $(flame_size(flame)) nodes... ")
    open(out, "w") do io
        JSON.print(io, to_json(flame))
    end
    println("wrote $ADDR:$PORT/html/prof.html?path=$out")
end

function flame_size(flame)
    total = 1
    for child in flame
        total += flame_size(child)
    end
    total
end

function to_json(flame)::Dict{Symbol, Any}
    fields = [
        :runtime_dispatch,
        :gc_event,
        :repl,
        :start,
        :stop,
        :func,
        :file,
        :fullpath,
        :line,
        :from_c,
        :inlined,
        :types,
        :children,
    ]
    Dict(:fields => fields, :data => to_json_inner(flame))
end

function to_json_inner(flame)::Vector{Any}

    children = map(to_json_inner, flame)

    data = flame.data
    sf = data.sf
    linfo = sf.linfo
    types =
        linfo isa Core.MethodInstance ? map(string, linfo.specTypes.types[2:end]) : String[]

    Any[
        data.status&FlameGraphs.runtime_dispatch,
        data.status&FlameGraphs.gc_event,
        data.status&FlameGraphs.repl,
        first(data.span),
        last(data.span),
        sf.func,
        basename(string(sf.file)),
        string(sf.file),
        sf.line,
        sf.from_c ? 1 : 0,
        sf.inlined ? 1 : 0,
        types,
        children,
    ]
end
