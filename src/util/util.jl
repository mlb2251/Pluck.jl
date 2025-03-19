export logaddexp,
    sample,
    logsubexp,
    AssocList,
    prepend,
    head,
    add_timing_data!,
    tail,
    find,
    timestamp_dir,
    round3,
    write_out,
    webaddress,
    sync_html_folder,
    build_summary,
    rebuild_summaries,
    rebuild_summary,
    can_publish,
    TimeDataDict,
    round2,
    round1,
    round0,
    @maybethreads,
    CacheStats,
    hit!,
    miss!,
    merge_stats,
    logsumexp,
    RegionAlloc,
    @single_thread,
    launch_workers,
    nothreads
using AutoHashEquals

function logaddexp(x::Float64, y::Float64)::Float64
    # @assert (x <= 0 || isapprox(x, 0; atol=2 * eps())) &&
    #         (y <= 0 || isapprox(y, 0; atol=2 * eps())) "logaddexp only works for negative numbers, got x=$x, y=$y"
    if x == -Inf
        return y
    elseif y == -Inf
        return x
    else
        # Numerically stable implementation
        res = max(x, y) + log1p(exp(-abs(x - y)))
        return (res > 0.0 && isapprox(res, 0.0; atol = eps(1.0))) ? 0.0 : res
    end
end

logsumexp(x::Vector{Float64}) = reduce(logaddexp, x; init = -Inf)


function logsubexp(x, y)
    @assert x <= 0 && y <= 0
    @assert x >= y
    x == -Inf && return -Inf
    # Either of these are fine numerically I think
    # return x + log1p(-exp(y - x))
    return x + log(-expm1(y - x))
end

"""
log(1 - exp(-|x|))
"""
# function log1m(x)
#     x < np.log(2), tf.math.log(-tf.math.expm1(-x)),
#     tf.math.log1p(-tf.math.exp(-x)))
# end

"""
Derivation:
log(exp(x) + exp(y))

abs(x-y) + min(x,y) = max(x,y)

"""


# Adapted from Combinatorics.jl
struct Combinations
    n::Int
    t::Int
end

function Base.iterate(c::Combinations, s = [min(c.t - 1, i) for i ∈ 1:c.t])
    if c.t == 0 # special case to generate 1 result for t==0
        isempty(s) && return (s, [1])
        return
    end
    for i ∈ c.t:-1:1
        s[i] += 1
        if s[i] > (c.n - (c.t - i))
            continue
        end
        for j ∈ i+1:c.t
            s[j] = s[j-1] + 1
        end
        break
    end
    s[1] > c.n - c.t + 1 && return
    (s, s)
end

Base.length(c::Combinations) = binomial(c.n, c.t)

Base.eltype(::Type{Combinations}) = Vector{Int}

"""
combinations(n, k)

Generate all combinations of `t` elements

This has been modified from the Combinatorics.jl package to
re-use the same allocation for each combination instead of reallocating each time.
We also return the result as a vector of booleans
"""
function combinations(n, t)
    # this one closured boolvec allocation will be re-used for each combination
    boolvec = [false for i ∈ 1:n]
    function as_boolvec(c)
        fill!(boolvec, false)
        for i in c
            boolvec[i] = true
        end
        boolvec
    end
    (as_boolvec(c) for c in Combinations(n, t))
end


# struct AssocListNil end

# struct AssocList{T} where T
#     val :: T
#     next :: Union{AssocList{T}, Nothing}
# end

struct AssocList{T}
    inner::Union{Nothing, Tuple{T, AssocList{T}}}
end
Base.eltype(::Type{AssocList{T}}) where {T} = T

function Base.:(==)(l1::AssocList{T}, l2::AssocList{T}) where {T}
    while !isempty(l1) && !isempty(l2)
        head(l1) != head(l2) && return false
        l1 = tail(l1)
        l2 = tail(l2)
    end
    isempty(l1) && isempty(l2)
end

function Base.hash(l::AssocList{T}, h::UInt) where {T}
    while !isempty(l)
        h = hash(head(l), h)
        l = tail(l)
    end
    h
end


AssocList{T}() where {T} = AssocList{T}(nothing)

function Base.show(io::IO, l::AssocList)
    print(io, "[")
    while !isempty(l)
        print(io, head(l))
        l = tail(l)
        !isempty(l) && print(io, ", ")
    end
    print(io, "]")
end

@inline Base.isempty(l::AssocList) = isnothing(l.inner)

@inline function head(l::AssocList{T})::T where {T}
    isempty(l) && error("Empty list")
    l.inner[1]
end

@inline function tail(l::AssocList{T})::AssocList{T} where {T}
    isempty(l) && error("Empty list")
    l.inner[2]
end

function Base.getindex(l::AssocList{T}, idx)::T where {T}
    while idx > 1
        l = tail(l)
        idx -= 1
    end
    head(l)
end
function Base.length(l::AssocList)::Int
    len = 0
    while !isempty(l)
        len += 1
        l = tail(l)
    end
    len
end

function find(f::F, l::AssocList{T}) where {F <: Function, T}
    while !isempty(l)
        hd = head(l)
        f(hd) && return hd
        l = tail(l)
    end
    nothing
end

prepend(val::T, l::AssocList{T}) where {T} = AssocList((val, l))

function timestamp_dir(; base = "out/results")
    date = Dates.format(Dates.now(), "yyyy-mm-dd")
    time = Dates.format(Dates.now(), "HH-MM-SS")
    dir = nothing
    i = 0
    while isnothing(dir) || isdir(dir)
        padded_i = lpad(i, 3, '0')
        dir = joinpath(base, date, "$time-$padded_i")
        i += 1
    end
    mkpath(dir)
    while !isdir(dir)
        # wait for dir to be created
    end
    dir
end

round3(x) = round(x; sigdigits = 3)
round2(x) = round(x; sigdigits = 2)
round1(x) = round(x; sigdigits = 1)
round0(x) = round(x; sigdigits = 0)

"""
adapted from StatsBase.sample(); samples an index from `weights`
with probability proportional to the weight at that index
"""
function sample(weights)
    t = rand() * sum(weights)
    n = length(weights)
    i = 1
    cw = weights[1]
    while cw < t && i < n
        i += 1
        @inbounds cw += weights[i]
    end
    return i
end

SINGLE_THREAD::Bool = false

function nothreads(value=!SINGLE_THREAD)
    global SINGLE_THREAD = value
    println("SINGLE_THREAD = $SINGLE_THREAD")
    SINGLE_THREAD
end


macro single_thread(e)
    global SINGLE_THREAD = true
    quote
        $(esc(e))
    end
end
macro many_threads(e)
    global SINGLE_THREAD = false
    quote
        $(esc(e))
    end
end

macro maybethreads(loop)
    if Threads.nthreads() > 1
        quote
            if SINGLE_THREAD
                $(esc(loop))
            else
                Threads.@threads $(Expr(loop.head,
                    Expr(loop.args[1].head, esc.(loop.args[1].args)...),
                    esc(loop.args[2])))
            end
        end
    else
        quote
            $(esc(loop))
        end
    end
end

"""
Repeatedly calls `worker` on items from `channel` until it is closed
"""
@inline function wrap_worker(worker_process_item, worker_init, channel, worker_id)
    worker_state = worker_init(worker_id)
    for item in channel
        # print("S")
        worker_process_item(item, worker_id, worker_state)
        # print("E")
    end
end


"""
Construct an unbuffered channel and launch a task to feed it items from the `worklist`.
This is adapted from the :greedy schedule coming in Julia 1.11
This channel will stay open until the task finishes, ie until all the items have been put in the channel.
"""
@inline function start_producer(items::Vector{T})::Channel{Tuple{Int, T}} where T
    Channel{Tuple{Int, T}}(0, spawn = true) do channel
        for (i, item) in enumerate(items)
            put!(channel, (i, item))
        end
    end
end

function launch_workers(worker_process_item::F, items::Vector{T}, worker_init_fn = (_) -> nothing) where {T, F <: Function}
    if Pluck.SINGLE_THREAD
        worker_state = worker_init_fn(1)
        for (i, item) in enumerate(items)
            worker_process_item((i, item), 1, worker_state)
        end
        return
    end

    channel = start_producer(items)
    ccall(:jl_enter_threaded_region, Cvoid, ())
    num_workers = Threads.threadpoolsize()
    tasks = Vector{Task}(undef, num_workers)
    for worker_id = 1:num_workers
        t = Task(() -> wrap_worker(worker_process_item, worker_init_fn, channel, worker_id))
        t.sticky = false
        _result = ccall(:jl_set_task_threadpoolid, Cint, (Any, Int8), t, Threads._sym_to_tpid(:default))
        @assert _result == 1
        tasks[worker_id] = t
        schedule(t)
    end
    for worker_id = 1:num_workers
        Base._wait(tasks[worker_id])
    end
    ccall(:jl_exit_threaded_region, Cvoid, ())
    failed_tasks = filter!(istaskfailed, tasks)
    if !isempty(failed_tasks)
        throw(CompositeException(map(TaskFailedException, failed_tasks)))
    end
    nothing
end



mutable struct CacheStats
    name::String
    numerator::Int
    denominator::Int
end
CacheStats(name) = CacheStats(name, 0, 0)
function hit!(c::CacheStats, hit::Bool)
    hit && (c.numerator += 1)
    c.denominator += 1
end
hit!(c::CacheStats) = hit!(c, true)
miss!(c::CacheStats) = hit!(c, false)
Base.show(io::IO, stats::CacheStats) = print(
    io,
    stats.name,
    "=",
    stats.denominator > 0 ? round(stats.numerator / stats.denominator, sigdigits = 2) :
    "0/0",
)
function Base.:+(a::CacheStats, b::CacheStats)
    @assert a.name == b.name
    CacheStats(a.name, a.numerator + b.numerator, a.denominator + b.denominator)
end

function merge_stats(v::Vector{CacheStats})
    if isempty(v)
        return CacheStats("empty")
    end
    reduce(+, v)
end



mutable struct RegionAlloc{T}
    allocations::Vector{T}
    next::Int
    region_starts::Vector{Int}
end
RegionAlloc{T}() where {T} = RegionAlloc{T}(T[], 1, Int[])

@inline function push_region!(a::RegionAlloc)
    push!(a.region_starts, a.next)
end

@inline function pop_region!(a::RegionAlloc)
    a.next = pop!(a.region_starts)
    nothing
end

function Base.get(a::RegionAlloc{T})::T where {T}
    if a.next > length(a.allocations)
        push!(a.allocations, T())
    end
    a.next += 1
    empty!(a.allocations[a.next-1])
    return @inbounds a.allocations[a.next-1]
end





const Id = Int

struct IdSet{T}
    id_of_entry::Dict{T, Id}
    entry_of_id::Vector{T}
end
IdSet{T}() where T = IdSet(Dict{T, Id}(), Vector{T}())
function Base.getindex(idset::IdSet{T}, entry::T) where T
    get!(idset.id_of_entry, entry) do
        push!(idset.entry_of_id, entry)
        length(idset.entry_of_id)
    end
end
function Base.getindex(idset::IdSet{T}, id::Id) where T
    idset.entry_of_id[id]
end


# const TimedType = typeof(@timed nothing)


mutable struct TimeData
    time::Float64
    bytes::Int64
    gctime::Float64
    gcstats::Base.GC_Diff
    compile_time::Float64
    recompile_time::Float64
end
function Base.show(io::IO, td::TimeData)
    print(io, "(time=", td.time, ", bytes=", td.bytes, ", gctime=", td.gctime, ", gcstats=", td.gcstats, ")")
end

mutable struct TimeDataDict
    dict::Dict{Symbol, TimeData}
    order::Vector{Symbol}
end
function Base.show(io::IO, tdd::TimeDataDict)
    isempty(tdd.dict) && return print(io, "TimeDataDict()")
    print(io, "TimeDataDict(")

    rpad_sym = maximum(length.(string.(tdd.order)))

    # Time
    times = [tdd.dict[sym].time for sym in tdd.order]
    total_time = sum(times)
    relative_times = times ./ total_time
    print(io, "\n  Time: ", round2(total_time), "s")
    for (sym, time, relative_time) in zip(tdd.order, times, relative_times)
        print(io, "\n    ", rpad(sym, rpad_sym), " => ", rpad(string(round2(relative_time * 100), "%"), 5), " (", round2(time), "s)")
    end

    # GCTime 
    gctimes = [tdd.dict[sym].gctime for sym in tdd.order]
    total_gctime = sum(gctimes)
    if total_gctime > 0
        frac_gc = total_gctime / total_time
        relative_gctimes = gctimes ./ total_gctime
        print(io, "\n  GC Time: ", round2(total_gctime), "s (", round2(frac_gc * 100), "%)")
        for (sym, gctime, relative_gctime) in zip(tdd.order, gctimes, relative_gctimes)
            print(io, "\n    ", rpad(sym, rpad_sym), " => ", rpad(string(round2(relative_gctime * 100), "%"), 5), " (", round2(gctime), "s)")
        end
    end

    # Compile Time
    compile_times = [tdd.dict[sym].compile_time for sym in tdd.order]
    total_compile_time = sum(compile_times)
    if total_compile_time > 0
        frac_compile = total_compile_time / total_time
        relative_compile_times = compile_times ./ total_compile_time
        print(io, "\n  Compile Time: ", round2(total_compile_time), "s (", round2(frac_compile * 100), "%)")
        for (sym, compile_time, relative_compile_time) in zip(tdd.order, compile_times, relative_compile_times)
            print(io, "\n    ", rpad(sym, rpad_sym), " => ", rpad(string(round2(relative_compile_time * 100), "%"), 5), " (", round2(compile_time), "s)")
        end
    end

    # Recompile Time
    recompile_times = [tdd.dict[sym].recompile_time for sym in tdd.order]
    total_recompile_time = sum(recompile_times)
    if total_recompile_time > 0
        frac_recompile = total_recompile_time / total_time
        relative_recompile_times = recompile_times ./ total_recompile_time
        print(io, "\n  Recompile Time: ", round2(total_recompile_time), "s (", round2(frac_recompile * 100), "%)")
        for (sym, recompile_time, relative_recompile_time) in zip(tdd.order, recompile_times, relative_recompile_times)
            print(io, "\n    ", rpad(sym, rpad_sym), " => ", rpad(string(round2(relative_recompile_time * 100), "%"), 5), " (", round2(recompile_time), "s)")
        end
    end

    # Bytes
    bytes = [tdd.dict[sym].bytes for sym in tdd.order]
    total_bytes = sum(bytes)
    relative_bytes = bytes ./ total_bytes
    print(io, "\n  Bytes: ", round2(total_bytes), " bytes")
    for (sym, bytes, relative_byte) in zip(tdd.order, bytes, relative_bytes)
        print(io, "\n    ", rpad(sym, rpad_sym), " => ", rpad(string(round2(relative_byte * 100), "%"), 5), " (", round2(bytes), " bytes)")
    end


    print(io, "\n)")
end



TimeDataDict() = TimeDataDict(Dict{Symbol, TimeData}(), Symbol[])

function add_timing_data!(tdd::TimeDataDict, sym, timed_result)
    td = get!(tdd.dict, sym) do
        push!(tdd.order, sym)
        TimeData()
    end
    add_timing_data!(td, timed_result)
end

function add_timing_data!(tdd::TimeDataDict, tdd2::TimeDataDict)
    for sym in tdd2.order
        if haskey(tdd.dict, sym)
            add_timing_data!(tdd.dict[sym], tdd2.dict[sym])
        else
            tdd.dict[sym] = tdd2.dict[sym]
            push!(tdd.order, sym)
        end
    end
end


TimeData() = TimeData(0.0, 0, 0.0, Base.GC_Diff(0, 0, 0, 0, 0, 0, 0, 0, 0), 0.0, 0.0)

function add_timing_data!(td::TimeData, timed_result)
    td.time += timed_result.time
    td.bytes += timed_result.bytes
    td.gctime += timed_result.gctime

    old = td.gcstats
    new = timed_result.gcstats
    td.gcstats = Base.GC_Diff(
        old.allocd + new.allocd, # Bytes allocated
        old.malloc + new.malloc,          # Number of GC aware malloc()
        old.realloc + new.realloc,        # Number of GC aware realloc()
        old.poolalloc + new.poolalloc,    # Number of pool allocations
        old.bigalloc + new.bigalloc,      # Number of big (non-pool) allocations
        old.freecall + new.freecall,      # Number of GC aware free()
        old.total_time + new.total_time,  # Time spent in garbage collection
        old.pause + new.pause,            # Number of GC pauses
        old.full_sweep + new.full_sweep,  # Number of GC full collections
    )
    td.compile_time += timed_result.compile_time
    td.recompile_time += timed_result.recompile_time
    nothing
end



macro tdata(ex)
    quote
        Base.Experimental.@force_compile
        # Threads.lock_profiling(true)
        # local lock_conflicts = Threads.LOCK_CONFLICT_COUNT[]
        local stats = Base.gc_num()
        local elapsedtime = time_ns()
        Base.cumulative_compile_timing(true)
        local compile_elapsedtimes = Base.cumulative_compile_time_ns()
        local val = Base.@__tryfinally($(esc(ex)),
            (
                elapsedtime = time_ns() - elapsedtime;
                Base.cumulative_compile_timing(false);
                compile_elapsedtimes = Base.cumulative_compile_time_ns() .- compile_elapsedtimes
                # lock_conflicts = Threads.LOCK_CONFLICT_COUNT[] - lock_conflicts;
                # Threads.lock_profiling(false)
            )
        )
        local diff = Base.GC_Diff(Base.gc_num(), stats)
        (
            value = val,
            time = elapsedtime / 1e9,
            bytes = diff.allocd,
            gctime = diff.total_time / 1e9,
            gcstats = diff,
            # lock_conflicts=lock_conflicts,
            compile_time = compile_elapsedtimes[1] / 1e9,
            recompile_time = compile_elapsedtimes[2] / 1e9,
        )
    end
end
