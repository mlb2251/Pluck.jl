module Timing
export ttime, @ttime, ttime_init, ttime_deinit, blackbox, ttime_is_init, has_task_metrics, TimeState, lower_bound, upper_bound, task_time, upper_bound_julia, Ttimer, start!, stop!, elapsed, check_time_limit, elapsed_lower_bound, check_time_limit_lower_bound, remaining_time_lower_bound

const ttime_is_init = Ref(false)
const has_task_metrics = isdefined(Base.Experimental, :task_metrics)



function ttime_init()
    if !ttime_is_init[]
        Base.cumulative_compile_timing(true)
        has_task_metrics && Base.Experimental.task_metrics(true)
        ttime_is_init[] = true
    end
end

function ttime_deinit()
    if ttime_is_init[]
        Base.cumulative_compile_timing(false)
        has_task_metrics && Base.Experimental.task_metrics(false)
        ttime_is_init[] = false
    end
end

function blackbox(@nospecialize f)
    return f()
end

macro ttime(ex)
    quote
        local tstart = ttime()
        local val = $(esc(ex))
        local t = ttime() - tstart
        val, t
    end
end

struct TimeState
    wall_time::Float64 # wall clock
    gc_total_time::Float64 # gc time
    gc_total_time_to_safepoint::Float64 # gc time to safepoint (not included in gc_total_time for some reason)
    compile_time::Float64 # compile time
    task_running_time::Union{Float64, Nothing} # task running time
    task_wall_time::Union{Float64, Nothing} # task wall time
end

function Base.show(io::IO, t::TimeState)
    lb = lower_bound(t)
    ub = upper_bound(t)
    ubjl = upper_bound_julia(t)
    print(io, "(task_time=$(task_time(t)), lower_bound=$(lb), wall_time=$(t.wall_time), upper_bound_julia=$(ubjl), upper_bound=$(ub), bound_diff=$(ub-lb), gc=$(t.gc_total_time), safepoint=$(t.gc_total_time_to_safepoint), compile_time=$(t.compile_time), task_running_time=$(t.task_running_time), task_wall_time=$(t.task_wall_time))")
end

function Base.:(-)(a::TimeState, b::TimeState)
    task_running_time = isnothing(a.task_running_time) || isnothing(b.task_running_time) ? nothing : a.task_running_time - b.task_running_time
    task_wall_time = isnothing(a.task_wall_time) || isnothing(b.task_wall_time) ? nothing : a.task_wall_time - b.task_wall_time
    TimeState(a.wall_time - b.wall_time, a.gc_total_time - b.gc_total_time, a.gc_total_time_to_safepoint - b.gc_total_time_to_safepoint, a.compile_time - b.compile_time, task_running_time, task_wall_time)
end



mutable struct Ttimer
    init_time::TimeState
    time_limit::Union{Nothing, Float64}
    Ttimer() = new(ttime(), nothing)
end

function start!(timer::Ttimer, time_limit)
    timer.init_time = ttime()
    timer.time_limit = time_limit
    return timer
end

function stop!(timer::Ttimer)
    timer.time_limit = nothing
    return timer
end

function elapsed_lower_bound(timer::Ttimer)
    return lower_bound(ttime() - timer.init_time)
end

function remaining_time_lower_bound(timer::Ttimer)
    return isnothing(timer.time_limit) ? Inf64 : max(0., timer.time_limit - elapsed_lower_bound(timer))
end

function check_time_limit_lower_bound(timer::Ttimer)
    return !isnothing(timer.time_limit) && remaining_time_lower_bound(timer) <= 0.
end




"""
Excludes time in sleep() or print() or file io or manual yields or anything
else that might make this task pause.
If task_running_time is not set because the julia version doesn't support it or ttime_init() was not called
before entering the @threads block, then this will return the wall time which is still fine, just a less tight bound.
Alternatively --task-metrics=yes could have been used as a julia CLI flag, which is the only way to make the
main-thread task have task_running_time set.

wall_time: includes GC, includes safepoint, includes compile time, includes yielded time
task_time: includes GC, includes safepoint, includes compile time only when this thread did the compilation
    excludes yielded time, excludes compilation time done by other threads

so task_time is a smaller upper-bound than wall_time, however when computing the lower bound,
which you'd like to be as high as possible, we kinda wish we didn't have to subtract off that compilation
time but unfortunately we can't tell whether it was included in the task_running_time or not so we must subtract it off.
"""
function task_time(t::TimeState)
    @assert isnothing(t.task_running_time) || t.task_running_time <= t.wall_time || isapprox(t.task_running_time, t.wall_time; atol=.001) "sanity check: task_running_time=$(t.task_running_time) <= wall_time=$(t.wall_time)"
    isnothing(t.task_running_time) ? t.wall_time : t.task_running_time
end

"""
Upper bound on the time spent in pure julia code, which would have to block on the GC.
We wish we could subtract off the gc_total_time_to_safepoint, but technically only the very first
thread thats waiting at the safepoint logs that number so other threads might get more work done.

If you know that the code is in pure julia, this can put a much tighter upper bound on the time.
"""
function upper_bound_julia(t::TimeState)
    task_time(t) - t.gc_total_time
end

"""
For a true upper bound that includes C/Rust code that can run while GC is happening,
we can only use the wall clock time.
"""
function upper_bound(t::TimeState)
    task_time(t)
end



"""
A lower bound on the time spent actually doing work, obtained by subtracting various upper bounds off the wall clock time.
* gc_total_time: time spent in GC was not work. Loose bound because we might have been in Rust/C code with gc_safe=true.
* gc_total_time_to_safepoint: time spent waiting at a safepoint is not work. Loose bound because we might not have been the thread that started the safepoint wait (so we might have waited less time), or also we might be in Rust/C code with gc_safe=true.
* compile_time: time spent compiling is not work. Loose bound due to a double-counting bug in julia's compile time logging.

Note that the one case where this is *not* actually guaranteed to be a lower bound is when
task_running_time is nothing, because in that case time spent yielded to other threads will appear as work.
Also, if there are any other sources of time that we haven't accounted for, this will be a slightly invalid bound.

"""
function lower_bound(t::TimeState)
    lb = task_time(t) - t.gc_total_time - t.gc_total_time_to_safepoint - t.compile_time
    max(0., lb)
end

function ttime()
    ttime_init()
    gc_num = Base.gc_num()
    task_run = has_task_metrics ? Base.Experimental.task_running_time_ns() : nothing
    task_wall = has_task_metrics ? Base.Experimental.task_wall_time_ns() : nothing
    TimeState(
        time_ns()/1e9,
        gc_num.total_time/1e9,
        gc_num.total_time_to_safepoint/1e9,
        Base.cumulative_compile_time_ns()[1]/1e9,
        isnothing(task_run) ? nothing : task_run/1e9,
        isnothing(task_wall) ? nothing : task_wall/1e9
    )
end

function verify()
    ttime_init()

    if has_task_metrics
        # run this test within a task so that we can see the task_running_time
        t = Task(verify_task_metrics)
        schedule(t)
        wait(t)
    else
        printstyled("task_metrics not supported, skipping verify_task_metrics\n", color=:yellow)
    end


    return nothing
end

function verify_task_metrics()
    println("Verifying that sleeping (and thus yielding) is not included in task_running_time...")
    res, t = @ttime blackbox(() -> sleep(1))
    # println("sleep(1) time: ", t)
    @assert t.wall_time >= 1.
    @assert t.task_running_time < 1.

    println("Verifying that gc_total_time is included in task_running_time...")
    function mostly_gc()
        xs=Any[]
        for i in 1:10000000
            push!(xs,i)
        end
        xs=nothing
        GC.gc(true)
        nothing
    end
    res, t = @ttime blackbox(mostly_gc)
    # println("mostly_gc() time: ", t)
    @assert t.gc_total_time > t.wall_time/2
    @assert task_time(t) - t.gc_total_time > 0.

    println("Verifying that compile_time is included in task_running_time...")
    res, t = @ttime blackbox(() -> some_global(Val(rand())))
    # println("mostly_compile() time: ", t)
    @assert t.compile_time > 0
    @assert t.compile_time > t.wall_time/2
    @assert task_time(t) - t.compile_time > 0.

    return nothing
end

"""
A function that must be recompiled with every new input :)
"""
function mostly_compile(::Val{T}) where T
    if log(10) < 0
        println("impossible branch")
        return log.(rand(1000)) .* rand(1000)
    end
    return nothing
end
some_global = mostly_compile



end # module Timing