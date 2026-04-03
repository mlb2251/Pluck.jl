# Julia bindings for the Rust RSDD library.
# To use, first make sure to build rsdd with the ffi feature flag on.
export RSDD
module RSDD

include("../util/timing.jl")
using .Timing
export ttime, @ttime, ttime_init, ttime_deinit, blackbox, ttime_is_init, has_task_metrics, TimeState, lower_bound, upper_bound, task_time, upper_bound_julia, Ttimer, start!, stop!, elapsed, check_time_limit, elapsed_lower_bound, check_time_limit_lower_bound, remaining_time_lower_bound, bdd_start_ite_limit, bdd_stop_ite_limit, bdd_time_limit_exceeded, bdd_ite_limit_exceeded, bdd_deep_copy, bdd_wmc_raw, bdd_wmc, bdd_num_recursive_calls, bdd_get_vars, BDD, embed_bdd


export WmcParams, 
    new_weights,
    new_wmc_params_f64, 
    new_wmc_params_f64_dual, 
    set_weight, 
    set_weight_deriv, 
    var_partial,
    bdd_wmc, 
    bdd_wmc_dual,
    bdd_true,
    bdd_false

export InnerBDD,
    bdd_and,
    bdd_or,
    bdd_iff,
    bdd_xor,
    bdd_negate,
    bdd_is_true,
    bdd_is_false,
    bdd_true,
    bdd_false,
    bdd_ite,
    bdd_eq,
    bdd_high,
    bdd_low,
    bdd_topvar,
    bdd_num_recursive_calls,
    print_bdd_string,
    bdd_exists,
    bdd_condition,
    bdd_compose,
    bdd_size,
    bdd_is_var,
    man_print_stats,
    bdd_is_const,
    bdd_vector_compose,
    bdd_new_var,
    mk_bdd_manager_default_order,
    bdd_has_variable,
    bdd_implies,
    bdd_json,
    CDCLSolver,
    cdcl_solver_from,
    cdcl_check_assuming!,
    cdcl_new_selector!,
    cdcl_push_assumption!,
    cdcl_pop_assumption!,
    CDCLStats,
    get_cdcl_stats,
    clear_cdcl_stats!,
    show_cdcl_stats


# Declare global variables
const librsdd_path = joinpath(@__DIR__, "rsdd", "target", "release", "librsdd")


export get_rsdd_time, clear_rsdd_time!, rsdd_time!, rsdd_timed, @rsdd_time, get_bdd_stats, clear_bdd_stats!

# Default vector size for DualNumber
const DEFAULT_VECTOR_SIZE = 3

mutable struct BDDStats
    rsdd_time::Float64
    total_bdd_size::Int
end
const bdd_stats = BDDStats(0.0, 0)
Base.show(io::IO, stats::BDDStats) = print(io, "BDDStats(rsdd_time=$(round(stats.rsdd_time, digits=2)) s, total_bdd_size=$(stats.total_bdd_size))")

function get_rsdd_time()
    return bdd_stats
end

function get_bdd_stats()
    return bdd_stats
end

function rsdd_time!(time::Float64)
    bdd_stats.rsdd_time += time
end

function clear_rsdd_time!()
    bdd_stats.rsdd_time = 0.0
end

function clear_bdd_stats!()
    bdd_stats.rsdd_time = 0.0
    bdd_stats.total_bdd_size = 0
end

macro bdd_time_limit(manager, expr)
    quote
        bdd_start_time_limit($(esc(manager)))
        try
            $(esc(expr))
        finally
            bdd_stop_time_limit($(esc(manager)))
        end
    end
end

macro rsdd_time(expr)
    quote
        clear_rsdd_time!()
        tstart = time()
        res = $(esc(expr))
        total_time = time() - tstart
        bdd_time = get_rsdd_time()
        println("InnerBDD time: $(100*round(bdd_time.rsdd_time / total_time, digits=2))%")
        res
    end
end


macro rsdd_timed(expr)
    quote
        tstart = time()
        res = $(esc(expr))
        rsdd_time!(time() - tstart)
        res
    end
end


mutable struct WmcParams
    ptr::Ptr{Cvoid}
    freed::Bool
    vector_size::UInt
    dual::Bool
end

# Updated to include size field
struct WmcDual
    _0::Float64 # primal
    _1::Ptr{Float64} # dual
    _size::UInt
end

# Define types
const ManagerPtr = Ptr{Cvoid}
const Label = Csize_t

mutable struct Manager
    ptr::ManagerPtr
    bdds::Vector{Any}
    freed::Bool
    BDD_TRUE::Any
    BDD_FALSE::Any
    weights::WmcParams
    vector_size::UInt
    active_time_limit
    active_ite_limit::Union{Nothing, Int}
    hit_time_limit::Bool
    hit_ite_limit::Bool
end

function Manager(; num_vars::Int=0, vector_size::Int=0, dual::Bool=false)
    manager_ptr = @rsdd_timed @ccall librsdd_path.mk_bdd_manager_default_order(num_vars::Cint)::ManagerPtr
    weights = dual ? new_weights_dual(vector_size) : new_weights()
    manager = Manager(manager_ptr, [], false, nothing, nothing, weights, vector_size, nothing, nothing, false, false)
    manager.BDD_TRUE = bdd_true(manager)
    manager.BDD_FALSE = bdd_false(manager)
    return manager
end

struct InnerBDD
    manager::Manager
    ptr::Csize_t
    function InnerBDD(manager::Manager, ptr::Csize_t)
        bdd = new(manager, ptr)
        push!(manager.bdds, bdd)
        return bdd
    end
end

struct BDDRawPtr
    ptr::Csize_t
end

# Show method for InnerBDD
Base.show(io::IO, bdd::InnerBDD) = print(io, print_bdd_string(bdd))


"""
Creates a new InnerBDD variable.
Returns: InnerBDD
"""
function bdd_new_var(manager::Manager, polarity::Bool)
    ptr = @rsdd_timed @ccall librsdd_path.bdd_new_var(manager.ptr::ManagerPtr, polarity::Bool)::Csize_t
    InnerBDD(manager, ptr)
end

"""
Performs logical AND operation on two BDDs.
Returns: InnerBDD
"""
function bdd_and(a::InnerBDD, b::InnerBDD)
    # tstart = time()
    @assert a.manager == b.manager "BDDs must belong to the same manager"
    ptr = @bdd_time_limit a.manager @rsdd_timed @ccall librsdd_path.bdd_and(a.manager.ptr::ManagerPtr, a.ptr::Csize_t, b.ptr::Csize_t)::Csize_t
    # tstop = time()
    # bdd_time.bdd_and += (tstop - tstart)
    return InnerBDD(a.manager, ptr)
end

"""
Performs logical OR operation on two BDDs.
Returns: InnerBDD
"""
function bdd_or(a::InnerBDD, b::InnerBDD)
    # tstart = time()
    @assert a.manager == b.manager "BDDs must belong to the same manager"
    ptr = @bdd_time_limit a.manager @rsdd_timed @ccall librsdd_path.bdd_or(a.manager.ptr::ManagerPtr, a.ptr::Csize_t, b.ptr::Csize_t)::Csize_t
    # tstop = time()
    # bdd_time.bdd_or += (tstop - tstart)
    return InnerBDD(a.manager, ptr)
end

"""
Performs logical IFF (if and only if) operation on two BDDs.
Returns: InnerBDD
"""
function bdd_iff(a::InnerBDD, b::InnerBDD)
    @assert a.manager == b.manager "BDDs must belong to the same manager"
    ptr = @bdd_time_limit a.manager @rsdd_timed @ccall librsdd_path.bdd_iff(a.manager.ptr::ManagerPtr, a.ptr::Csize_t, b.ptr::Csize_t)::Csize_t
    InnerBDD(a.manager, ptr)
end

"""
Performs logical XOR operation on two BDDs.
Returns: InnerBDD
"""
function bdd_xor(a::InnerBDD, b::InnerBDD)
    @assert a.manager == b.manager "BDDs must belong to the same manager"
    bdd_ite(a, bdd_negate(b), b)
end

"""
Negates a InnerBDD.
Returns: InnerBDD
"""
function bdd_negate(bdd::InnerBDD)
    ptr = @rsdd_timed @ccall librsdd_path.bdd_negate(bdd.manager.ptr::ManagerPtr, bdd.ptr::Csize_t)::Csize_t
    InnerBDD(bdd.manager, ptr)
end

"""
Checks if a InnerBDD represents the constant true.
Returns: Bool
"""
bdd_is_true(bdd::InnerBDD) = @rsdd_timed @ccall librsdd_path.bdd_is_true(bdd.ptr::Csize_t)::Bool

"""
Checks if a InnerBDD represents the constant false.
Returns: Bool
"""
bdd_is_false(bdd::InnerBDD) = @rsdd_timed @ccall librsdd_path.bdd_is_false(bdd.ptr::Csize_t)::Bool

"""
Creates a InnerBDD representing the constant true.
Returns: InnerBDD
"""
function bdd_true(manager::Manager)
    ptr = @rsdd_timed @ccall librsdd_path.bdd_true(manager.ptr::ManagerPtr)::Csize_t
    true_bdd(InnerBDD(manager, ptr))
end

"""
Creates a InnerBDD representing the constant false.
Returns: InnerBDD
"""
function bdd_false(manager::Manager)
    ptr = @rsdd_timed @ccall librsdd_path.bdd_false(manager.ptr::ManagerPtr)::Csize_t
    false_bdd(InnerBDD(manager, ptr))
end

"""
Performs if-then-else operation on three BDDs.
Returns: InnerBDD
"""
function bdd_ite(f::InnerBDD, g::InnerBDD, h::InnerBDD)
    @assert f.manager == g.manager == h.manager "BDDs must belong to the same manager"
    ptr = @bdd_time_limit f.manager @rsdd_timed @ccall librsdd_path.bdd_ite(f.manager.ptr::ManagerPtr, f.ptr::Csize_t, g.ptr::Csize_t, h.ptr::Csize_t)::Csize_t
    InnerBDD(f.manager, ptr)
end

"""
Checks if two BDDs are equal.
Returns: Bool
"""
function bdd_eq(a::InnerBDD, b::InnerBDD)
    @assert a.manager == b.manager "BDDs must belong to the same manager"
    @rsdd_timed @ccall librsdd_path.bdd_eq(a.manager.ptr::ManagerPtr, a.ptr::Csize_t, b.ptr::Csize_t)::Bool
end

"""
Gets the high child of a InnerBDD node.
Returns: InnerBDD
"""
function bdd_high(bdd::InnerBDD)
    ptr = @rsdd_timed @ccall librsdd_path.bdd_high(bdd.manager.ptr::ManagerPtr, bdd.ptr::Csize_t)::Csize_t
    InnerBDD(bdd.manager, ptr)
end

"""
Gets the low child of a InnerBDD node.
Returns: InnerBDD
"""
function bdd_low(bdd::InnerBDD)
    ptr = @rsdd_timed @ccall librsdd_path.bdd_low(bdd.manager.ptr::ManagerPtr, bdd.ptr::Csize_t)::Csize_t
    InnerBDD(bdd.manager, ptr)
end

"""
Gets the top variable of a InnerBDD.
Returns: Label (Csize_t)
"""
bdd_topvar(bdd::InnerBDD) = @rsdd_timed @ccall librsdd_path.bdd_topvar(bdd.ptr::Csize_t)::Label

"""
Gets the number of recursive calls made by the InnerBDD manager.
Returns: Int
"""
bdd_num_recursive_calls(manager::Manager) = @rsdd_timed Int(@ccall librsdd_path.bdd_num_recursive_calls(manager.ptr::ManagerPtr)::UInt64)

"""
Prints a InnerBDD to a string.
Returns: String
"""
function print_bdd_string(bdd::InnerBDD)
    cstr = @rsdd_timed @ccall librsdd_path.print_bdd(bdd.ptr::Csize_t)::Ptr{Cchar}
    return unsafe_string(cstr)
end

"""
Prints a InnerBDD to a JSON string.
Returns: String
"""
function bdd_json(bdd::InnerBDD)
    cstr = @rsdd_timed @ccall librsdd_path.bdd_json(bdd.ptr::Csize_t)::Ptr{Cchar}
    return unsafe_string(cstr)
end

"""
Existentially quantifies a variable in a InnerBDD.
Returns: InnerBDD
"""
function bdd_exists(bdd::InnerBDD, var::Label)
    ptr = @rsdd_timed @ccall librsdd_path.bdd_exists(bdd.manager.ptr::ManagerPtr, bdd.ptr::Csize_t, var::Label)::Csize_t
    InnerBDD(bdd.manager, ptr)
end

"""
Conditions a InnerBDD on a variable.
Returns: InnerBDD
"""
function bdd_condition(bdd::InnerBDD, var::Label, value::Bool)
    ptr = @rsdd_timed @ccall librsdd_path.bdd_condition(bdd.manager.ptr::ManagerPtr, bdd.ptr::Csize_t, var::Label, value::Bool)::Csize_t
    InnerBDD(bdd.manager, ptr)
end

"""
Composes a InnerBDD by substituting a variable with another InnerBDD.
Returns: InnerBDD
"""
function bdd_compose(f::InnerBDD, var::Label, g::InnerBDD)
    @assert f.manager == g.manager "BDDs must belong to the same manager"
    ptr = @rsdd_timed @ccall librsdd_path.bdd_compose(f.manager.ptr::ManagerPtr, f.ptr::Csize_t, var::Label, g.ptr::Csize_t)::Csize_t
    InnerBDD(f.manager, ptr)
end

"""
Checks if one InnerBDD implies another.
Returns: Bool
"""
bdd_implies(a::InnerBDD, b::InnerBDD) = b | !a

"""
Gets the size of a InnerBDD.
Returns: Int
"""
bdd_size(bdd::InnerBDD) = @rsdd_timed Int(@ccall librsdd_path.bdd_size(bdd.ptr::Csize_t)::UInt64)

"""
Checks if a InnerBDD represents a variable.
Returns: Bool
"""
bdd_is_var(bdd::InnerBDD) = @rsdd_timed @ccall librsdd_path.bdd_is_var(bdd.manager.ptr::ManagerPtr, bdd.ptr::Csize_t)::Bool

"""
Prints statistics about the InnerBDD manager.
"""
man_print_stats(manager::Manager) = @rsdd_timed @ccall librsdd_path.man_print_stats(manager.ptr::ManagerPtr)::Cvoid

"""
Checks if a InnerBDD represents a constant (true or false).
Returns: Bool
"""
bdd_is_const(bdd::InnerBDD) = !bdd_is_var(bdd)

"""
Composes multiple variables into a InnerBDD according to given BDDs.
Returns: InnerBDD
"""
function bdd_vector_compose(f::InnerBDD, vars::Vector{Label}, bdds::Vector{InnerBDD})
    @assert length(vars) == length(bdds) "Number of variables must match number of BDDs"
    result = f
    for (var, bdd) in zip(vars, bdds)
        result = bdd_compose(result, var, bdd)
    end
    result
end

function Base.isequal(a::InnerBDD, b::InnerBDD)
    return bdd_eq(a, b)
end


"""
Checks if a InnerBDD has a variable.
Returns: Bool
"""
bdd_has_variable(bdd::InnerBDD, var::Label) = @rsdd_timed @ccall librsdd_path.bdd_has_variable(bdd.manager.ptr::ManagerPtr, bdd.ptr::Csize_t, var::Label)::Bool

# Convenience operators
Base.:&(a::InnerBDD, b::InnerBDD) = bdd_and(a, b)
Base.:|(a::InnerBDD, b::InnerBDD) = bdd_or(a, b)
Base.:!(a::InnerBDD) = bdd_negate(a)
Base.:⊻(a::InnerBDD, b::InnerBDD) = bdd_xor(a, b)
Base.:(==)(a::InnerBDD, b::InnerBDD) = bdd_eq(a, b)
Base.:(!=)(a::InnerBDD, b::InnerBDD) = !bdd_eq(a, b)
(⟺)(a::InnerBDD, b::InnerBDD) = bdd_iff(a, b)
Base.:~(a::InnerBDD) = bdd_negate(a)

"""
Creates a new WmcParams object for floating-point weights.
Returns: WmcParams
"""
function new_weights()
    ptr = @rsdd_timed @ccall librsdd_path.new_wmc_params_f64()::Ptr{Cvoid}
    WmcParams(ptr, false, 0, false)
end

"""
Creates a new WmcParams object for dual floating-point weights.
Returns: WmcParams
"""
function new_weights_dual(vector_size::Integer)
    ptr = @rsdd_timed @ccall librsdd_path.new_wmc_params_f64_dual()::Ptr{Cvoid}
    WmcParams(ptr, false, vector_size, true)
end

"""
Sets the weight for a variable in the WmcParams object.
"""
function set_weight(mgr::Manager, var::Label, low::Float64, high::Float64)
    set_weight(mgr.weights, var, low, high)
end

"""
Sets the weight for a variable in the WmcParams object. 
"""
function set_weight(params::WmcParams, var::Label, low::Float64, high::Float64)
    if params.dual
        low_dual = zeros(Float64, params.vector_size)
        high_dual = zeros(Float64, params.vector_size)    
        set_weight_deriv(params, var, low, low_dual, high, high_dual)
    else
        @rsdd_timed @ccall librsdd_path.wmc_param_f64_set_weight(params.ptr::Ptr{Cvoid}, var::Label, low::Float64, high::Float64)::Cvoid
    end
end

"""
Sets the weight and derivative for a variable in the WmcParams object. 
"""
function set_weight_deriv(params::WmcParams, var::Label, low::Float64, low_dual::Vector{Float64}, high::Float64, high_dual::Vector{Float64})
    # Get sizes of vectors
    low_size = length(low_dual)
    high_size = length(high_dual)
    
    @rsdd_timed @ccall librsdd_path.wmc_param_f64_set_weight_deriv_dual(params.ptr::Ptr{Cvoid}, var::Label, low::Float64, low_dual::Ptr{Float64}, low_size::Csize_t, high::Float64, high_dual::Ptr{Float64}, high_size::Csize_t)::Cvoid
end

"""
Get a partial derivative from a vector pointer.
"""
function var_partial(partials::Ptr{Float64}, metaparam::UInt, size::UInt)
    # Added size parameter
    @rsdd_timed @ccall librsdd_path.wmc_param_f64_var_partial(partials::Ptr{Float64}, metaparam::Csize_t, size::Csize_t)::Float64
end

"""
Performs weighted model counting on a InnerBDD.
Returns: Float64
"""
function bdd_wmc(bdd::InnerBDD)
    bdd_wmc_raw(bdd.ptr, bdd.manager.weights)
end

function bdd_wmc_raw(bdd_ptr::Csize_t, params::WmcParams)
    if params.dual
        result = @rsdd_timed @ccall librsdd_path.bdd_wmc_dual(bdd_ptr::Csize_t, params.ptr::Ptr{Cvoid})::WmcDual
        # this is a bit of a jank way to get the floats over one by one, there must be a better way
        partials = [var_partial(result._1, unsigned(i), result._size) for i=0:signed(result._size)-1]
        return result._0, partials
    else
        @rsdd_timed @ccall librsdd_path.bdd_wmc(bdd_ptr::Csize_t, params.ptr::Ptr{Cvoid})::Float64
    end
end

# """
# Frees the memory associated with a InnerBDD.
# """
function free_bdd(bdd::InnerBDD)
    @rsdd_timed @ccall librsdd_path.free_bdd(bdd.ptr::Csize_t)::Cvoid
end

"""
Frees the memory associated with a InnerBDD manager.
"""
function free_bdd_manager(manager::Manager)
    manager.freed && return
    for bdd in manager.bdds
        free_bdd(bdd)
    end
    manager.bdds = []
    manager.freed = true
    @rsdd_timed @ccall librsdd_path.free_bdd_manager(manager.ptr::ManagerPtr)::Cvoid
end

"""
Frees the memory associated with a WmcParams object.
"""
function free_wmc_params(params::WmcParams)
    params.freed && return
    if params.dual
        @rsdd_timed @ccall librsdd_path.free_wmc_params_dual(params.ptr::Ptr{Cvoid})::Cvoid
    else
        @rsdd_timed @ccall librsdd_path.free_wmc_params(params.ptr::Ptr{Cvoid})::Cvoid
    end
    params.freed = true
    return
end

"""
Frees the memory associated with derivative vectors.
"""
function free_wmc_dual_derivatives(ptr::Ptr{Float64}, size::Integer)
    @rsdd_timed @ccall librsdd_path.free_wmc_dual_derivatives(ptr::Ptr{Float64}, size::Csize_t)::Cvoid
end

"""
Creates a new variable at a specified position in the InnerBDD manager's variable order.

# Arguments
- `manager::Manager`: The InnerBDD manager.
- `position::Integer`: The position at which to insert the new variable.
- `polarity::Bool`: The polarity of the new variable (true for positive, false for negative).

# Returns
A new InnerBDD representing the variable.
"""
function bdd_new_var_at_position(manager::Manager, position::Integer, polarity::Bool)
    ptr = @rsdd_timed @ccall librsdd_path.bdd_new_var_at_position(manager.ptr::ManagerPtr, position::Csize_t, polarity::Bool)::Csize_t
    InnerBDD(manager, ptr)
end

"""
Gets the size of a DualNumber vector.
"""
function dual_number_get_size(dual_ptr::Ptr{Cvoid})
    @rsdd_timed @ccall librsdd_path.dual_number_get_size(dual_ptr::Ptr{Cvoid})::Csize_t
end

"""
Creates a DualNumber with a specified size.
"""
function dual_number_create(value::Float64, size::Integer)
    @rsdd_timed @ccall librsdd_path.dual_number_create(value::Float64, size::Csize_t)::Ptr{Cvoid}
end

struct WeightedSampleResult
    sample::Csize_t
    probability::Cdouble
end

"""
Performs weighted sampling on a InnerBDD.
Returns: Tuple of (InnerBDD, Float64) representing the sampled InnerBDD and its probability
"""
function bdd_weighted_sample(bdd::InnerBDD)
    result = @rsdd_timed @ccall librsdd_path.robdd_weighted_sample(bdd.manager.ptr::ManagerPtr, bdd.ptr::Csize_t, bdd.manager.weights.ptr::Ptr{Cvoid})::WeightedSampleResult

    sample_bdd = InnerBDD(bdd.manager, result.sample)
    probability = result.probability

    return (sample_bdd, probability)
end

function bdd_top_k_paths(bdd::InnerBDD, k::Integer)
    ptr = @rsdd_timed @ccall librsdd_path.robdd_top_k_paths(bdd.manager.ptr::ManagerPtr, bdd.ptr::Csize_t, k::Csize_t, bdd.manager.weights.ptr::Ptr{Cvoid})::Csize_t
    InnerBDD(bdd.manager, ptr)
end

"""
Sets a time limit for the InnerBDD manager and starts the clock.
"""
function bdd_set_time_limit(manager::Manager, time_limit)
    if !isnothing(time_limit)
        manager.active_time_limit = time_limit
        manager.hit_time_limit = false
    end
    nothing
end

function bdd_start_ite_limit(manager::Manager, ite_limit)
    isnothing(ite_limit) && return
    @ccall librsdd_path.start_bdd_manager_ite_limit(manager.ptr::ManagerPtr, ite_limit::Csize_t)::Cvoid
end

function bdd_stop_ite_limit(manager::Manager)
    @ccall librsdd_path.stop_bdd_manager_ite_limit(manager.ptr::ManagerPtr)::Cvoid
end

"""
Sets a time limit for the InnerBDD manager and starts the clock.
"""
function bdd_start_time_limit(manager::Manager)
    if !isnothing(manager.active_time_limit) && !isnothing(manager.active_time_limit.time_limit)
        remaining_time = remaining_time_lower_bound(manager.active_time_limit)
        @ccall librsdd_path.start_bdd_manager_time_limit(manager.ptr::ManagerPtr, remaining_time::Cdouble)::Cvoid
    end
end

"""
Stops the InnerBDD manager time limit.
"""
function bdd_stop_time_limit(manager::Manager)
    if !isnothing(manager.active_time_limit)
        hit_limit = @ccall librsdd_path.bdd_manager_time_limit_exceeded(manager.ptr::ManagerPtr)::Bool
        manager.hit_time_limit |= hit_limit    
        @ccall librsdd_path.stop_bdd_manager_time_limit(manager.ptr::ManagerPtr)::Cvoid
    end
end

"""
Checks if the InnerBDD manager time limit has been exceeded.
Returns: Bool
"""
function bdd_time_limit_exceeded(manager::Manager)
    manager.hit_time_limit
end

function bdd_ite_limit_exceeded(manager::Manager)
    @ccall librsdd_path.bdd_manager_ite_limit_exceeded(manager.ptr::ManagerPtr)::Bool
end

function bdd_deep_copy(bdd::InnerBDD)
    ptr = @rsdd_timed @ccall librsdd_path.bdd_deep_copy(bdd.ptr::Csize_t)::Csize_t
    BDDRawPtr(ptr)
end

function bdd_free_deep_copy(bdd::BDDRawPtr)
    @rsdd_timed @ccall librsdd_path.bdd_free_deep_copy(bdd.ptr::Csize_t)::Cvoid
end

struct VarArray
    data::Ptr{UInt64}
    len::Csize_t
end

function bdd_get_vars(bdd::InnerBDD)::Set{Label}
    arr = @rsdd_timed @ccall librsdd_path.bdd_get_vars(bdd.ptr::Csize_t)::VarArray
    vars = Set{Label}()
    for i in 1:arr.len
        push!(vars, unsafe_load(arr.data, i))
    end
    if arr.len > 0
        @ccall librsdd_path.free_var_array(arr::VarArray)::Cvoid
    end
    return vars
end

include("SAT.jl")
using .SAT


include("satbased.jl")

# include("deferred.jl")

# Add these to the exports at the end of the file
export free_bdd, 
free_bdd_manager, 
free_wmc_params, 
bdd_new_var_at_position, 
bdd_weighted_sample, 
bdd_top_k_paths, 
free_wmc_dual_derivatives,
dual_number_get_size,
dual_number_create,
bdd_var_position, 
bdd_last_var,
bdd_set_time_limit,
bdd_stop_time_limit,
bdd_time_limit_exceeded

end # module
