# Julia bindings for the Rust RSDD library.
# To use, first make sure to build rsdd with the ffi feature flag on.
export RSDD
module RSDD

include("../util/timing.jl")
using .Timing
export ttime, @ttime, ttime_init, ttime_deinit, blackbox, ttime_is_init, has_task_metrics, TimeState, lower_bound, upper_bound, task_time, upper_bound_julia, Ttimer, start!, stop!, elapsed, check_time_limit, elapsed_lower_bound, check_time_limit_lower_bound, remaining_time_lower_bound



using Libdl

export WmcParams, 
    WmcParamsDual, 
    getWmcDual,
    new_weights,
    new_wmc_params_f64, 
    new_wmc_params_f64_dual, 
    set_weight, 
    set_weight_deriv, 
    set_weight_dual,
    var_partial,
    bdd_wmc, 
    bdd_wmc_dual,
    bdd_true,
    bdd_false

export BDD,
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
    bdd_json


# Declare global variables
const librsdd_path = joinpath(@__DIR__, "rsdd", "target", "release", "librsdd")
let
    global librsdd = C_NULL
    global mk_bdd_manager_default_order_ptr = C_NULL
    global bdd_new_var_ptr = C_NULL
    global bdd_and_ptr = C_NULL
    global bdd_or_ptr = C_NULL
    global bdd_iff_ptr = C_NULL
    global bdd_negate_ptr = C_NULL
    global bdd_is_true_ptr = C_NULL
    global bdd_is_false_ptr = C_NULL
    global bdd_true_ptr = C_NULL
    global bdd_false_ptr = C_NULL
    global bdd_ite_ptr = C_NULL
    global bdd_eq_ptr = C_NULL
    global bdd_high_ptr = C_NULL
    global bdd_low_ptr = C_NULL
    global bdd_topvar_ptr = C_NULL
    global bdd_num_recursive_calls_ptr = C_NULL
    global print_bdd_ptr = C_NULL
    global bdd_exists_ptr = C_NULL
    global bdd_condition_ptr = C_NULL
    global bdd_compose_ptr = C_NULL
    global bdd_size_ptr = C_NULL
    global bdd_has_variable_ptr = C_NULL
    global bdd_is_var_ptr = C_NULL
    global man_print_stats_ptr = C_NULL
    global bdd_is_const_ptr = C_NULL
    global bdd_hash_ptr = C_NULL
    global new_wmc_params_f64_ptr = C_NULL
    global wmc_param_f64_set_weight_ptr = C_NULL
    global wmc_param_f64_set_weight_deriv_dual_ptr = C_NULL
    global wmc_param_f64_set_weight_dual_ptr = C_NULL
    global wmc_param_f64_var_partial_ptr = C_NULL
    global bdd_wmc_ptr = C_NULL
    global bdd_wmc_dual_ptr = C_NULL
    global free_bdd_ptr = C_NULL
    global free_bdd_manager_ptr = C_NULL
    global free_wmc_params_ptr = C_NULL
    global free_wmc_params_dual_ptr = C_NULL
    global free_wmc_dual_derivatives_ptr = C_NULL
    global bdd_new_var_at_position_ptr = C_NULL
    global robdd_weighted_sample_ptr = C_NULL
    global robdd_top_k_paths_ptr = C_NULL
    global bdd_last_var_ptr = C_NULL
    global bdd_var_position_ptr = C_NULL
    global dual_number_get_size_ptr = C_NULL
    global dual_number_create_ptr = C_NULL
    global start_bdd_manager_time_limit_ptr = C_NULL
    global stop_bdd_manager_time_limit_ptr = C_NULL
    global bdd_manager_time_limit_exceeded_ptr = C_NULL
end

export get_rsdd_time, clear_rsdd_time!, rsdd_time!, rsdd_timed, @rsdd_time

# Default vector size for DualNumber
const DEFAULT_VECTOR_SIZE = 3

mutable struct BDDStats
    rsdd_time::Float64
end
const bdd_stats = BDDStats(0.0)
Base.show(io::IO, stats::BDDStats) = print(io, "BDDStats(rsdd_time=$(round(stats.rsdd_time, digits=2)) s)")

function get_rsdd_time()
    return bdd_stats
end

function rsdd_time!(time::Float64)
    bdd_stats.rsdd_time += time
end

function clear_rsdd_time!()
    bdd_stats.rsdd_time = 0.0
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
        println("BDD time: $(100*round(bdd_time.rsdd_time / total_time, digits=2))%")
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

abstract type AbstractWmcParams end

mutable struct WmcParams <: AbstractWmcParams
    ptr::Ptr{Cvoid}
    freed::Bool
end

mutable struct WmcParamsDual <: AbstractWmcParams
    ptr::Ptr{Cvoid}
    freed::Bool
    vector_size::UInt
    
    function WmcParamsDual(ptr::Ptr{Cvoid}, freed::Bool, vector_size::Integer)
        new(ptr, freed, UInt(vector_size))
    end
end

# Updated to include size field
struct WmcDual
    _0::Float64
    _1::Ptr{Float64}
    _size::UInt
end

function getWmcDual(wmc::Tuple{Float64, Ptr{Float64}, UInt})
    size = wmc[3]
    if size == 0
        return wmc[1], []
    end
    partials = [var_partial(wmc[2], unsigned(i), size) for i=0:size-1]
    return wmc[1], partials
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
    weights::AbstractWmcParams
    vector_size::UInt
    active_time_limit
    hit_time_limit::Bool
end

function Manager(; num_vars::Int=0)
    manager_ptr = @rsdd_timed ccall(mk_bdd_manager_default_order_ptr, ManagerPtr, (Cint,), num_vars)
    weights = new_weights()
    manager = Manager(manager_ptr, [], false, nothing, nothing, weights, 0, nothing, false)
    manager.BDD_TRUE = bdd_true(manager)
    manager.BDD_FALSE = bdd_false(manager)
    return manager
end

function ManagerDual(vector_size::Integer; num_vars::Int=0) # = DEFAULT_VECTOR_SIZE)
    manager_ptr = @rsdd_timed ccall(mk_bdd_manager_default_order_ptr, ManagerPtr, (Cint,), num_vars)
    weights = new_weights_dual(vector_size)
    manager = Manager(manager_ptr, [], false, nothing, nothing, weights, vector_size, nothing, false)
    manager.BDD_TRUE = bdd_true(manager)
    manager.BDD_FALSE = bdd_false(manager)
    return manager
end

struct BDD
    manager::Manager
    ptr::Csize_t
    function BDD(manager::Manager, ptr::Csize_t)
        bdd = new(manager, ptr)
        push!(manager.bdds, bdd)
        return bdd
    end
end

# Helper function to look up symbols
function get_symbol(name::String)
    sym = Libdl.dlsym(librsdd, Symbol(name))
    if sym == C_NULL
        error("Symbol $name not found in the library")
    end
    return sym
end

function __init__()
    global librsdd = Libdl.dlopen(librsdd_path * "." * Libdl.dlext)
    global mk_bdd_manager_default_order_ptr = get_symbol("mk_bdd_manager_default_order")
    global bdd_new_var_ptr = get_symbol("bdd_new_var")
    global bdd_and_ptr = get_symbol("bdd_and")
    global bdd_or_ptr = get_symbol("bdd_or")
    global bdd_iff_ptr = get_symbol("bdd_iff")
    global bdd_negate_ptr = get_symbol("bdd_negate")
    global bdd_is_true_ptr = get_symbol("bdd_is_true")
    global bdd_is_false_ptr = get_symbol("bdd_is_false")
    global bdd_true_ptr = get_symbol("bdd_true")
    global bdd_false_ptr = get_symbol("bdd_false")
    global bdd_ite_ptr = get_symbol("bdd_ite")
    global bdd_eq_ptr = get_symbol("bdd_eq")
    global bdd_high_ptr = get_symbol("bdd_high")
    global bdd_low_ptr = get_symbol("bdd_low")
    global bdd_topvar_ptr = get_symbol("bdd_topvar")
    global bdd_num_recursive_calls_ptr = get_symbol("bdd_num_recursive_calls")
    global print_bdd_ptr = get_symbol("print_bdd")
    global bdd_json_ptr = get_symbol("bdd_json")
    global bdd_exists_ptr = get_symbol("bdd_exists")
    global bdd_condition_ptr = get_symbol("bdd_condition")
    global bdd_compose_ptr = get_symbol("bdd_compose")
    global bdd_size_ptr = get_symbol("bdd_size")
    global bdd_has_variable_ptr = get_symbol("bdd_has_variable")
    global new_wmc_params_f64_ptr = get_symbol("new_wmc_params_f64")
    global new_wmc_params_f64_dual_ptr = get_symbol("new_wmc_params_f64_dual")
    global wmc_param_f64_set_weight_ptr = get_symbol("wmc_param_f64_set_weight")
    global wmc_param_f64_set_weight_deriv_dual_ptr = get_symbol("wmc_param_f64_set_weight_deriv_dual")
    global wmc_param_f64_set_weight_dual_ptr = get_symbol("wmc_param_f64_set_weight_dual")
    global wmc_param_f64_var_partial_ptr = get_symbol("wmc_param_f64_var_partial")
    global bdd_wmc_ptr = get_symbol("bdd_wmc")
    global bdd_wmc_dual_ptr = get_symbol("bdd_wmc_dual")
    global free_bdd_ptr = get_symbol("free_bdd")
    global free_bdd_manager_ptr = get_symbol("free_bdd_manager")
    global free_wmc_params_ptr = get_symbol("free_wmc_params")
    global free_wmc_params_dual_ptr = get_symbol("free_wmc_params_dual")
    global free_wmc_dual_derivatives_ptr = get_symbol("free_wmc_dual_derivatives")
    global bdd_new_var_at_position_ptr = get_symbol("bdd_new_var_at_position")
    global robdd_weighted_sample_ptr = get_symbol("robdd_weighted_sample")
    global robdd_top_k_paths_ptr = get_symbol("robdd_top_k_paths")
    global dual_number_get_size_ptr = get_symbol("dual_number_get_size")
    global dual_number_create_ptr = get_symbol("dual_number_create")
    global start_bdd_manager_time_limit_ptr = get_symbol("start_bdd_manager_time_limit")
    global stop_bdd_manager_time_limit_ptr = get_symbol("stop_bdd_manager_time_limit")
    global bdd_manager_time_limit_exceeded_ptr = get_symbol("bdd_manager_time_limit_exceeded")
end

# Show method for BDD
Base.show(io::IO, bdd::BDD) = print(io, print_bdd_string(bdd))


"""
Creates a new BDD variable.
Returns: BDD
"""
function bdd_new_var(manager::Manager, polarity::Bool)
    ptr = @rsdd_timed ccall(bdd_new_var_ptr, Csize_t, (ManagerPtr, Bool), manager.ptr, polarity)
    BDD(manager, ptr)
end

"""
Performs logical AND operation on two BDDs.
Returns: BDD
"""
function bdd_and(a::BDD, b::BDD)
    # tstart = time()
    @assert a.manager == b.manager "BDDs must belong to the same manager"
    ptr = @bdd_time_limit a.manager @rsdd_timed ccall(bdd_and_ptr, Csize_t, (ManagerPtr, Csize_t, Csize_t), a.manager.ptr, a.ptr, b.ptr)
    # tstop = time()
    # bdd_time.bdd_and += (tstop - tstart)
    return BDD(a.manager, ptr)
end

"""
Performs logical OR operation on two BDDs.
Returns: BDD
"""
function bdd_or(a::BDD, b::BDD)
    # tstart = time()
    @assert a.manager == b.manager "BDDs must belong to the same manager"
    ptr = @bdd_time_limit a.manager @rsdd_timed ccall(bdd_or_ptr, Csize_t, (ManagerPtr, Csize_t, Csize_t), a.manager.ptr, a.ptr, b.ptr)
    # tstop = time()
    # bdd_time.bdd_or += (tstop - tstart)
    return BDD(a.manager, ptr)
end

"""
Performs logical IFF (if and only if) operation on two BDDs.
Returns: BDD
"""
function bdd_iff(a::BDD, b::BDD)
    @assert a.manager == b.manager "BDDs must belong to the same manager"
    ptr = @bdd_time_limit a.manager @rsdd_timed ccall(bdd_iff_ptr, Csize_t, (ManagerPtr, Csize_t, Csize_t), a.manager.ptr, a.ptr, b.ptr)
    BDD(a.manager, ptr)
end

"""
Performs logical XOR operation on two BDDs.
Returns: BDD
"""
function bdd_xor(a::BDD, b::BDD)
    @assert a.manager == b.manager "BDDs must belong to the same manager"
    bdd_ite(a, bdd_negate(b), b)
end

"""
Negates a BDD.
Returns: BDD
"""
function bdd_negate(bdd::BDD)
    ptr = @rsdd_timed ccall(bdd_negate_ptr, Csize_t, (ManagerPtr, Csize_t), bdd.manager.ptr, bdd.ptr)
    BDD(bdd.manager, ptr)
end

"""
Checks if a BDD represents the constant true.
Returns: Bool
"""
bdd_is_true(bdd::BDD) = @rsdd_timed ccall(bdd_is_true_ptr, Bool, (Csize_t,), bdd.ptr)

"""
Checks if a BDD represents the constant false.
Returns: Bool
"""
bdd_is_false(bdd::BDD) = @rsdd_timed ccall(bdd_is_false_ptr, Bool, (Csize_t,), bdd.ptr)

"""
Creates a BDD representing the constant true.
Returns: BDD
"""
function bdd_true(manager::Manager)
    ptr = @rsdd_timed ccall(bdd_true_ptr, Csize_t, (Manager,), manager)
    BDD(manager, ptr)
end

"""
Creates a BDD representing the constant false.
Returns: BDD
"""
function bdd_false(manager::Manager)
    ptr = @rsdd_timed ccall(bdd_false_ptr, Csize_t, (Manager,), manager)
    BDD(manager, ptr)
end

"""
Performs if-then-else operation on three BDDs.
Returns: BDD
"""
function bdd_ite(f::BDD, g::BDD, h::BDD)
    @assert f.manager == g.manager == h.manager "BDDs must belong to the same manager"
    ptr = @bdd_time_limit f.manager @rsdd_timed ccall(bdd_ite_ptr, Csize_t, (ManagerPtr, Csize_t, Csize_t, Csize_t), f.manager.ptr, f.ptr, g.ptr, h.ptr)
    BDD(f.manager, ptr)
end

"""
Checks if two BDDs are equal.
Returns: Bool
"""
function bdd_eq(a::BDD, b::BDD)
    @assert a.manager == b.manager "BDDs must belong to the same manager"
    @rsdd_timed ccall(bdd_eq_ptr, Bool, (ManagerPtr, Csize_t, Csize_t), a.manager.ptr, a.ptr, b.ptr)
end

"""
Gets the high child of a BDD node.
Returns: BDD
"""
function bdd_high(bdd::BDD)
    ptr = @rsdd_timed ccall(bdd_high_ptr, Csize_t, (ManagerPtr, Csize_t), bdd.manager.ptr, bdd.ptr)
    BDD(bdd.manager, ptr)
end

"""
Gets the low child of a BDD node.
Returns: BDD
"""
function bdd_low(bdd::BDD)
    ptr = @rsdd_timed ccall(bdd_low_ptr, Csize_t, (ManagerPtr, Csize_t), bdd.manager.ptr, bdd.ptr)
    BDD(bdd.manager, ptr)
end

"""
Gets the top variable of a BDD.
Returns: Label (Csize_t)
"""
bdd_topvar(bdd::BDD) = @rsdd_timed ccall(bdd_topvar_ptr, Label, (Csize_t,), bdd.ptr)

"""
Gets the number of recursive calls made by the BDD manager.
Returns: UInt64
"""
bdd_num_recursive_calls(manager::Manager) = @rsdd_timed ccall(bdd_num_recursive_calls_ptr, UInt64, (ManagerPtr,), manager.ptr)

"""
Prints a BDD to a string.
Returns: String
"""
function print_bdd_string(bdd::BDD)
    cstr = @rsdd_timed ccall(print_bdd_ptr, Ptr{Cchar}, (Csize_t,), bdd.ptr)
    return unsafe_string(cstr)
end

"""
Prints a BDD to a JSON string.
Returns: String
"""
function bdd_json(bdd::BDD)
    cstr = @rsdd_timed ccall(bdd_json_ptr, Ptr{Cchar}, (Csize_t,), bdd.ptr)
    return unsafe_string(cstr)
end

"""
Existentially quantifies a variable in a BDD.
Returns: BDD
"""
function bdd_exists(bdd::BDD, var::Label)
    ptr = @rsdd_timed ccall(bdd_exists_ptr, Csize_t, (ManagerPtr, Csize_t, Label), bdd.manager.ptr, bdd.ptr, var)
    BDD(bdd.manager, ptr)
end

"""
Conditions a BDD on a variable.
Returns: BDD
"""
function bdd_condition(bdd::BDD, var::Label, value::Bool)
    ptr = @rsdd_timed ccall(bdd_condition_ptr, Csize_t, (ManagerPtr, Csize_t, Label, Bool), bdd.manager.ptr, bdd.ptr, var, value)
    BDD(bdd.manager, ptr)
end

"""
Composes a BDD by substituting a variable with another BDD.
Returns: BDD
"""
function bdd_compose(f::BDD, var::Label, g::BDD)
    @assert f.manager == g.manager "BDDs must belong to the same manager"
    ptr = @rsdd_timed ccall(bdd_compose_ptr, Csize_t, (ManagerPtr, Csize_t, Label, Csize_t), f.manager.ptr, f.ptr, var, g.ptr)
    BDD(f.manager, ptr)
end

"""
Checks if one BDD implies another.
Returns: Bool
"""
bdd_implies(a::BDD, b::BDD) = b | !a

"""
Gets the size of a BDD.
Returns: UInt64
"""
bdd_size(bdd::BDD) = @rsdd_timed ccall(bdd_size_ptr, UInt64, (Csize_t,), bdd.ptr)

"""
Checks if a BDD represents a variable.
Returns: Bool
"""
bdd_is_var(bdd::BDD) = @rsdd_timed ccall(bdd_is_var_ptr, Bool, (ManagerPtr, Csize_t), bdd.manager.ptr, bdd.ptr)

"""
Prints statistics about the BDD manager.
"""
man_print_stats(manager::Manager) = @rsdd_timed ccall(man_print_stats_ptr, Cvoid, (ManagerPtr,), manager.ptr)

"""
Checks if a BDD represents a constant (true or false).
Returns: Bool
"""
bdd_is_const(bdd::BDD) = !bdd_is_var(bdd)

"""
Composes multiple variables into a BDD according to given BDDs.
Returns: BDD
"""
function bdd_vector_compose(f::BDD, vars::Vector{Label}, bdds::Vector{BDD})
    @assert length(vars) == length(bdds) "Number of variables must match number of BDDs"
    result = f
    for (var, bdd) in zip(vars, bdds)
        result = bdd_compose(result, var, bdd)
    end
    result
end

function Base.isequal(a::BDD, b::BDD)
    return bdd_eq(a, b)
end


"""
Checks if a BDD has a variable.
Returns: Bool
"""
bdd_has_variable(bdd::BDD, var::Label) = @rsdd_timed ccall(bdd_has_variable_ptr, Bool, (ManagerPtr, Csize_t, Label), bdd.manager.ptr, bdd.ptr, var)

# Convenience operators
Base.:&(a::BDD, b::BDD) = bdd_and(a, b)
Base.:|(a::BDD, b::BDD) = bdd_or(a, b)
Base.:!(a::BDD) = bdd_negate(a)
Base.:⊻(a::BDD, b::BDD) = bdd_xor(a, b)
Base.:(==)(a::BDD, b::BDD) = bdd_eq(a, b)
Base.:(!=)(a::BDD, b::BDD) = !bdd_eq(a, b)
(⟺)(a::BDD, b::BDD) = bdd_iff(a, b)


"""
Creates a new WmcParams object for floating-point weights.
Returns: WmcParams
"""
function new_weights()
    ptr = @rsdd_timed ccall(new_wmc_params_f64_ptr, Ptr{Cvoid}, ())
    WmcParams(ptr, false)
end

"""
Creates a new WmcParams object for dual floating-point weights.
Returns: WmcParams
"""
function new_weights_dual(vector_size::Integer)
    ptr = @rsdd_timed ccall(new_wmc_params_f64_dual_ptr, Ptr{Cvoid}, ())
    WmcParamsDual(ptr, false, vector_size)
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
    @rsdd_timed ccall(wmc_param_f64_set_weight_ptr, Cvoid, (Ptr{Cvoid}, Label, Float64, Float64), params.ptr, var, low, high)
end

"""
Sets the weight for a variable in the WmcParamsDual object.
"""
function set_weight(params::WmcParamsDual, var::Label, low::Float64, high::Float64)
    # Create empty vectors of the right size
    low_dual = zeros(Float64, params.vector_size)
    high_dual = zeros(Float64, params.vector_size)
    
    # Call the updated function with size parameters
    @rsdd_timed ccall(wmc_param_f64_set_weight_deriv_dual_ptr, Cvoid, 
        (Ptr{Cvoid}, Label, Float64, Ptr{Float64}, Csize_t, Float64, Ptr{Float64}, Csize_t), 
        params.ptr, var, low, low_dual, params.vector_size, high, high_dual, params.vector_size)
end

"""
Sets the weight for a variable in the WmcParamsDual object with metaparam.
"""
function set_weight_dual(mgr::Manager, var::Label, metaparam::UInt, low::Float64, high::Float64)
    set_weight_dual(mgr.weights, var, metaparam, low, high)
end

"""
Sets the weight for a variable in the WmcParamsDual object with metaparam.
"""
function set_weight_dual(params::WmcParamsDual, var::Label, metaparam::UInt, low::Float64, high::Float64)
    # Added vector_size parameter
    @rsdd_timed ccall(wmc_param_f64_set_weight_dual_ptr, Cvoid, 
        (Ptr{Cvoid}, Label, Csize_t, Csize_t, Float64, Float64), 
        params.ptr, var, metaparam, params.vector_size, low, high)
end

"""
Sets the weight and derivative for a variable in the WmcParamsDual object. 
"""
function set_weight_deriv(params::WmcParamsDual, var::Label, low::Float64, low_dual::Vector{Float64}, high::Float64, high_dual::Vector{Float64})
    # Get sizes of vectors
    low_size = length(low_dual)
    high_size = length(high_dual)
    
    @rsdd_timed ccall(wmc_param_f64_set_weight_deriv_dual_ptr, Cvoid, 
        (Ptr{Cvoid}, Label, Float64, Ptr{Float64}, Csize_t, Float64, Ptr{Float64}, Csize_t), 
        params.ptr, var, low, low_dual, low_size, high, high_dual, high_size)
end

"""
Get a partial derivative from a vector pointer.
"""
function var_partial(partials::Ptr{Float64}, metaparam::UInt, size::UInt)
    # Added size parameter
    @rsdd_timed ccall(wmc_param_f64_var_partial_ptr, Float64, 
        (Ptr{Float64}, Csize_t, Csize_t), 
        partials, metaparam, size)
end

"""
Performs weighted model counting on a BDD.
Returns: Float64
"""
function bdd_wmc(bdd::BDD)
    bdd_wmc_manual(bdd, bdd.manager.weights)
end

function bdd_wmc_manual(bdd::BDD, params::WmcParams)
    @rsdd_timed ccall(bdd_wmc_ptr, Float64, (Csize_t, Ptr{Cvoid}), bdd.ptr, params.ptr)
end

function bdd_wmc_manual(bdd::BDD, params::WmcParamsDual)
    # Updated to handle size
    @rsdd_timed result = ccall(bdd_wmc_dual_ptr, WmcDual, (Csize_t, Ptr{Cvoid}), bdd.ptr, params.ptr)
    (result._0, result._1, result._size)
end

function bdd_wmc_dual(bdd::BDD, params::WmcParamsDual)
    # Updated to handle size
    result = ccall(bdd_wmc_dual_ptr, WmcDual, (Csize_t, Ptr{Cvoid}), bdd.ptr, params.ptr)
    (result._0, result._1, result._size)
end

# """
# Frees the memory associated with a BDD.
# """
function free_bdd(bdd::BDD)
    @rsdd_timed ccall(free_bdd_ptr, Cvoid, (Csize_t,), bdd.ptr)
end

"""
Frees the memory associated with a BDD manager.
"""
function free_bdd_manager(manager::Manager)
    free_wmc_params(manager.weights)
    manager.freed && return
    for bdd in manager.bdds
        free_bdd(bdd)
    end
    manager.bdds = []
    manager.freed = true
    @rsdd_timed ccall(free_bdd_manager_ptr, Cvoid, (ManagerPtr,), manager.ptr)
end

"""
Frees the memory associated with a WmcParams object.
"""
function free_wmc_params(params::WmcParams)
    params.freed && return
    @rsdd_timed ccall(free_wmc_params_ptr, Cvoid, (Ptr{Cvoid},), params.ptr)
    params.freed = true
    return
end

"""
Frees the memory associated with a WmcParams object.
"""
function free_wmc_params(params::WmcParamsDual)
    params.freed && return
    @rsdd_timed ccall(free_wmc_params_dual_ptr, Cvoid, (Ptr{Cvoid},), params.ptr)
    params.freed = true
    return
end

"""
Frees the memory associated with derivative vectors.
"""
function free_wmc_dual_derivatives(ptr::Ptr{Float64}, size::Integer)
    @rsdd_timed ccall(free_wmc_dual_derivatives_ptr, Cvoid, (Ptr{Float64}, Csize_t), ptr, size)
end

"""
Creates a new variable at a specified position in the BDD manager's variable order.

# Arguments
- `manager::Manager`: The BDD manager.
- `position::Integer`: The position at which to insert the new variable.
- `polarity::Bool`: The polarity of the new variable (true for positive, false for negative).

# Returns
A new BDD representing the variable.
"""
function bdd_new_var_at_position(manager::Manager, position::Integer, polarity::Bool)
    ptr = @rsdd_timed ccall(bdd_new_var_at_position_ptr, Csize_t, (ManagerPtr, Csize_t, Bool), manager.ptr, position, polarity)
    BDD(manager, ptr)
end

"""
Gets the size of a DualNumber vector.
"""
function dual_number_get_size(dual_ptr::Ptr{Cvoid})
    @rsdd_timed ccall(dual_number_get_size_ptr, Csize_t, (Ptr{Cvoid},), dual_ptr)
end

"""
Creates a DualNumber with a specified size.
"""
function dual_number_create(value::Float64, size::Integer)
    @rsdd_timed ccall(dual_number_create_ptr, Ptr{Cvoid}, (Float64, Csize_t), value, size)
end

struct WeightedSampleResult
    sample::Csize_t
    probability::Cdouble
end

"""
Performs weighted sampling on a BDD.
Returns: Tuple of (BDD, Float64) representing the sampled BDD and its probability
"""
function weighted_sample(bdd::BDD, wmc_params::WmcParams)
    result = @rsdd_timed ccall(robdd_weighted_sample_ptr, WeightedSampleResult,
        (ManagerPtr, Csize_t, Ptr{Cvoid}),
        bdd.manager.ptr, bdd.ptr, wmc_params.ptr)

    sample_bdd = BDD(bdd.manager, result.sample)
    probability = result.probability

    return (sample_bdd, probability)
end

function bdd_top_k_paths(bdd::BDD, k::Integer, wmc_params::WmcParams)
    ptr = @rsdd_timed ccall(robdd_top_k_paths_ptr, Csize_t, (ManagerPtr, Csize_t, Csize_t, Ptr{Cvoid}), bdd.manager.ptr, bdd.ptr, k, wmc_params.ptr)
    BDD(bdd.manager, ptr)
end

"""
Sets a time limit for the BDD manager and starts the clock.
"""
function bdd_set_time_limit(manager::Manager, time_limit)
    if !isnothing(time_limit)
        manager.active_time_limit = time_limit
        manager.hit_time_limit = false
    end
    nothing
end

"""
Sets a time limit for the BDD manager and starts the clock.
"""
function bdd_start_time_limit(manager::Manager)
    if !isnothing(manager.active_time_limit) && !isnothing(manager.active_time_limit.time_limit)
        remaining_time = remaining_time_lower_bound(manager.active_time_limit)
        ccall(start_bdd_manager_time_limit_ptr, Cvoid, (ManagerPtr, Cdouble), manager.ptr, remaining_time)
    end
end

"""
Stops the BDD manager time limit.
"""
function bdd_stop_time_limit(manager::Manager)
    if !isnothing(manager.active_time_limit)
        hit_limit = ccall(bdd_manager_time_limit_exceeded_ptr, Bool, (ManagerPtr,), manager.ptr)
        manager.hit_time_limit |= hit_limit    
        ccall(stop_bdd_manager_time_limit_ptr, Cvoid, (ManagerPtr,), manager.ptr)
    end
end

"""
Checks if the BDD manager time limit has been exceeded.
Returns: Bool
"""
function bdd_time_limit_exceeded(manager::Manager)
    manager.hit_time_limit
end

# Add these to the exports at the end of the file
export free_bdd, 
free_bdd_manager, 
free_wmc_params, 
bdd_new_var_at_position, 
weighted_sample, 
bdd_top_k_paths, 
free_wmc_params_dual,
free_wmc_dual_derivatives,
dual_number_get_size,
dual_number_create,
bdd_var_position, 
bdd_last_var,
bdd_set_time_limit,
bdd_stop_time_limit,
bdd_time_limit_exceeded

end # module