# Julia bindings for the Rust RSDD library.
# To use, first make sure to build rsdd with the ffi feature flag on.
export RSDD

module RSDD

using Libdl


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
    global bdd_wmc_ptr = C_NULL
    global free_bdd_ptr = C_NULL
    global free_bdd_manager_ptr = C_NULL
    global free_wmc_params_ptr = C_NULL
    global bdd_new_var_at_position_ptr = C_NULL
    global robdd_weighted_sample_ptr = C_NULL
    global robdd_top_k_paths_ptr = C_NULL
    global bdd_last_var_ptr = C_NULL
    global bdd_var_position_ptr = C_NULL
end


# Define types
const ManagerPtr = Ptr{Cvoid}
const Label = Csize_t

mutable struct Manager
    ptr::ManagerPtr
    bdds::Vector{Any}
    freed::Bool
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
    # global bdd_is_var_ptr = get_symbol("bdd_is_var")
    # global man_print_stats_ptr = get_symbol("man_print_stats")
    # global bdd_is_const_ptr = get_symbol("bdd_is_const")
    # global bdd_hash_ptr = get_symbol("bdd_hash")
    # Add these new symbol lookups
    global new_wmc_params_f64_ptr = get_symbol("new_wmc_params_f64")
    global wmc_param_f64_set_weight_ptr = get_symbol("wmc_param_f64_set_weight")
    global bdd_wmc_ptr = get_symbol("bdd_wmc")
    # Add these to the __init__() function
    global free_bdd_ptr = get_symbol("free_bdd")
    global free_bdd_manager_ptr = get_symbol("free_bdd_manager")
    global free_wmc_params_ptr = get_symbol("free_wmc_params")
    global bdd_new_var_at_position_ptr = get_symbol("bdd_new_var_at_position")
    global robdd_weighted_sample_ptr = get_symbol("robdd_weighted_sample")
    global robdd_top_k_paths_ptr = get_symbol("robdd_top_k_paths")
    # global bdd_last_var_ptr = get_symbol("bdd_last_var")
    # global bdd_var_position_ptr = get_symbol("bdd_var_position")
    # println("Initialized RSDD")
end



# Define BDD struct
struct BDD
    manager::Manager
    ptr::Csize_t
    function BDD(manager::Manager, ptr::Csize_t)
        bdd = new(manager, ptr)
        push!(manager.bdds, bdd)
        return bdd
    end
end

# Show method for BDD
Base.show(io::IO, bdd::BDD) = print(io, print_bdd_string(bdd))

"""
Creates a new BDD manager with default variable order.
Returns: Manager (Ptr{Cvoid})
"""
function mk_bdd_manager_default_order(num_vars::Integer)
    ptr = ccall(mk_bdd_manager_default_order_ptr, ManagerPtr, (Cint,), num_vars)
    Manager(ptr, [], false)
end

"""
Creates a new BDD variable.
Returns: BDD
"""
function bdd_new_var(manager::Manager, polarity::Bool)
    ptr = ccall(bdd_new_var_ptr, Csize_t, (ManagerPtr, Bool), manager.ptr, polarity)
    BDD(manager, ptr)
end

export BDDTime, bdd_time, reset_bdd_time
mutable struct BDDTime
    bdd_and::Float64
    bdd_or::Float64
end
const bdd_time = BDDTime(0.0, 0.0)

function reset_bdd_time()
    bdd_time.bdd_and = 0.0
    bdd_time.bdd_or = 0.0
end


"""
Performs logical AND operation on two BDDs.
Returns: BDD
"""
function bdd_and(a::BDD, b::BDD)
    # tstart = time()
    @assert a.manager == b.manager "BDDs must belong to the same manager"
    ptr = ccall(bdd_and_ptr, Csize_t, (ManagerPtr, Csize_t, Csize_t), a.manager.ptr, a.ptr, b.ptr)
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
    ptr = ccall(bdd_or_ptr, Csize_t, (ManagerPtr, Csize_t, Csize_t), a.manager.ptr, a.ptr, b.ptr)
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
    ptr = ccall(bdd_iff_ptr, Csize_t, (ManagerPtr, Csize_t, Csize_t), a.manager.ptr, a.ptr, b.ptr)
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
    ptr = ccall(bdd_negate_ptr, Csize_t, (ManagerPtr, Csize_t), bdd.manager.ptr, bdd.ptr)
    BDD(bdd.manager, ptr)
end

"""
Checks if a BDD represents the constant true.
Returns: Bool
"""
bdd_is_true(bdd::BDD) = ccall(bdd_is_true_ptr, Bool, (Csize_t,), bdd.ptr)

"""
Checks if a BDD represents the constant false.
Returns: Bool
"""
bdd_is_false(bdd::BDD) = ccall(bdd_is_false_ptr, Bool, (Csize_t,), bdd.ptr)

"""
Creates a BDD representing the constant true.
Returns: BDD
"""
function bdd_true(manager::Manager)
    ptr = ccall(bdd_true_ptr, Csize_t, (Manager,), manager)
    BDD(manager, ptr)
end

"""
Creates a BDD representing the constant false.
Returns: BDD
"""
function bdd_false(manager::Manager)
    ptr = ccall(bdd_false_ptr, Csize_t, (Manager,), manager)
    BDD(manager, ptr)
end

"""
Performs if-then-else operation on three BDDs.
Returns: BDD
"""
function bdd_ite(f::BDD, g::BDD, h::BDD)
    @assert f.manager == g.manager == h.manager "BDDs must belong to the same manager"
    ptr = ccall(bdd_ite_ptr, Csize_t, (ManagerPtr, Csize_t, Csize_t, Csize_t), f.manager.ptr, f.ptr, g.ptr, h.ptr)
    BDD(f.manager, ptr)
end

"""
Checks if two BDDs are equal.
Returns: Bool
"""
function bdd_eq(a::BDD, b::BDD)
    @assert a.manager == b.manager "BDDs must belong to the same manager"
    ccall(bdd_eq_ptr, Bool, (ManagerPtr, Csize_t, Csize_t), a.manager.ptr, a.ptr, b.ptr)
end

"""
Gets the high child of a BDD node.
Returns: BDD
"""
function bdd_high(bdd::BDD)
    ptr = ccall(bdd_high_ptr, Csize_t, (ManagerPtr, Csize_t), bdd.manager.ptr, bdd.ptr)
    BDD(bdd.manager, ptr)
end

"""
Gets the low child of a BDD node.
Returns: BDD
"""
function bdd_low(bdd::BDD)
    ptr = ccall(bdd_low_ptr, Csize_t, (ManagerPtr, Csize_t), bdd.manager.ptr, bdd.ptr)
    BDD(bdd.manager, ptr)
end

"""
Gets the top variable of a BDD.
Returns: Label (Csize_t)
"""
bdd_topvar(bdd::BDD) = ccall(bdd_topvar_ptr, Label, (Csize_t,), bdd.ptr)

"""
Gets the number of recursive calls made by the BDD manager.
Returns: UInt64
"""
bdd_num_recursive_calls(manager::Manager) = ccall(bdd_num_recursive_calls_ptr, UInt64, (ManagerPtr,), manager.ptr)

"""
Prints a BDD to a string.
Returns: String
"""
function print_bdd_string(bdd::BDD)
    cstr = ccall(print_bdd_ptr, Ptr{Cchar}, (Csize_t,), bdd.ptr)
    return unsafe_string(cstr)
end

"""
Prints a BDD to a JSON string.
Returns: String
"""
function bdd_json(bdd::BDD)
    cstr = ccall(bdd_json_ptr, Ptr{Cchar}, (Csize_t,), bdd.ptr)
    return unsafe_string(cstr)
end

"""
Existentially quantifies a variable in a BDD.
Returns: BDD
"""
function bdd_exists(bdd::BDD, var::Label)
    ptr = ccall(bdd_exists_ptr, Csize_t, (ManagerPtr, Csize_t, Label), bdd.manager.ptr, bdd.ptr, var)
    BDD(bdd.manager, ptr)
end

"""
Conditions a BDD on a variable.
Returns: BDD
"""
function bdd_condition(bdd::BDD, var::Label, value::Bool)
    ptr = ccall(bdd_condition_ptr, Csize_t, (ManagerPtr, Csize_t, Label, Bool), bdd.manager.ptr, bdd.ptr, var, value)
    BDD(bdd.manager, ptr)
end

"""
Composes a BDD by substituting a variable with another BDD.
Returns: BDD
"""
function bdd_compose(f::BDD, var::Label, g::BDD)
    @assert f.manager == g.manager "BDDs must belong to the same manager"
    ptr = ccall(bdd_compose_ptr, Csize_t, (ManagerPtr, Csize_t, Label, Csize_t), f.manager.ptr, f.ptr, var, g.ptr)
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
bdd_size(bdd::BDD) = ccall(bdd_size_ptr, UInt64, (Csize_t,), bdd.ptr)

"""
Checks if a BDD represents a variable.
Returns: Bool
"""
bdd_is_var(bdd::BDD) = ccall(bdd_is_var_ptr, Bool, (ManagerPtr, Csize_t), bdd.manager.ptr, bdd.ptr)

"""
Prints statistics about the BDD manager.
"""
man_print_stats(manager::Manager) = ccall(man_print_stats_ptr, Cvoid, (ManagerPtr,), manager.ptr)

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



# """
# Computes the hash of a BDD.
# Returns: UInt64
# """
# bdd_hash(bdd::BDD) = ccall(bdd_hash_ptr, UInt64, (Csize_t,), bdd.ptr)

# function Base.hash(bdd::BDD, h::UInt)
#     return Base.hash(bdd_hash(bdd), h)
# end

function Base.isequal(a::BDD, b::BDD)
    return bdd_eq(a, b)
end


"""
Checks if a BDD has a variable.
Returns: Bool
"""
bdd_has_variable(bdd::BDD, var::Label) = ccall(bdd_has_variable_ptr, Bool, (ManagerPtr, Csize_t, Label), bdd.manager.ptr, bdd.ptr, var)

# Convenience operators
Base.:&(a::BDD, b::BDD) = bdd_and(a, b)
Base.:|(a::BDD, b::BDD) = bdd_or(a, b)
Base.:!(a::BDD) = bdd_negate(a)
Base.:⊻(a::BDD, b::BDD) = bdd_xor(a, b)
Base.:(==)(a::BDD, b::BDD) = bdd_eq(a, b)
Base.:(!=)(a::BDD, b::BDD) = !bdd_eq(a, b)
(⟺)(a::BDD, b::BDD) = bdd_iff(a, b)
# (⟹)(a::BDD, b::BDD) = bdd_implies(a, b)

# Define WmcParams struct
struct WmcParams
    ptr::Ptr{Cvoid}
end

"""
Creates a new WmcParams object for floating-point weights.
Returns: WmcParams
"""
function new_wmc_params_f64()
    ptr = ccall(new_wmc_params_f64_ptr, Ptr{Cvoid}, ())
    WmcParams(ptr)
end

"""
Sets the weight for a variable in the WmcParams object.
"""
function wmc_param_f64_set_weight(params::WmcParams, var::Label, low::Float64, high::Float64)
    ccall(wmc_param_f64_set_weight_ptr, Cvoid, (Ptr{Cvoid}, Label, Float64, Float64), params.ptr, var, low, high)
end

"""
Performs weighted model counting on a BDD.
Returns: Float64
"""
function bdd_wmc(bdd::BDD, params::WmcParams)
    ccall(bdd_wmc_ptr, Float64, (Csize_t, Ptr{Cvoid}), bdd.ptr, params.ptr)
end

# """
# Constructs a WmcParams object from a dictionary mapping Labels to floats.
# The float values represent the high parameter, and 1 - float gives the low parameter.

# Parameters:
# - manager: The BDD manager
# - weights: A dictionary mapping Labels to floats

# Returns: WmcParams
# """
# function construct_wmc(weights::Dict{Label, Float64})
#     params = new_wmc_params_f64()

#     for label in keys(weights)
#         high = weights[label]
#         low = 1.0 - high
#         wmc_param_f64_set_weight(params, label, low, high)
#     end

#     return params
# end



# Add exports for the new functions
export WmcParams, new_wmc_params_f64, wmc_param_f64_set_weight, bdd_wmc

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
# Add these functions after the existing functions

# """
# Frees the memory associated with a BDD.
# """
function free_bdd(bdd::BDD)
    ccall(free_bdd_ptr, Cvoid, (Csize_t,), bdd.ptr)
end

"""
Frees the memory associated with a BDD manager.
"""
function free_bdd_manager(manager::Manager)
    manager.freed && return
    for bdd in manager.bdds
        free_bdd(bdd)
    end
    manager.bdds = []
    manager.freed = true
    ccall(free_bdd_manager_ptr, Cvoid, (ManagerPtr,), manager.ptr)
end

"""
Frees the memory associated with a WmcParams object.
"""
function free_wmc_params(params::WmcParams)
    ccall(free_wmc_params_ptr, Cvoid, (Ptr{Cvoid},), params.ptr)
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
    ptr = ccall(bdd_new_var_at_position_ptr, Csize_t, (ManagerPtr, Csize_t, Bool), manager.ptr, position, polarity)
    BDD(manager, ptr)
end

# """
# Gets the last variable in the variable order of a BDD.
# Returns: Union{Label,Nothing} - The last variable in the order, or nothing if the BDD is constant
# """
# function bdd_last_var(bdd::BDD)
#     var = ccall(bdd_last_var_ptr, Int64, (Manager, Csize_t), bdd.manager, bdd.ptr)
#     if var == -1
#         return nothing
#     end
#     return Label(var)
# end

# """
# Gets the position of a variable in the variable order of a BDD.
# Returns: UInt64
# """
# bdd_var_position(builder::Manager, var::Label) = ccall(bdd_var_position_ptr, UInt64, (Manager, Label), builder, var)

struct WeightedSampleResult
    sample::Csize_t
    probability::Cdouble
end
"""
Performs weighted sampling on a BDD.
Returns: Tuple of (BDD, Float64) representing the sampled BDD and its probability
"""
function weighted_sample(bdd::BDD, wmc_params::WmcParams)
    result = ccall(robdd_weighted_sample_ptr, WeightedSampleResult,
        (ManagerPtr, Csize_t, Ptr{Cvoid}),
        bdd.manager.ptr, bdd.ptr, wmc_params.ptr)

    sample_bdd = BDD(bdd.manager, result.sample)
    probability = result.probability

    return (sample_bdd, probability)
end

function bdd_top_k_paths(bdd::BDD, k::Integer, wmc_params::WmcParams)
    ptr = ccall(robdd_top_k_paths_ptr, Csize_t, (ManagerPtr, Csize_t, Csize_t, Ptr{Cvoid}), bdd.manager.ptr, bdd.ptr, k, wmc_params.ptr)
    BDD(bdd.manager, ptr)
end

# Add these to the exports at the end of the file
export free_bdd, free_bdd_manager, free_wmc_params, bdd_new_var_at_position, weighted_sample, bdd_top_k_paths, bdd_var_position, bdd_last_var

end # module