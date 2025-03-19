# Compiling programs to BDDs.

using .RSDD

manager = RSDD.mk_bdd_manager_default_order(0)

# struct BDDEnumValue
#     # is_constructor[c] is a true formula when this value is constructor c
#     # any constructor that is not represented is assumed to be false.
#     is_constructor::Dict{Symbol, BDD}
#     # values[c] is a list of (guard, thunks) pairs, where when guard is true,
#     # and is_constructor[c] is true, the thunks represent the arguments 
#     # to the constructor.
#     values::Dict{Symbol, Vector{Tuple{BDD, Vector{BDDThunk}}}}
# end

function memoize(f)
    cache = Dict()
    return (args...) -> begin
        if haskey(cache, args)
            return cache[args]
        else
            val = f(args...)
            cache[args] = val
            return val
        end
    end
end

struct CompileState
    # current_thunk::BDDThunk
    address::Vector{Symbol}
    names::Dict{Vector{Symbol}, BDD}
end

function constant_function(val)
    function constant_function_impl(state::CompileState)
        return val
    end
    return constant_function_impl
end

# Return and bind of a monad...
function bdd_return(val)
    function compute_return(world::BDD)
        return [(val, world)]
    end
    return compute_return
end

function bdd_bind(vals, f)
    function compiled_bind(world::BDD)
        #bind_id = gensym("bdd_bind")
        #println("$(bind_id): Running bdd_bind. Incoming world: $world")
        # Run vals on world and state.
        possible_values = vals(world)
        #println("$(bind_id): Possible values from first part of bind:")
        #println([(v isa Tuple && length(v) > 0 && v[1] isa Symbol ? v[1] : "lambda", g) for (v, g) in possible_values])
        # Each value comes with a guard.
        # Running f on a value yields a function of world and state.
        ret_possibilities = Dict()
        for (val, guard) in possible_values
            if RSDD.bdd_is_false(guard)
                #println("$(bind_id): Guard for $(val isa Tuple ? val[1] : "lambda") is false, skipping.")
                continue
            end
            # Run f on val and guard.
            # println("$(bind_id): Running f on $(val isa Tuple ? val[1] : "lambda") and $guard... when anded with $world, guard is $(world & guard)")
            for (ret, retguard) in f(val)(world & guard)
                if RSDD.bdd_is_false(retguard)
                    #println("$(bind_id): Result guard for $(ret isa Tuple ? ret[1] : "lambda") is false, skipping.")
                    continue
                end
                if haskey(ret_possibilities, ret)
                    #println("$(bind_id): Result $(ret isa Tuple ? ret[1] : "lambda") already has a guard, combining with $retguard...")
                    ret_possibilities[ret] = RSDD.bdd_or(ret_possibilities[ret], retguard)
                    #println("$(bind_id): Result $(ret isa Tuple ? ret[1] : "lambda") now has guard $(ret_possibilities[ret]).")
                else
                    ret_possibilities[ret] = retguard
                    #println("$(bind_id): Result $(ret isa Tuple ? ret[1] : "lambda") did not have a guard, adding $retguard.")
                end
            end
        end
        # println("$(bind_id): Returning $([(k, v) for (k, v) in ret_possibilities])")
        return [(k, v) for (k, v) in ret_possibilities]
    end
    return compiled_bind
end

with_modified_address(f, state, new_address) = begin
    new_state = CompileState(copy(state.address), state.names)
    push!(new_state.address, new_address)
    return f(new_state)
end


# VARIABLES
function compile(e::Var)
    :(constant_function($(e.name)))
end

# FUNCTION APPLICATION
function compile(e::App)
    compiled_f_var = gensym("compiled_f")
    compiled_x_var = gensym("compiled_x")
    compiled_vals_var = gensym("compiled_vals")
    return quote
        (state -> begin
            $compiled_f_var = with_modified_address(state, :app_f) do state
                $(compile(e.f))(state)
            end
            $compiled_x_var = with_modified_address(state, :app_x) do state
                $(compile(e.x))(state)
            end
            $compiled_vals_var = with_modified_address(state, :app_call) do state
                bdd_bind($compiled_f_var, f -> f($compiled_x_var, state))
            end
            return $compiled_vals_var
        end)
    end
end

# LAMBDA ABSTRACTION
function compile(e::Abs)
    return quote
        (state -> begin
            function compiled_abs($(e.name), s)
                $(compile(e.body))(s)
            end
            return bdd_return(compiled_abs)
        end)
    end
end

# CONSTANT BOOLEAN
function compile(e::ConstBool)
    :(state -> bdd_return($(e.val ? (:True, ()) : (:False, ()))))
end

function compile(e::Construct)
    state_var = gensym("state")
    compiled_args = [
        quote
            begin
                with_modified_address($(state_var), Symbol($i)) do $(state_var)
                    compiled_arg = $(compile(arg))($(state_var))
                end
                compiled_arg
            end
        end for (i, arg) in enumerate(e.args)
    ]

    return quote
        ($state_var -> begin
            return bdd_return(($(QuoteNode(e.constructor)), Tuple([$(compiled_args...)])))
        end)
    end
end

# PRIMITIVE OPERATIONS - FLIP
function compile(e::PrimOp)
    return compile_prim(e.op, e.args)
end

function compile_prim(op::FlipOp, args::Vector)
    # Ignore args for now...
    return quote
        (state -> begin
            address = copy(state.address)
            #println("Flip at $address")
            world -> begin
                println("Evaluating flip at $address in world $world")
                # Check if this variable exists or not.
                if haskey(state.names, address)
                    var = state.names[address]
                else
                    var = RSDD.bdd_new_var(manager, true)
                    state.names[(address)] = var
                end
                return ([((:True, ()), world & var), ((:False, ()), world & !var)])
            end
        end)
    end
end

# PATTERN MATCHING
function compile(e::CaseOf)
    scrut_var = gensym("scrutinee")
    state_var = gensym("state")

    compiled_cases = []
    for (k, v) in e.cases
        # TODO: this does not allow for match to return a function type; fix later by only reading the right number of args based on type of constructor
        arg_names = []
        while v isa Abs
            push!(arg_names, v.name)
            v = v.body
        end

        assignments = [:($(arg_names[i]) = $(scrut_var)[2][i]) for i = 1:length(arg_names)]
        this_case = quote
            if $(scrut_var)[1] == $(QuoteNode(k))
                # assign the arguments to the variables
                return with_modified_address($(state_var), :case_branch) do $(state_var)
                    $(assignments...)
                    $(compile(v))($state_var)
                end
            end
        end
        push!(compiled_cases, this_case)
    end

    scrutinee_var = gensym("scrutinee")
    cont_var = gensym("cont")
    return quote
        ($state_var) -> begin
            # Compile the scrutinee.
            $scrutinee_var = with_modified_address($(state_var), :case_scrutinee) do $(state_var)
                $(compile(e.scrutinee))($(state_var))
            end

            # Compile the branches.
            $cont_var = ($scrut_var -> begin
                $(compiled_cases...)
                return (world -> [])
            end)
            return bdd_bind($scrutinee_var, $cont_var)
        end
    end
end

function run_forward(expr)
    state = CompileState([], Dict())
    results = Base.invokelatest(Base.invokelatest(eval(compile(parse_expr(expr))), state), RSDD.bdd_true(manager))
    return results, state
end

run_forward(
    "((λ s1 -> ((λ route -> ((λ s2 -> ((λ s3 -> ((λ drop -> (case s2 of True => true | False => (case s3 of True => (case drop of True => false | False => true) | False => false))) (flip 0.0001))) (case route of True => false | False => s1))) (case route of True => s1 | False => false))) (flip 0.5))) true)",
)

function compile_to_julia_file(expr, filename)
    open(filename, "w") do f
        write(f, string(compile(parse_expr(expr))))
    end
end

compile_to_julia_file(
    "((λ diamond -> (diamond (diamond true))) (λ s1 -> ((λ route -> ((λ s2 -> ((λ s3 -> ((λ drop -> (case s2 of True => (True) | False => (case s3 of True => (case drop of True => (False) | False => (True)) | False => (False)))) (flip 0.0001))) (case route of True => (False) | False => s1))) (case route of True => s1 | False => (False)))) (flip 0.5))))",
    "diamond.jl",
)

alternative_diamond_program_small = "(λ s1 -> ((λ route -> ((λ drop -> (case drop of True => (case route of True => s1 | False => (False)) | False => s1)) (flip 0.0001))) (flip 0.5)))"
run_forward("((λ diamond -> (diamond (diamond (diamond true)))) $alternative_diamond_program_small)")
alternative_diamond_program_large = "(λ s1 -> ((λ route -> ((λ drop -> (case route of True => s1 | False => (case drop of True => (False) | False => s1))) (flip 0.0001))) (flip 0.5)))"
run_forward("((λ diamond -> (diamond (diamond (diamond true)))) $alternative_diamond_program_large)")

compiled_program = eval(compile(parse_expr(
    "((λ diamond -> (diamond (diamond (diamond true)))) $alternative_diamond_program_small)",
)))


compiled_program = eval(compile(parse_expr(
    "((λ diamond -> (diamond (diamond (diamond true)))) $alternative_diamond_program_large)",
)))



function test_diamond()
    Int(bdd_size(compiled_program(CompileState([], Dict()))(RSDD.bdd_true(manager))[2][2]))
end

@time Int(bdd_size(run_forward("((λ diamond -> (diamond (diamond (diamond true)))) $alternative_diamond_program_small)")[1][2][2]))
@time Int(bdd_size(run_forward("((λ diamond -> (diamond (diamond (diamond true)))) $alternative_diamond_program_large)")[1][2][2]))



run_forward(
    "((λ diamond -> (diamond (diamond true))) (λ s1 -> ((λ route -> ((λ s2 -> ((λ s3 -> ((λ drop -> (case s2 of True => (True) | False => (case s3 of True => (case drop of True => (False) | False => (True)) | False => (False)))) (flip 0.0001))) (case route of True => (False) | False => s1))) (case route of True => s1 | False => (False)))) (flip 0.5))))",
)


@define "diamond" "(λ s1 -> ((λ route -> ((λ s2 -> ((λ s3 -> ((λ drop -> (case s2 of True => true | False => (case s3 of True => (case drop of True => false | False => true) | False => false))) (flip 0.0001))) (case route of True => false | False => s1))) (case route of True => s1 | False => false))) (flip 0.5)))"
@define "dice_program" "(diamond true)"

# lazy paths:
#   - see that outer-route is true, so set outer-s2 to outer-s1, then see that inner-route is true, so set inner-s2 to inner-s1 (true), return true
#     (outer-route, inner-route) -> true
#   - see that outer-route is true, so set outer-s2 to outer-s1, then see that inner-route is false, so set inner-s2 to false, set inner-s3 to inner-s1 (true), check inner-drop and see true, so outer-s1 is false, hence outer-s2 is false, outer-s3 is false, return false
#     (outer-route, !inner-route, inner-drop) -> false

# Result of s2 in outer diamond: [((:False, ()), !(92, F, (93, !(94, T, (95, F, T)), (94, F, T)))), ((:True, ()), (92, F, (93, !(94, T, (95, F, T)), (94, F, T))))]
#    Indicates that s2 can be false in two ways: either 92 (outer route) is false, or 92 (outer route) is true and outer-s1 (inner diamond call) is true.
#    But why is "inner diamond call is true" what it is?

# Note: if outer route is false, then we don't *yet* evaluate inner diamond. That comes later.
# Therefore, the inner diamond's route coin flip (when we are evaluating s1 in the case where outer route is true)
#   is that outer-route and inner-route are both true; it will be false iff outer route is true and inner route is false.



# We need representations of:
# - algebraic data types
# - function types [i.e. closures]
# - reals (arguments to `flip`)

# It doesn't seem like we want to precompile higher-order functions
# to use a generic closure type for the argument, because essentially
# the compiled function would need to have a formula that accounts for 
# every possible function argument it might be called with.
# One option is a more specific type for each variable of function type,
# which is compiled based on an analysis of what functions it can possibly
# be called with. Note however that this means we cannot precompile 
# defined higher-order functions before they are used in a program.