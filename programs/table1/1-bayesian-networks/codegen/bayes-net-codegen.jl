include("../../../../src/util/util.jl")

names = ["cancer", "survey", "alarm", "insurance", "hepar2", "hailfinder", "pigs", "water", "munin"]
raw_bayes_nets_dir = "programs/table1/1-bayesian-networks/codegen/raw_data"
pluck_format_dir = "programs/table1/1-bayesian-networks/"


# which variable to get the single marginal of
target_vars::Dict{String, Symbol} = Dict(
    "alarm" => :BP,
    "cancer" => :Dyspnoea,
    "hailfinder" => :R5Fcst,
    "hepar2" => :jaundice,
    "insurance" => :PropCost,
    "pigs" => :p48084991,
    "survey" => :T,
    "water" => :CNON_12_45,
    "munin" => :L_SUR_CV_CA
)

expected_outputs = Dict(
    "alarm" => [(:OptionLOW, 0.38999308773414654), (:OptionNORMAL, 0.20470776251260087), (:OptionHIGH, 0.4052991497532523)],
    "cancer" => [(:OptionTrue, 0.3040705), (:OptionFalse, 0.6959294999999999)],
    "hailfinder" => [(:OptionXNIL, 0.25206480542413834), (:OptionSIG, 0.44059947932150173), (:OptionSVR, 0.3073357152543599)],
    "hepar2" => [(:Optionpresent, 0.2719147607671873), (:Optionabsent, 0.7280852392328125)],
    "insurance" => [(:OptionThousand, 0.5629455909005231), (:OptionTenThou, 0.3151875947814524), (:OptionHundredThou, 0.10507029426792233), (:OptionMillion, 0.01679652005010235)],
    "pigs" => [(:Option0, 0.2656249999748047), (:Option1, 0.4687500000078124), (:Option2, 0.2656250000173828)],
    "survey" => [(:Optioncar, 0.5618339760097999), (:Optiontrain, 0.28085725199020023), (:Optionother, 0.15730877199999996)],
    "water" => [(:Option2_MG_L, 0.004161748754297062), (:Option4_MG_L, 0.9047758779258376), (:Option6_MG_L, 0.09106235327587024), (:Option10_MG_L, 2.0043995018129032e-8)],
    "munin" => [(:OptionM_S00, 0.008716364148532453), (:OptionM_S04, 0.0001237557537930512), (:OptionM_S08, 0.0008255742377163428), (:OptionM_S12, 0.0015344946621133775), (:OptionM_S16, 0.0015667764969255586), (:OptionM_S20, 0.0013746809661952988), (:OptionM_S24, 0.0018831614905352439), (:OptionM_S28, 0.0020968149527313216), (:OptionM_S32, 0.004044895489278196), (:OptionM_S36, 0.009388818407956679), (:OptionM_S40, 0.034088231795036374), (:OptionM_S44, 0.09472751695144571), (:OptionM_S48, 0.29201934141813285), (:OptionM_S52, 0.3541139707266835), (:OptionM_S56, 0.15438224661460737), (:OptionM_S60, 0.03637682276538774), (:OptionM_S_64, 0.0027365331229289008)]
)

function generate_benchmarks()
    for (i, name) in enumerate(names)
        code = generate_benchmark(name)
        outfile = "$pluck_format_dir/$i-$name.pluck"
        write(outfile, code)
    end
end

function generate_benchmark(name; use_int_dist=false, remove_unused=false, dice_ordering=true)
    vars, probs, types = parse_bif("$raw_bayes_nets_dir/$name.bif")

    # either match ordering to dice's ordering, or do a topological_sort
    if dice_ordering
        var_order = get_var_order(name)
        @assert length(var_order) == length(probs)
        probs = sort(probs, by = p -> findfirst(==(p.target), var_order))
    else
        probs = topological_sort(probs)
    end

    # decide on the target var
    target_var = target_vars[String(name)]

    if remove_unused
        probs = remove_unused_vars(probs, target_var)
    end

    type_defs = generate_type_defs(types)

    bn_code = generate_bayes_net_code(vars, probs, target_var; use_int_dist=use_int_dist)

    expected = expected_outputs[String(name)]
    expected_pairs = join([" (($val) $prob)" for (val, prob) in expected], "\n")
    marginal_code = "(assert-query '$name (Marginal $bn_code)\n$expected_pairs)"

    return type_defs * "\n" * marginal_code
end

struct PluckType
    name::Symbol
    domain::Vector{Symbol}
end

function generate_type_defs(types::Vector{PluckType})
    type_defs = String[]
    for type in types
        push!(type_defs, "(define-type " * string(type.name) * " " * join(["($val)" for val in type.domain], " ") * ")")
    end
    return join(type_defs, "\n")
end


struct Variable
    name::Symbol
    domain::Vector{Symbol}
end

bitwidth(var::Variable) = ceil(Int, log2(length(var.domain)))

function mk_int(var::Variable, i::Int; use_int_dist=false)
    @assert use_int_dist
    @assert i > 0 && i <= length(var.domain)
    width = bitwidth(var)
    return "(mk_int @$width @$(i-1))"
end

function mk_int(var::Variable, val::Symbol; use_int_dist=false)
    if !use_int_dist
        return "($(val))"
    end
    idx = findfirst(==(val), var.domain)
    @assert idx !== nothing
    return mk_int(var, idx; use_int_dist=use_int_dist)
end

function mk_eq(var::Variable, x, y; use_int_dist=false)
    equality = use_int_dist ? "int_dist_eq" : "constructors_equal"
    return "($equality $x $y)"
end

struct ProbabilityStatement
    target::Symbol
    parents::Vector{Symbol}
    # For conditional probabilities, this is a Dict mapping parent combinations to probability vectors
    # For marginal probabilities, this is just a single probability vector
    probabilities::Union{Vector{Float64}, Dict{Vector{Symbol}, Vector{Float64}}}
end


# define_type!(type_name, Dict(val => Symbol[] for val in domain))


function parse_bif(filename::String)
    variables = Dict{Symbol, Variable}()
    probabilities = Vector{ProbabilityStatement}()
    types = Vector{PluckType}()

    # Track unique domains to create type definitions
    domain_to_type = Dict{Vector{Symbol}, Symbol}()

    open(filename) do file
        content = read(file, String)
        # Remove comments and normalize whitespace
        content = replace(content, r"//.*$"m => "")
        content = replace(content, r"/\*.*?\*/"s => "")

        # Parse variable declarations
        for m in eachmatch(r"variable\s+(\w+)\s*\{\s*type\s+discrete\s*\[\s*(\d+)\s*\]\s*\{([^}]+)\}", content)
            name = Symbol(m[1])
            domain_size = parse(Int, m[2])
            # Add "Option" prefix to all domain values
            domain = [Symbol("Option" * strip(v)) for v in split(m[3], ",")]
            @assert length(domain) == domain_size

            variables[name] = Variable(name, domain)

            # If this is a new unique domain, create a type for it
            if !haskey(domain_to_type, domain)
                type_name = name  # Use first variable name as type name
                domain_to_type[domain] = type_name
                # define_type!(type_name, Dict(val => Symbol[] for val in domain))
                push!(types, PluckType(type_name, domain))
            end
        end

        # Parse probability statements
        for m in eachmatch(r"probability\s*\(\s*(\w+)(?:\s*\|\s*([^)]+))?\s*\)\s*\{([^}]+)\}", content)
            target = Symbol(m[1])
            parents = isnothing(m[2]) ? Symbol[] : [Symbol(strip(p)) for p in split(m[2], ",")]
            prob_data = strip(m[3])

            if isempty(parents)
                # Parse marginal probability
                probs = parse_probability_table(prob_data)
                push!(probabilities, ProbabilityStatement(target, parents, probs))
            else
                # Parse conditional probability table
                cpt = Dict{Vector{Symbol}, Vector{Float64}}()
                for line in split(prob_data, ";")
                    line = strip(line)
                    isempty(line) && continue

                    # Parse parent values and corresponding probabilities
                    m = match(r"\((.*?)\)\s*(.*)", line)
                    parent_vals = [Symbol("Option" * strip(v)) for v in split(m[1], ",")]

                    #parent_vals = [Symbol(strip(v)) for v in split(m[1], ",")]
                    probs = parse_probability_table(m[2])
                    cpt[parent_vals] = probs
                end
                push!(probabilities, ProbabilityStatement(target, parents, cpt))
            end
        end
    end

    return variables, probabilities, types
end
function parse_probability_table(str)
    # Remove "table" keyword if present and any extra whitespace
    str = replace(str, r"^\s*table\s+" => "")
    # Remove any semicolons and extra whitespace
    str = replace(str, r"[;\s]+" => "")
    str = strip(str)
    # Parse the comma-separated probabilities
    return [parse(Float64, p) for p in split(str, ",")]
end

function generate_bayes_net_code(variables::Dict{Symbol, Variable}, probabilities::Vector{ProbabilityStatement}, target_var::Symbol; use_int_dist=false)
    # Generate let bindings
    bindings = String[]
    seen_vars = Set{Symbol}()  # Track variables we've already processed
    for prob in probabilities
        # Skip if we've already processed this variable
        if prob.target in seen_vars
            continue
        end
        push!(seen_vars, prob.target)

        if isempty(prob.parents)
            # Marginal probability
            var = variables[prob.target]
            values = [mk_int(var, val; use_int_dist=use_int_dist) for val in var.domain]
            # add a new let binding for the target variable
            push!(bindings, "$(prob.target) $(discrete(values, prob.probabilities))")
        else
            # Conditional probability
            expr = generate_conditional_distribution(prob, variables; use_int_dist=use_int_dist)
            push!(bindings, "$(prob.target) $expr")
        end
    end

    # Return the complete let expression with the return variable
    res = "(let ($(join(bindings, "\n      "))) $target_var)"
    return res
end


function generate_conditional_distribution(prob::ProbabilityStatement, variables::Dict{Symbol, Variable}; use_int_dist=false)
    # Handle single parent case directly
    if length(prob.parents) == 1
        parent = prob.parents[1]
        if use_int_dist
            # we build the dist for the last value first becuase it doesn't need an "if", it just sits in the last else branch
            last_val = variables[parent].domain[end]
            last_probs = prob.probabilities[[last_val]]
            last_values = [mk_int(variables[prob.target], val; use_int_dist=use_int_dist) for val in variables[prob.target].domain]
            expr = discrete(last_values, last_probs)

            # loop over domain of parent "B" (all except last variable)
            # for each of these variables, we build a new if-statement and put the previous result in the else branch
            for val in reverse(variables[parent].domain[1:end-1])
                probs = prob.probabilities[[val]] # P(A|B=val)
                var = variables[prob.target]
                values = [mk_int(var, val; use_int_dist=use_int_dist) for val in var.domain]
                if_cond = mk_eq(variables[parent], parent, mk_int(variables[parent], val; use_int_dist=use_int_dist); use_int_dist=use_int_dist)
                then_br = discrete(values, probs)
                expr = "(if $if_cond $then_br $expr)"
            end
            return expr
        else
            # this is the caseof version, instead of using int dists
            exprs = String[]
            for val in variables[parent].domain
                probs = prob.probabilities[[val]] # P(A|B=val)
                var = variables[prob.target]
                values = [mk_int(var, val; use_int_dist=use_int_dist) for val in var.domain]
                then_br = discrete(values, probs)
                expr = "$val -> $then_br"
                push!(exprs, expr)
            end
            expr = "(match $parent $(join(exprs, " ")))"
            return expr
        end
    end

    # For multiple parents, build from innermost to outermost
    # First, create a mapping of all parent value combinations to their probabilities
    parent_domains = [variables[p].domain for p in prob.parents]
    var = variables[prob.target]
    target_values = [mk_int(var, val; use_int_dist=use_int_dist) for val in var.domain]

    # Start with innermost expressions (the discrete distributions).
    current_exprs = Dict{Vector{Symbol}, String}()
    for parent_vals in Iterators.product(parent_domains...)
        parent_vals = collect(Symbol, parent_vals)
        probs = prob.probabilities[parent_vals]
        current_exprs[parent_vals] = discrete(target_values, probs)
    end

    # We're trying to generate a probabilistic program representing P(A | B,C,D)
    # And we have mappings from concrete parent values to distributions on target values
    # (which we can reify with discrete()).
    # Our approach is this: we first build an expression for P(A | B=b C=c D=d) and store it in current_exprs[bcd]
    # This is easy it's just discrete() and generates a flipnest 
    # Then we generate an expression for P(A | B=b C=c) and store it in current_exprs[bc]. This expression 
    # is going to end up casing on D and the branches of the case will be the current_exprs[bcd] expression we got 
    # at the previous step.
    # We do this until we get P(A).

    # Work backwards through parents, wrapping in case expressions
    for parent_idx = length(prob.parents):-1:1
        parent = prob.parents[parent_idx]
        new_exprs = Dict{Vector{Symbol}, String}()

        # Group expressions by their shared parent prefixes.
        # So at the previous step we generated things like P(A | B=b C=c D=d)
        # and stored them in current_exprs[bcd]
        # Now we're generating P(A | B=b C=c) and we want to store it in new_exprs[bc]
        # We do this by finding all the entries in current_exprs that have b and c in their prefix
        # and storing them in prefix_groups[bc]
        prefix_groups = Dict{Vector{Symbol}, Vector{Tuple{Symbol, String}}}()
        for (parent_vals, expr) in current_exprs
            prefix = parent_vals[1:parent_idx-1]
            val = parent_vals[parent_idx]
            if !haskey(prefix_groups, prefix)
                prefix_groups[prefix] = Tuple{Symbol, String}[]
            end
            push!(prefix_groups[prefix], (val, expr))
        end

        # Create case expression for each group. So we'll case on the parent we're eliminating 
        # at this step, "d", and the branches will be the expressions we got in the previous step
        for (prefix, cases_list) in prefix_groups

            sort!(cases_list, by = t -> findfirst(==(t[1]), variables[parent].domain))
            _, expr = cases_list[end]
    
            if use_int_dist
                for (val, then_br) in reverse(cases_list[1:end-1])
                    if_cond = mk_eq(variables[parent], parent, mk_int(variables[parent], val; use_int_dist=use_int_dist); use_int_dist=use_int_dist)
                    expr = "(if $if_cond $then_br $expr)"
                end
            else
                exprs = String[]
                for (val, then_br) in cases_list
                    e = "$val -> $then_br"
                    push!(exprs, e)
                end
                expr = "(match $parent $(join(exprs, " ")))"
            end

            new_exprs[prefix] = expr
        end

        current_exprs = new_exprs
    end

    # At the end, we should have a single expression
    @assert length(current_exprs) == 1
    return first(values(current_exprs))
end

function topological_sort(probabilities::Vector{ProbabilityStatement})
    remaining = copy(probabilities)
    sorted = ProbabilityStatement[]

    while !isempty(remaining)
        # Find all nodes with no parents in the remaining set
        no_parents = filter(p -> all(parent ∉ [r.target for r in remaining] for parent in p.parents), remaining)

        # If we can't find any nodes without parents, we have a cycle
        isempty(no_parents) && error("Cycle detected in Bayesian network")

        # Add these to sorted and remove from remaining
        append!(sorted, no_parents)
        filter!(p -> p ∉ no_parents, remaining)
    end

    return sorted
end

function remove_unused_vars(probabilities::Vector{ProbabilityStatement}, target::Symbol)
    # Find all variables that are parents of any probability statement
    relevant_vars = Set{Symbol}()
    worklist = Set{Symbol}([target])
    while !isempty(worklist)
        var = pop!(worklist)
        push!(relevant_vars, var)
        statement = findall(p -> p.target == var, probabilities)
        @assert length(statement) == 1
        statement = probabilities[first(statement)]
        for parent in statement.parents
            push!(worklist, parent)
        end
    end
    return filter(p -> p.target in relevant_vars, probabilities)
end


"""
Get the variable order from the .bif.dice file. so that we can use the same variable
order as dice
"""
function get_var_order(name)
    file = "$raw_bayes_nets_dir/$name.bif.dice"
    vars = Symbol[]
    open(file) do f
        for line in eachline(f)
            if startswith(line, "let ")
                # "parse let C_NI_12_00 = " into C_NI_12_00
                var = split(line, " = ")[1]
                var = split(var, "let ")[2]
                push!(vars, Symbol(var))
            end
        end
    end
    return vars
end