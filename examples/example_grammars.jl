
"""
A builder for constructing grammars incrementally. Supports adding rules with weights
and building up complex grammars piece by piece.
"""
struct GrammarBuilder
    rules::Dict{String, Vector{Pair{String, Int}}}
    GrammarBuilder() = new(Dict{String, Vector{Pair{String, Int}}}())
    GrammarBuilder(rule::String) = add_rule!(GrammarBuilder(), rule)
end

Base.getindex(g::GrammarBuilder, lhs::String) = g.rules[lhs]

"""
Add one or more rules to the grammar builder. Rules can be specified in several formats:
1. Single rule: "?foo => ?bar" adds ?bar as a RHS for ?foo with weight 1
2. Multiple rules: "?foo => ?bar 2 | ?baz 3" adds two RHS with weights 2 and 3
3. Multiple lines: "?foo => ?bar ; ?baz => ?qux" adds rules across multiple lines
"""
function add_rule!(g::GrammarBuilder, rule::String)
    # Split multiple rules separated by semicolons
    # Split multiple rules separated by semicolons or newlines
    for rule_part in split(rule, ";")
        rule_part = strip(rule_part)
        isempty(rule_part) && continue
        
        # Parse LHS => RHS
        @assert occursin("=>", rule_part) "Rule must contain => but didn't find it in $rule_part"
        lhs, rhs = split(rule_part, "=>")
        lhs = strip(lhs)

        if startswith(lhs, "??")
            @assert !haskey(g.rules, lhs[2:end]) "LHS $(lhs[3:end]) used with ?? in some places and ? in others"
        elseif startswith(lhs, "?")
            @assert !haskey(g.rules, "?" * lhs) "LHS $(lhs[2:end]) used with ? in some places and ?? in others"
        else
            error("Unexpected LHS, doesn't start with `?` or `??`: $lhs")
        end

        # Add to rules
        if !haskey(g.rules, lhs)
            g.rules[lhs] = Vector{Pair{String,Int}}()
        end
        
        # Split RHS alternatives
        for alt in split(rhs, "|")
            alt = strip(alt)
            
            # Parse weight if present
            parts = split(alt)
            if length(parts) > 1 && all(isdigit, parts[end])
                weight = parse(Int, pop!(parts))
                rhs_expr = join(parts, " ")
            else
                weight = 1
                rhs_expr = alt
            end
            push!(g.rules[lhs], strip(rhs_expr) => weight)
        end
    end
    g
end

# Define + operator to merge GrammarBuilders and handle string conversion
function Base.:+(g1::GrammarBuilder, g2::GrammarBuilder)
    result = GrammarBuilder()
    # Copy rules from g1
    for (lhs, rhss) in g1.rules
        result.rules[lhs] = copy(rhss) # shallow since Pair is immutable
    end
    # Merge rules from g2
    for (lhs, rhss) in g2.rules
        if !haskey(result.rules, lhs)
            result.rules[lhs] = Vector{Pair{String,Int}}()
        end
        append!(result.rules[lhs], rhss)
    end
    result
end

Base.:+(g::GrammarBuilder, rule::String) = g + GrammarBuilder(rule)
Base.:+(rule::String, g::GrammarBuilder) = GrammarBuilder(rule) + g

Base.:-(g::GrammarBuilder, rule::String) = remove_rule!(g, rule)

"""
Convert the GrammarBuilder to a Grammar with the given type mappings and size distribution
"""
function build(g::GrammarBuilder; size_dist=Geometric(0.5))

    sym_of_type = [lhs[2:end] => lhs for lhs in keys(g.rules) if !startswith(lhs, "??")] # int => ?int
    
    # Convert rules to format expected by Grammar constructor
    prods = []
    for (lhs, rhss) in g.rules
        rhs_vec = []
        for (rhs, weight) in rhss
            push!(rhs_vec, rhs => weight)
        end
        push!(prods, lhs => rhs_vec)
    end

    start_expr_of_type = Vector{Pair{String, String}}()
    
    Grammar(prods, sym_of_type, start_expr_of_type; size_dist=size_dist)
end

function Base.filter!(f, g::GrammarBuilder)
    for (lhs, rhss) in g.rules
        filter!(rhs_wt -> f(lhs, rhs_wt[1]), rhss)
    end
    g
end

function remove_rule!(g::GrammarBuilder, rhs::AbstractString; lhs=nothing, verbose=false, expect_one=true)
    count = 0
    filter!(g) do lhs_, rhs_expr
        res = occursin(rhs, rhs_expr) && (isnothing(lhs) || lhs == lhs_)
        count += res
        verbose && println("removed $lhs_ => $rhs_expr")
        !res
    end
    verbose && println("removed $count rules")
    expect_one && @assert count == 1 "$count rules removed by remove_rule!($rhs)"
    g
end


@define "plus10" "int -> int" "(λx -> (+ x 10))"


function alex_list_ppcfg(; isempty = false, length = true, append = true, append_one = true, caseof = false, size_dist = Geometric(0.5))
    prods = [
        "?int" => ["?int_term" => 6, "?int_nonterm" => 4],
        "?int_term" => ["(geom 0.2)", "#int", "?constint"],
        "?constint" => [("$i" for i ∈ 0:9)...],
        "?int_nonterm" => [
            "(index ?int ?list)",
            # "?arith",
            #"(length ?list)",
            "(car ?list)",
            "(if ?bool ?int ?int)",
            "(inc ?int)",
            "(dec ?int)",
            # "(plus10 ?int)",
            # "(+ ?int ?int)",
            # "(- ?int ?int)",
            # todo you prob do want to allow this:
            # (caseof ? ["(case ?list of Nil => ?int | Cons => (λhd tl -> ?int))"] : [])...,
            (length ? ["(length ?list)"] : [])...,
        ],
        "?list" => ["?list_term" => 6, "?list_nonterm" => 4],
        "?list_term" => ["#list", "(geom_list 0.5 0.2)", "make_nil"],
        "?list_nonterm" => [
            "(cons ?int ?list)",
            "(cdr_safe ?list)",
            "(mapi (λx i -> ?int) ?list)",
            "(filteri (λx i -> ?bool) ?list)",
            "(if ?bool ?list ?list)",
            (caseof ? ["(case ?list of Nil => ?list | Cons => (λhd tl -> ?list))"] : [])...,
            (append_one ? ["(append_one ?list ?int)"] : [])...,
            (append ? ["(append ?list ?list)"] : [])...,
        ],
        "?bool" => ["?bool_term" => 6, "?bool_nonterm" => 4],
        "?bool_term" => [
            "#bool",
            ["(flip 0.$i)" for i in (1, 2, 3, 4, 5, 6, 7, 8, 9)]...,
            "false",
            "true",
        ],
        "?bool_nonterm" => [
            "(== ?int ?int)",
            (isempty ? ["(isempty ?list)"] : [])...,
            "(> ?int ?int)",
            "(iseven ?int)",
            # "(issquare ?int)",
            # "(isprime ?int)",
            "(if ?bool ?bool ?bool)",
        ],
        "?arith" =>
            ["(+ ?int ?int)", "(- ?int ?int)", "(* ?int ?int)", "(mod ?int ?int)"],
    ]
    sym_of_type = [
        "list" => "?list",
        "int" => "?int",
        "bool" => "?bool",
    ]
    start_expr_of_type = [
        "list" => "(geom_list 0.5 0.2)",
        "int" => "(geom 0.2)",
    ]
    return Grammar(prods, sym_of_type, start_expr_of_type; size_dist = size_dist)
end

function rational_rules_ppcfg(; perturb = true, isempty = false, length = true, append = true, append_one = true, caseof = false, size_dist = Geometric(0.5))
    prods = [
        (perturb ? ("?start" => ["(perturb ?list)"]) : [])...,
        "?int" => ["?int_term" => 6, "?int_nonterm" => 4],
        "?int_term" => ["#int", "?constint"],
        "?constint" => [("$i" for i ∈ 0:9)...],
        "?int_nonterm" => [
            "(index ?int ?list)",
            # "?arith",
            #"(length ?list)",
            "(car ?list)",
            "(if ?bool ?int ?int)",
            # "(plus10 ?int)",
            "(inc ?int)",
            "(dec ?int)",
            # "(+ ?int ?int)",
            # "(- ?int ?int)",
            # todo you prob do want to allow this:
            # (caseof ? ["(case ?list of Nil => ?int | Cons => (λhd tl -> ?int))"] : [])...,
            (length ? ["(length ?list)"] : [])...,
        ],
        "?list" => ["?list_term" => 6, "?list_nonterm" => 4],
        "?list_term" => ["#list", "make_nil"],
        "?list_nonterm" => [
            "(cons ?int ?list)",
            "(cdr_safe ?list)",
            "(mapi (λx i -> ?int) ?list)",
            "(filteri (λx i -> ?bool) ?list)",
            "(if ?bool ?list ?list)",
            (caseof ? ["(case ?list of Nil => ?list | Cons => (λhd tl -> ?list))"] : [])...,
            (append_one ? ["(append_one ?list ?int)"] : [])...,
            (append ? ["(append ?list ?list)"] : [])...,
        ],
        "?bool" => ["?bool_term" => 6, "?bool_nonterm" => 4],
        "?bool_term" => [
            "#bool",
            "false",
            "true",
        ],
        "?bool_nonterm" => [
            "(== ?int ?int)",
            (isempty ? ["(isempty ?list)"] : [])...,
            "(> ?int ?int)",
            # "(issquare ?int)",
            # "(isprime ?int)",
            "(iseven ?int)",
            "(if ?bool ?bool ?bool)",
        ],
        "?arith" =>
            ["(+ ?int ?int)", "(- ?int ?int)", "(* ?int ?int)", "(mod ?int ?int)"],
    ]
    sym_of_type = [
        "list" => "?list",
        "int" => "?int",
        "bool" => "?bool",
    ]
    start_sym_of_type = [
        "list" => perturb ? "?start" : "?list",
    ]
    start_expr_of_type = [
        "list" => perturb ? "(perturb make_nil)" : "make_nil",
    ]
    return Grammar(prods, sym_of_type, start_expr_of_type; start_sym_of_type = start_sym_of_type, size_dist = size_dist)
end

function caseof_joshrule_ppcfg(; size_dist = Geometric(0.5))
    prods = [
        "?int" => ["?int_term" => 6, "?int_nonterm" => 4],
        "?int_term" => [
            "make_random_digit",
            "#int",
            # "?constint"
        ],
        "?constint" => [("$i" for i ∈ 0:9)...],
        "?int_nonterm" => [
            "(car ?list)",
            "(if ?bool ?int ?int)",
            "(+ ?int ?int)",
            "(- ?int ?int)",
            "(Y{list,int} (λrec xs -> ?int) ?list)",
            "(Y{int,int} (λrec xs -> ?int) ?int)",
            "(S ?int)",
            "(case ?list of Nil => ?int | Cons => (λhd tl -> ?int))",
            # "(case ?int of O => ?int | S => (λx -> ?int))",
        ],
        "?list" => ["?list_term" => 6, "?list_nonterm" => 4],
        "?list_term" => ["#list", "make_random_list", "make_nil"],
        "?list_nonterm" => [
            "(cons ?int ?list)",
            "(cdr_safe ?list)",
            "(if ?bool ?list ?list)",
            "(Y{list,list} (λrec xs -> ?list) ?list)",
            "(Y{int,list} (λrec xs -> ?list) ?int)",
            "(case ?list of Nil => ?list | Cons => (λhd tl -> ?list))",
            "(case ?int of O => ?list | S => (λx -> ?list))",
        ],
        "?bool" => ["?bool_term" => 6, "?bool_nonterm" => 4],
        "?bool_term" => [
            "#bool",
            ["(flip 0.$i)" for i in (1, 2, 3, 4, 5, 6, 7, 8, 9)]...,
            "false",
            "true",
        ],
        "?bool_nonterm" => [
            "(== ?int ?int)",
            "(> ?int ?int)",
            "(if ?bool ?bool ?bool)",
            "(isempty ?list)",
            "(case ?list of Nil => ?bool | Cons => (λhd tl -> ?bool))",
            "(case ?int of O => ?bool | S => (λx -> ?bool))",
        ],
    ]

    sym_of_type = [
        "list" => "?list",
        "int" => "?int",
        "bool" => "?bool",
    ]
    start_expr_of_type = [
        "list" => "make_random_list",
        "int" => "make_random_digit",
    ]
    return Grammar(prods, sym_of_type, start_expr_of_type; size_dist = size_dist)
end



function joshrule_ppcfg(; size_dist = Geometric(0.5))
    prods = [
        # "?start" => ["?list"],
        # "?start" => ["(Y{list,list} (λrec xs -> ?list) #1)"],

        "?int" => ["?int_term" => 6, "?int_nonterm" => 4],
        "?int_term" => ["make_random_digit", "#int", "?constint"],
        "?constint" => [("$i" for i ∈ 0:9)...],
        "?int_nonterm" => [
            "(car ?list)",
            "(if ?bool ?int ?int)",
            "(+ ?int ?int)",
            "(- ?int ?int)",
            "(Y{list,int} (λrec xs -> ?int) ?list)",
            "(Y{int,int} (λrec xs -> ?int) ?int)",
        ],
        "?list" => ["?list_term" => 6, "?list_nonterm" => 4],
        "?list_term" => ["#list", "make_random_list", "make_nil"],
        "?list_nonterm" => [
            "(cons ?int ?list)",
            "(cdr_safe ?list)",
            "(if ?bool ?list ?list)",
            "(Y{list,list} (λrec xs -> ?list) ?list)",
            "(Y{int,list} (λrec xs -> ?list) ?int)",
        ],
        "?bool" => ["?bool_term" => 6, "?bool_nonterm" => 4],
        "?bool_term" => [
            "#bool",
            ["(flip 0.$i)" for i in (1, 2, 3, 4, 5, 6, 7, 8, 9)]...,
            "false",
            "true",
        ],
        "?bool_nonterm" => [
            "(== ?int ?int)",
            "(> ?int ?int)",
            "(if ?bool ?bool ?bool)",
            "(isempty ?list)",
        ],
    ]

    sym_of_type = [
        "list" => "?list",
        "int" => "?int",
        "bool" => "?bool",
    ]
    start_expr_of_type = [
        "list" => "make_random_list",
        "int" => "make_random_digit",
    ]
    return Grammar(prods, sym_of_type, start_expr_of_type; size_dist = size_dist)
end

function caseof_ppcfg(; size_dist = Geometric(0.5))
    prods = [
        "?int" => ["?int_term" => 8, "?int_nonterm" => 2],
        "?int_term" => ["make_random_digit", "#int", "?constint"],
        "?constint" => [("$i" for i ∈ 0:9)...],
        "?int_nonterm" => [
            "(case ?list of Nil => ?int | Cons => (λhd tl -> ?int))",
            "(if ?bool ?int ?int)",
            "(+ ?int ?int)",
            "(- ?int ?int)",
            "(Y{list,int} (λrec xs -> ?int) ?list)",
            "(Y{int,int} (λrec xs -> ?int) ?int)",
        ],
        "?list" => ["?list_term" => 8, "?list_nonterm" => 2],
        "?list_term" => ["#list", "make_random_list", "make_nil"],
        "?list_nonterm" => [
            "(Cons ?int ?list)",
            "(case ?list of Nil => ?list | Cons => (λhd tl -> ?list))",
            "(if ?bool ?list ?list)",
            "(Y{list,list} (λrec xs -> ?list) ?list)",
            "(Y{int,list} (λrec xs -> ?list) ?int)",
        ],
        "?bool" => ["?bool_term" => 8, "?bool_nonterm" => 2],
        "?bool_term" => [
            "#bool",
            ["(flip 0.$i)" for i in (0, 1, 2, 3, 4, 5, 6, 7, 8, 9)]...,
            "true",
        ],
        "?bool_nonterm" => [
            "(== ?int ?int)",
            "(> ?int ?int)",
            "(if ?bool ?bool ?bool)",
            "(case ?list of Nil => ?bool | Cons => (λhd tl -> ?bool))",
        ],
    ]

    sym_of_type = [
        "list" => "?list",
        "int" => "?int",
        "bool" => "?bool",
    ]
    start_expr_of_type = [
        "list" => "make_random_list",
        "int" => "make_random_digit",
    ]
    return Grammar(prods, sym_of_type, start_expr_of_type; size_dist = size_dist)
end



function origami_ppcfg(; caseof = true, fold = false, size_dist = Geometric(0.5))
    prods = [
        "?startlist" => ["(Y{list,list} (λrec xs -> ?list) #1)"],
        "?startint" => ["(Y{list,int} (λrec xs -> ?int) #1)"],
        "?int" => ["?int_term" => 6, "?int_nonterm" => 4],
        "?int_term" => ["make_random_digit", "#int", "?constint"],
        "?constint" => [("$i" for i ∈ 0:1)...],
        "?int_nonterm" => [
            "(car ?list)",
            "(if ?bool ?int ?int)",
            # "(inc ?int)", # added inc
            "(+ ?int ?int)",
            "(- ?int ?int)",
            # (caseof ? ["(case ?list of Nil => ?int | Cons => (λhd tl -> ?int))"] : [])...,
        ],
        "?list" => ["?list_term" => 6, "?list_nonterm" => 4],
        "?list_term" => ["#list", "make_random_list", "make_nil"],
        "?list_nonterm" => [
            "(cons ?int ?list)",
            "(cdr_safe ?list)",
            "(if ?bool ?list ?list)",
            (caseof ? ["(case ?list of Nil => ?list | Cons => (λhd tl -> ?list))"] : [])...,
            # fold  "list -> list -> (int -> list -> list) -> list"
            (fold ? ["(fold ?list ?list (λnext acc -> ?list))"] : [])...,
        ],
        "?bool" => ["?bool_term" => 6, "?bool_nonterm" => 4],
        "?bool_term" => [
            "#bool",
            ["(flip 0.$i)" for i in (1, 2, 3, 4, 5, 6, 7, 8, 9)]...,
            "false",
            "true",
        ],
        "?bool_nonterm" => [
            "(== ?int ?int)",
            "(> ?int ?int)",
            "(if ?bool ?bool ?bool)",
            "(isempty ?list)",
        ],
    ]

    sym_of_type = [
        "list" => "?list",
        "int" => "?int",
        "bool" => "?bool",
    ]
    start_sym_of_type = [
        "list" => "?startlist",
        "int" => "?startint",
    ]
    start_expr_of_type = [
        "list" => "(Y{list,list} (λrec xs -> make_random_list) #1)",
        "int" => "(Y{list,int} (λrec xs -> make_random_digit) #1)",
    ]
    return Grammar(prods, sym_of_type, start_expr_of_type; start_sym_of_type = start_sym_of_type, size_dist = size_dist)
end
