export origami_solutions, dc_list_solutions

function origami_solutions()
    Dict{Symbol, PExpr}(
        Symbol("length int") => parse_expr(
            "(Y{list,int} (λ_->(λ_->(if (isempty #1) 0 (+ 1 (#2 (cdr #1)))))) #1)",
        ),
        Symbol("countdown") => parse_expr(
            "(Y{int,list} (λ_->(λ_->(if (== #1 0) make_nil (cons (+ 1 #1) (#2 (- #1 1)))))) #1)",
        ),
        Symbol("weird count") => parse_expr(
            "(Y{int,list} (λ_->(λ_->(if (== #1 0) make_nil (cons (- 0 #1) (#2 (+ 1 #1)))))) #1)",
        ),
        Symbol("take every other") => parse_expr(
            "(Y{list,list} (λ_->(λ_->(if (isempty #1) make_nil (cons (car #1) (#2 (cdr (cdr #1))))))) #1)",
        ),
        Symbol("drop last element") => parse_expr(
            "(Y{list,list} (λ_->(λ_->(if (isempty (cdr #1)) make_nil (cons (car #1) (#2 (cdr #1)))))) #1)",
        ),
        Symbol("stutter") => parse_expr(
            "(Y{list,list} (λ_->(λ_->(if (isempty #1) make_nil (cons (car #1) (cons (car #1) (#2 (cdr #1))))))) #1)",
        ),
        Symbol("sum") => parse_expr(
            "(Y{list,int} (λ_->(λ_->(if (isempty #1) 0 (+ (car #1) (#2 (cdr #1)))))) #1)",
        ),
        Symbol("append constant 0") => parse_expr(
            "(Y{list,list} (λ_->(λ_->(if (isempty #1) (cons 0 make_nil) (cons (car #1) (#2 (cdr #1)))))) #1)",
        ),
        Symbol("map double") => parse_expr(
            "(Y{list,list} (λ_->(λ_->(if (isempty #1) make_nil (cons (+ (car #1) (car #1)) (#2 (cdr #1)))))) #1)",
        ),
        Symbol("map increment") => parse_expr(
            "(Y{list,list} (λ_->(λ_->(if (isempty #1) make_nil (cons (+ 1 (car #1)) (#2 (cdr #1)))))) #1)",
        ),
        Symbol("map negation") => parse_expr(
            "(Y{list,list} (λ_->(λ_->(if (isempty #1) make_nil (cons (- 0 (car #1)) (#2 (cdr #1)))))) #1)",
        ),
    )
end

function dc_list_solutions()
    solutions = Dict{Symbol, PExpr}()
    all_solns = Dict{Symbol, Vector{String}}()
    tasks = load_tasks("data/compression_benchmark/io_examples/list.json")

    dirs = filter(
        contains("list"),
        readdir("data/compression_benchmark/benches/", join = true),
    )
    jsons = filter(
        endswith(".json"),
        collect(Iterators.flatten(map(d -> readdir(d; join = true), dirs))),
    )
    for json in jsons
        json = JSON.parsefile(json)
        for frontier in json["frontiers"]
            name = Symbol(frontier["name"])
            @assert !isnothing(findfirst(isequal(name), getfield.(tasks, :name))) "task not found: $name"
            for soln in getindex.(frontier["programs"], Ref("program"))
                if !haskey(all_solns, name)
                    all_solns[name] = String[]
                end
                push!(all_solns[name], soln)
            end
        end
    end
    # filter out learned ones
    for (name, solns) in all_solns
        unique!(solns)
        filter!(s -> !contains(s, "#("), solns)

        # eek temporarily drop all these
        # filter!(s -> !contains(s, "range"), solns)
        # filter!(s -> !contains(s, "index"), solns)
        # filter!(s -> !contains(s, "mod"), solns)
        # filter!(s -> !contains(s, "*"), solns)
        filter!(s -> !contains(s, "is-square"), solns)
        filter!(s -> !contains(s, "is-prime"), solns)
        length(solns) == 0 && continue
        sort!(solns, by = length)

        soln = solns[1]

        # dc -> ctf conversion
        soln = replace(
            soln,
            "lambda" => "λ_->",
            ("\$$i" => "#$(i+1)" for i = 0:9)...,
            "empty?" => "isempty",
            "empty" => "make_nil",
            "gt?" => ">",
            "eq?" => "==",
            "is-square" => "issquare",
            "is-prime" => "isprime",
        )

        soln = parse_expr(soln)

        # strip off the outer lambda
        @assert soln isa Abs
        soln = soln.body
        @assert !(soln isa Abs)

        solutions[name] = soln
    end

    solutions
end
