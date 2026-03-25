

function run_examples()
    for file in readdir(joinpath(@__DIR__, "..", "..", "programs"); join=true)
        if endswith(file, ".pluck")
            printstyled("Running $file\n"; color=:blue, bold=true)
            load_pluck_file(file)
        end
    end
end

function run_check(files=nothing; baseline=nothing, outfile=nothing, allow="", once=false)
    fail_count = Ref(0)
    check_results = CheckResult[]
    if files === nothing
        files = [f for f in readdir(joinpath(@__DIR__, "..", "..", "programs"); join=true) if endswith(f, ".pluck")]
    else
        files = [abspath(f) for f in files]
    end
    allow_filter = isempty(allow) ? nothing : allow
    for file in files
        load_pluck_file(file; check=true, fail_count, check_results, allow=allow_filter, once)
    end

    # Save results and show diff against baseline
    if !isempty(check_results)
        println()
        save_check_results(check_results; outfile)
        if baseline !== nothing
            diff_check_results(baseline)
        else
            diff_check_results()
        end
    end

    n = fail_count[]
    if n > 0
        printstyled("\n$n failure$(n == 1 ? "" : "s")\n"; color=:red, bold=true)
        error("check failed with $n failure$(n == 1 ? "" : "s")")
    else
        printstyled("\nAll checks passed\n"; color=:green, bold=true)
    end
end

