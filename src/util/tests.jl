

function run_examples()
    for file in readdir(joinpath(@__DIR__, "..", "..", "programs"); join=true)
        if endswith(file, ".pluck")
            printstyled("Running $file\n"; color=:blue, bold=true)
            load_pluck_file(file)
        end
    end
end

function run_check()
    fail_count = Ref(0)
    for file in readdir(joinpath(@__DIR__, "..", "..", "programs"); join=true)
        if endswith(file, ".pluck")
            load_pluck_file(file; check=true, fail_count)
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

