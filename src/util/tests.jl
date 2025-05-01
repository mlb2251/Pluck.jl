

function run_examples()
    for file in readdir(joinpath(@__DIR__, "..", "..", "programs"); join=true)
        if endswith(file, ".pluck")
            printstyled("Running $file\n"; color=:blue, bold=true)
            load_pluck_file(file)
        end
    end
end

