export load_pluck_file, eval_forms, sample_output, @pluck_str


abstract type InferenceMode end
struct ExactInference <: InferenceMode end
struct SMCInference <: InferenceMode
    k::Int
end

"""
pluck"..." is equivalent to eval_forms("...")
"""
macro pluck_str(str)
    # Handle string interpolation
    # interpolated_str = Meta.parse("\"$str\"")
    :(eval_forms($(esc(str))))
end
