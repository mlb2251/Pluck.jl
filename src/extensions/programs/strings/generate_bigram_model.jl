#!/usr/bin/env julia

# Generate a Pluck program that samples characters from bigram statistics.
# Usage: julia programs/generate_bigram_model.jl <text-file> [delimiter]
#
# The delimiter splits the input into separate sequences; defaults to newline.

using Printf

function usage()
    println("Usage: julia programs/generate_bigram_model.jl <text-file> [delimiter]")
    exit(1)
end

length(ARGS) >= 1 || usage()
path = ARGS[1]
delimiter = length(ARGS) >= 2 ? replace(ARGS[2], "\\n" => "\n", "\\t" => "\t") : "\n"

data = read(path, String)
sequences = isempty(delimiter) ? [data] : split(data, delimiter; keepempty=false)

const BOS_BYTE = UInt8('^')
const EOS_BYTE = UInt8('$')

# counts[prev][next] = count
counts = Dict{UInt8, Dict{UInt8, Int}}()

function add_count!(prev::UInt8, nxt::UInt8)
    inner = get!(counts, prev) do
        Dict{UInt8, Int}()
    end
    inner[nxt] = get(inner, nxt, 0) + 1
end

for seq in sequences
    prev = BOS_BYTE
    for b in codeunits(seq)
        add_count!(prev, b)
        prev = b
    end
    add_count!(prev, EOS_BYTE)
end

# Ensure every observed symbol has some outgoing transitions (EOS if none)
for prev in keys(counts)
    inner = counts[prev]
    if isempty(inner)
        inner[EOS_BYTE] = 1
    end
end

all_symbols = sort!(collect(keys(counts)))

function mk_int_literal(val::UInt8)
    return "(mk_int '8 '$(Int(val)))"
end

function render_discrete(inner::Dict{UInt8,Int})
    total = sum(values(inner))
    parts = String[]
    for (sym, cnt) in inner
        push!(parts, "($(mk_int_literal(sym)) $(cnt/total))")
    end
    return "(discrete " * join(parts, " ") * ")"
end

function render_smoothed_discrete(inner::Dict{UInt8,Int})
    total = sum(values(inner))
    if total == 0
        # If no counts, just use uniform
        return "(uniform_int_range '8 '32 '126)"
    end
    
    # Smoothing: with probability 1/(1+total), use uniform; otherwise use learned dist
    uniform_prob = 1.0 / (1.0 + total)
    learned_prob = total / (1.0 + total)
    
    # Add uniform_int_range as one option, then add all learned characters with scaled probabilities
    parts = String[]
    push!(parts, "((uniform_int_range '8 '32 '126) $uniform_prob)")
    
    for (sym, cnt) in inner
        scaled_prob = (cnt / total) * learned_prob
        push!(parts, "($(mk_int_literal(sym)) $scaled_prob)")
    end
    
    return "(discrete " * join(parts, " ") * ")"
end

function render_next_char()
    lines = String[]
    push!(lines, "(define BOS $(mk_int_literal(BOS_BYTE)))")
    push!(lines, "(define EOS $(mk_int_literal(EOS_BYTE)))")
    push!(lines, "(define (next-char prev)")
    # Build a nested if chain using int_dist_eq; no match on IntDist support yet.
    if isempty(all_symbols)
        # Default case with small probability of uniform character
        push!(lines, "  (discrete ((uniform_int_range '8 '32 '126) 0.01) (EOS 0.99))")
    else
        # Start with default: unseen characters get mostly EOS, but small chance of uniform
        expr = "    (discrete ((uniform_int_range '8 '32 '126) 0.01) (EOS 0.99))"
        for prev in reverse(all_symbols)
            cond = "(int_dist_eq prev $(mk_int_literal(prev)))"
            body = render_discrete(counts[prev])
            expr = "    (if $cond\n        $body\n        $expr)"
        end
        push!(lines, expr)
    end
    push!(lines, ")")
    return lines
end

function render_random_string()
    lines = String[]
    push!(lines, "(define (random-string prev)")
    push!(lines, "       (let ((c (next-char prev)))")
    push!(lines, "         (if (int_dist_eq c EOS)")
    push!(lines, "             (Nil)")
    push!(lines, "             (Cons c (random-string c)))))")
    return lines
end

program_lines = String[]
push!(program_lines, ";; Auto-generated bigram model from $(basename(path))")
append!(program_lines, render_next_char())
append!(program_lines, render_random_string())

println(join(program_lines, "\n"))
