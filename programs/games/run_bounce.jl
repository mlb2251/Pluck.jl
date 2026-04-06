using Pluck
using JSON

load_pluck_file("programs/games/games.pluck"; silent=true)

function games_nat(n::Int)
    @assert n >= 0
    n == 0 ? "(Z)" : "(P $(games_nat(n-1)))"
end

function run_game(n_steps::Int)
    query_str = "(Marginal (run $(games_nat(n_steps)) bounce-setup))"
    state = LazyKCState()
    body = deterministic_world(toplevel_compile(parse_expr(query_str); state))
    results = Pluck.eval_query(body, state)
    free_state(state)
    return results[1][1]  # single deterministic result
end

# --- Value tree walkers ---

function pluck_int(v::Value)
    v.constructor == :Z && return 0
    v.constructor == :P && return 1 + pluck_int(v.args[1])
    v.constructor == :N && return -1 + pluck_int(v.args[1])
    error("not an int: $(v.constructor)")
end

function pluck_list(v::Value)
    result = []
    while v.constructor == :Co
        push!(result, v.args[1])
        v = v.args[2]
    end
    @assert v.constructor == :Ni
    result
end

function extract_trajectory(setup::Value)
    @assert setup.constructor == :Setup
    states = pluck_list(setup.args[2])

    objects = []
    for st in states
        @assert st.constructor == :St
        slices = reverse(pluck_list(st.args[1]))  # chronological order

        timeline = []
        for sc in slices
            @assert sc.constructor == :Sc
            obs = sc.args[3]
            @assert obs.constructor == :Obs
            push!(timeline, Dict(
                "x" => pluck_int(obs.args[1]),
                "y" => pluck_int(obs.args[2]),
                "act" => string(sc.args[2].constructor),
            ))
        end
        push!(objects, Dict("timeline" => timeline))
    end
    objects
end

# --- Main ---

n_steps = length(ARGS) >= 1 ? parse(Int, ARGS[1]) : 10
println("Running $n_steps steps...")
result = run_game(n_steps)
data = Dict("objects" => extract_trajectory(result))
outpath = joinpath("programs", "games", "html", "trajectory.json")
open(outpath, "w") do f
    JSON.print(f, data, 2)
end
println("Wrote $outpath")
