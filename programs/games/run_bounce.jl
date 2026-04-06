using Pluck
using JSON

load_pluck_file("programs/games/games.pluck"; silent=true)

# --- Pluck int/expr helpers ---

function pluck_signed(n::Int)
    n == 0 ? "(Z)" :
    n > 0  ? "(P $(pluck_signed(n-1)))" :
             "(N $(pluck_signed(n+1)))"
end

function games_nat(n::Int)
    @assert n >= 0
    pluck_signed(n)
end

# --- Build setup expressions ---

function wall_state(x, y)
    "(St (Co (Sc (Lat (F) (F)) (X) (Obs $(pluck_signed(x)) $(pluck_signed(y)))) (Ni)))"
end

function bouncer_state(x, y; hdir=true, vdir=true)
    h = hdir ? "(T)" : "(F)"
    v = vdir ? "(T)" : "(F)"
    "(St (Co (Sc (Lat $h $v) (X) (Obs $(pluck_signed(x)) $(pluck_signed(y)))) (Ni)))"
end

function pluck_list(items)
    foldr((item, acc) -> "(Co $item $acc)", items; init="(Ni)")
end

function box_setup(; half=4, bx=0, by=0, hdir=true, vdir=true)
    walls = String[]
    for x in -half:half, y in -half:half
        if x == -half || x == half || y == -half || y == half
            push!(walls, wall_state(x, y))
        end
    end
    n_walls = length(walls)
    kinds = pluck_list([fill("wall-kind", n_walls); "diag-bouncer-kind"])
    states = pluck_list([walls; bouncer_state(bx, by; hdir, vdir)])
    "(Setup $kinds $states)"
end

# --- Run query ---

function run_game(setup_expr::String, n_steps::Int)
    query_str = "(Marginal (run $(games_nat(n_steps)) $setup_expr))"
    state = LazyKCState()
    body = deterministic_world(toplevel_compile(parse_expr(query_str); state))
    results = Pluck.eval_query(body, state)
    free_state(state)
    return results[1][1]
end

# --- Value tree walkers ---

function pluck_int(v::Value)
    v.constructor == :Z && return 0
    v.constructor == :P && return 1 + pluck_int(v.args[1])
    v.constructor == :N && return -1 + pluck_int(v.args[1])
    error("not an int: $(v.constructor)")
end

function extract_pluck_list(v::Value)
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
    kinds = extract_pluck_list(setup.args[1])
    states = extract_pluck_list(setup.args[2])

    # assign a kind index by string identity (Values with closures aren't ==)
    kind_strs = [Pluck.rawstring(k) for k in kinds]
    unique_strs = unique(kind_strs)
    kind_idx = [findfirst(==(s), unique_strs) - 1 for s in kind_strs]

    objects = []
    for (i, st) in enumerate(states)
        @assert st.constructor == :St
        slices = reverse(extract_pluck_list(st.args[1]))

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
        push!(objects, Dict("timeline" => timeline, "kind" => kind_idx[i]))
    end
    objects
end

# --- Main ---

example = length(ARGS) >= 1 ? ARGS[1] : "box"
n_steps = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 20

if example == "line"
    setup_expr = "bounce-setup"
elseif example == "box"
    setup_expr = box_setup(half=4, bx=0, by=1, hdir=true, vdir=true)
else
    error("Unknown example: $example. Use 'line' or 'box'.")
end

println("Running '$example' for $n_steps steps...")
result = run_game(setup_expr, n_steps)
data = Dict("objects" => extract_trajectory(result))
outpath = joinpath("programs", "games", "html", "trajectory.json")
open(outpath, "w") do f
    JSON.print(f, data, 2)
end
println("Wrote $outpath")
