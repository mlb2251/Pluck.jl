using Pluck
using JSON

load_pluck_file("programs/games/games.pluck"; silent=true)

# --- Pluck expression helpers ---

function pluck_int(n::Int)
    n == 0 ? "(Z)" :
    n > 0  ? "(P $(pluck_int(n-1)))" :
             "(N $(pluck_int(n+1)))"
end

function pluck_list(items)
    foldr((item, acc) -> "(Co $item $acc)", items; init="(Ni)")
end

function pluck_bool(b::Bool)
    b ? "(T)" : "(F)"
end

# --- Setup builders ---

function make_state(x, y, bools::Vector{Bool}=Bool[])
    lat_args = isempty(bools) ? "(F) (F) (F)" : join(pluck_bool.(bools), " ")
    "(St (Co (Sc (Lat $lat_args) (X) (Obs $(pluck_int(x)) $(pluck_int(y)))) (Ni)))"
end

function make_walls(coords)
    [make_state(x, y) for (x, y) in coords]
end

function make_box(; half=4)
    coords = [(x, y) for x in -half:half for y in -half:half
              if x == -half || x == half || y == -half || y == half]
    make_walls(coords)
end

function make_hline(; y=0, x0=-3, x1=3)
    make_walls([(x, y) for x in x0:x1])
end

function make_vline(; x=0, y0=-3, y1=3)
    make_walls([(x, y) for y in y0:y1])
end

function make_setup(wall_states, actors)
    n_walls = length(wall_states)
    kinds = pluck_list([fill("wall-kind", n_walls); [a.kind for a in actors]])
    states = pluck_list([wall_states; [a.state for a in actors]])
    "(Setup $kinds $states)"
end

struct Actor
    kind::String
    state::String
end

function bouncer(x, y; hdir=true, vdir=true, hturn=true)
    Actor("alt-bouncer-kind", make_state(x, y, [hdir, vdir, hturn]))
end

function hbouncer(x, y; dir=true)
    Actor("bouncer-kind", make_state(x, y, [dir, false, false]))
end

function water(x, y)
    Actor("water-kind", make_state(x, y))
end

# --- Run query ---

function run_game(setup_expr::String, n_steps::Int)
    query_str = "(PosteriorSamples (run $(pluck_int(n_steps)) $setup_expr) true 1)"
    state = LazyKCState()
    body = deterministic_world(toplevel_compile(parse_expr(query_str); state))
    results = Pluck.eval_query(body, state)
    free_state(state)
    return results[1]
end

# --- Value extraction ---

function extract_int(v::Value)
    v.constructor == :Z && return 0
    v.constructor == :P && return 1 + extract_int(v.args[1])
    v.constructor == :N && return -1 + extract_int(v.args[1])
    error("not an int: $(v.constructor)")
end

function extract_list(v::Value)
    result = []
    while v.constructor == :Co
        push!(result, v.args[1])
        v = v.args[2]
    end
    result
end

function extract_trajectory(setup::Value)
    kinds = extract_list(setup.args[1])
    states = extract_list(setup.args[2])

    kind_strs = [Pluck.rawstring(k) for k in kinds]
    unique_strs = unique(kind_strs)
    kind_idx = [findfirst(==(s), unique_strs) - 1 for s in kind_strs]

    objects = []
    for (i, st) in enumerate(states)
        slices = reverse(extract_list(st.args[1]))
        timeline = map(slices) do sc
            obs = sc.args[3]
            Dict(
                "x" => extract_int(obs.args[1]),
                "y" => extract_int(obs.args[2]),
                "act" => string(sc.args[2].constructor),
            )
        end
        push!(objects, Dict("timeline" => timeline, "kind" => kind_idx[i]))
    end
    objects
end

# --- Scenes ---

SCENES = [
    ("line", make_setup(
        [make_walls([(-3,0), (3,0)]);],
        [hbouncer(0, 0; dir=true)])),
    ("box", make_setup(
        make_box(half=4),
        [bouncer(0, 1; hdir=true, vdir=true)])),
    ("water", make_setup(
        make_box(half=4),
        [water(0, 3), water(-2, 3), water(2, 3)])),
]

# --- Main ---

n_steps = length(ARGS) >= 1 ? parse(Int, ARGS[1]) : 50

scenes = []
for (name, setup_expr) in SCENES
    println("Running '$name' for $n_steps steps...")
    result = run_game(setup_expr, n_steps)
    push!(scenes, Dict("name" => name, "objects" => extract_trajectory(result)))
end

outpath = joinpath("programs", "games", "html", "trajectory.json")
open(outpath, "w") do f
    JSON.print(f, Dict("scenes" => scenes), 2)
end
println("Wrote $outpath")
