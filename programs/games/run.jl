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

function make_state(x, y, bools::Vector{Bool}=Bool[]; alive=true)
    lat_args = isempty(bools) ? "(F) (F) (F)" : join(pluck_bool.(bools), " ")
    "(St (Co (Sc (Lat $lat_args) (X) (Obs $(pluck_int(x)) $(pluck_int(y)) $(pluck_bool(alive)))) (Ni)))"
end

function make_walls(coords)
    [make_state(x, y) for (x, y) in coords]
end

function make_box(; half=4)
    coords = [(x, y) for x in -half:half for y in -half:half
              if x == -half || x == half || y == -half || y == half]
    make_walls(coords)
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

bouncer(x, y; hdir=true, vdir=true, hturn=true) =
    Actor("alt-bouncer-kind", make_state(x, y, [hdir, vdir, hturn]))

hbouncer(x, y; dir=true) =
    Actor("bouncer-kind", make_state(x, y, [dir, false, false]))

water(x, y) =
    Actor("water-kind", make_state(x, y))

block(x, y) =
    Actor("block-kind", make_state(x, y))

# --- Wall geometry ---

function make_plinko(; half=4)
    walls = Set{Tuple{Int,Int}}()
    for x in -half:half, y in -half:half
        if x == -half || x == half || y == -half || y == half
            push!(walls, (x, y))
        end
    end
    peg_row = 0
    for row in (half-2):-2:(-half+2)
        offset = isodd(peg_row) ? 1 : 0
        for x in (-half+2+offset):2:(half-2)
            push!(walls, (x, row))
        end
        peg_row += 1
    end
    make_walls(collect(walls))
end

function make_basin_box(; half=4, bx=0, by=-1, bw=2, bh=2)
    walls = Set{Tuple{Int,Int}}()
    for x in -half:half, y in -half:half
        if x == -half || x == half || y == -half || y == half
            push!(walls, (x, y))
        end
    end
    x0, x1 = bx - bw÷2 - 1, bx + bw÷2
    y0, y1 = by, by + bh - 1
    for x in x0:x1
        push!(walls, (x, y0 - 1))
    end
    for y in y0:y1
        push!(walls, (x0, y))
        push!(walls, (x1, y))
    end
    make_walls(collect(walls))
end

# --- Run query ---

function run_game(setup_expr::String, n_steps::Int; n_samples::Int=1)
    n_nat = Pluck.pluck_nat(n_samples)
    query_str = "(PosteriorSamples (run $(pluck_int(n_steps)) $setup_expr) true $n_nat)"
    state = LazyKCState()
    body = deterministic_world(toplevel_compile(parse_expr(query_str); state))
    results = Pluck.eval_query(body, state)
    free_state(state)
    return results
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
            lat = sc.args[1]
            Dict(
                "x" => extract_int(obs.args[1]),
                "y" => extract_int(obs.args[2]),
                "alive" => obs.args[3].constructor == :T,
                "act" => string(sc.args[2].constructor),
                "lat" => [string(a.constructor) for a in lat.args],
            )
        end
        push!(objects, Dict("timeline" => timeline, "kind" => kind_idx[i]))
    end
    objects
end

# --- Scenes ---

function random_bouncer(xs, y; hdir=true, vdir=true, hturn=true)
    # Generate a Pluck uniform expression over possible x positions
    options = [Actor("alt-bouncer-kind", make_state(x, y, [hdir, vdir, hturn])) for x in xs]
    kind_exprs = [a.kind for a in options]
    state_exprs = [a.state for a in options]
    # All share the same kind, so just pick state randomly
    kind = kind_exprs[1]
    state = "(uniform $(join(state_exprs, " ")))"
    Actor(kind, state)
end

function breakout_setup(; half=4, block_rows=1:1)
    walls = make_box(half=half)
    blocks = [block(x, y) for y in block_rows for x in (-half+1):(half-1)]
    ball = random_bouncer((-half+1):(half-1), -2; hdir=true, vdir=true)
    make_setup(walls, [blocks; ball])
end

SCENES = [
    ("line", 50, make_setup(
        make_walls([(-3,0), (3,0)]),
        [hbouncer(0, 0; dir=true)])),
    ("box", 50, make_setup(
        make_box(half=4),
        [bouncer(0, 1; hdir=true, vdir=true)])),
    ("box 2-ball", 50, make_setup(
        make_box(half=4),
        [bouncer(0, 1; hdir=true, vdir=true),
         bouncer(1, -1; hdir=false, vdir=false, hturn=false)])),
    ("water", 25, make_setup(
        make_box(half=4),
        [water(0, 3), water(-2, 3), water(2, 3)])),
    ("plinko", 20, make_setup(
        make_plinko(half=4),
        [water(0, 3), water(-1, 3), water(1, 3)])),
    ("basin", 20, make_setup(
        make_basin_box(half=4, bx=0, by=-1, bw=2, bh=2),
        [water(0, 3), water(-1, 3), water(1, 3)])),
    ("breakout", 50, breakout_setup(block_rows=0:3)),
]

# --- Main ---

n_samples = 1

scenes = []
for (si, (name, n_steps, setup_expr)) in enumerate(SCENES)
    print("[$si/$(length(SCENES))] '$name' ($n_steps steps, $n_samples samples)... ")
    flush(stdout)
    t = time()
    results = run_game(setup_expr, n_steps; n_samples)
    elapsed = round(time() - t; digits=1)
    print("ran $(elapsed)s, extracting... ")
    flush(stdout)
    samples = [Dict("objects" => extract_trajectory(r)) for r in results]
    push!(scenes, Dict("name" => name, "samples" => samples))
    println("done")
end

outpath = joinpath("programs", "games", "html", "trajectory.json")
open(outpath, "w") do f
    JSON.print(f, Dict("scenes" => scenes), 2)
end
println("Wrote $outpath")
