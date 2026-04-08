using Pluck
using JSON

load_pluck_file("programs/games/games.pluck"; silent=true)

# --- Pluck expression helpers (from run.jl) ---

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

block(x, y) =
    Actor("block-kind", make_state(x, y))

function random_bouncer(xs, y; hdir=true, vdir=true, hturn=true)
    options = [Actor("alt-bouncer-kind", make_state(x, y, [hdir, vdir, hturn])) for x in xs]
    state_exprs = [a.state for a in options]
    kind = options[1].kind
    state = "(uniform $(join(state_exprs, " ")))"
    Actor(kind, state)
end

function breakout_setup(; half=4, block_rows=1:0, n_balls=1)
    walls = make_box(half=half)
    blocks = [block(x, y) for y in block_rows for x in (-half+1):(half-1)]
    balls = [random_bouncer((-half+1):(half-1), -2 - i + 1; hdir=true, vdir=true) for i in 1:n_balls]
    make_setup(walls, [blocks; balls])
end

function run_game(setup_expr::String, n_steps::Int; n_samples::Int=1)
    n_nat = Pluck.pluck_nat(n_samples)
    query_str = "(PosteriorSamples (run $(pluck_int(n_steps)) $setup_expr) true $n_nat)"
    local state = LazyKCState()
    local body = deterministic_world(toplevel_compile(parse_expr(query_str); state))
    local results = Pluck.eval_query(body, state)
    free_state(state)
    return results
end

function wall_row_actors(y; half=4)
    [Actor("wall-kind", make_state(x, y)) for x in (-half+1):(half-1)]
end

function breakout_mixed_setup(; half=4, block_rows=1:0, wall_rows=1:0, n_balls=1)
    walls = make_box(half=half)
    extra_walls = [Actor("wall-kind", make_state(x, y)) for y in wall_rows for x in (-half+1):(half-1)]
    blocks = [block(x, y) for y in block_rows for x in (-half+1):(half-1)]
    balls = [random_bouncer((-half+1):(half-1), -2 - i + 1; hdir=true, vdir=true) for i in 1:n_balls]
    # extra walls go into the actors list (not the wall_states list) so total object count matches
    make_setup(walls, [extra_walls; blocks; balls])
end

function main()
    N_STEPS = 20

    # Warmup
    println("Warmup (5 steps, 0 blocks, 1 ball)...")
    t = time()
    run_game(breakout_setup(block_rows=1:0, n_balls=1), 5)
    println("  warmup: $(round(time() - t; digits=2))s\n")

    # --- Blocks vs walls comparison ---
    println("=== Blocks vs walls ($(N_STEPS) steps, 1 ball) ===")

    configs = [
        ("2 rows blocks",           0:1,  1:0),
        ("2 rows blocks + 2 walls", 0:1,  2:3),
    ]
    for (label, br, wr) in configs
        n_blocks = length(br) > 0 && first(br) <= last(br) ? length(br) * 7 : 0
        n_walls_extra = length(wr) > 0 && first(wr) <= last(wr) ? length(wr) * 7 : 0
        setup = breakout_mixed_setup(block_rows=br, wall_rows=wr, n_balls=1)
        print("  $label ($(n_blocks)b + $(n_walls_extra)w = $(n_blocks+n_walls_extra) extra) ... ")
        flush(stdout)
        t = time()
        run_game(setup, N_STEPS)
        println("$(round(time() - t; digits=2))s")
    end
end

main()
