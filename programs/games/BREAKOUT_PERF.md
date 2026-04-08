# Breakout Performance Analysis

## Setup

- half=4 box (33 wall cells on perimeter)
- 7 blocks per row (x from -3 to 3)
- Ball: `alt-bouncer-kind` with uniform random starting x
- All timings post-warmup (5-step compile run excluded)

## Scaling with steps (4 rows = 28 blocks, 1 ball)

| Steps | Time (s) |
|-------|----------|
| 10    | 5.31     |
| 20    | 11.98    |
| 30    | 20.03    |
| 40    | 28.07    |

**Linear in steps** — ~0.7s per step.

## Scaling with block rows (20 steps, 1 ball)

| Rows | Blocks | Time (s) |
|------|--------|----------|
| 0    | 0      | 0.07     |
| 1    | 7      | 1.39     |
| 2    | 14     | 3.60     |
| 3    | 21     | 7.60     |
| 4    | 28     | 11.44    |

**Superlinear in blocks** — roughly quadratic. Doubling blocks gives ~2.5-3x time.

## Scaling with balls (20 steps, 0 blocks)

| Balls | Time (s) |
|-------|----------|
| 1     | 0.07     |
| 2     | 0.10     |
| 3     | 0.14     |
| 4     | 0.18     |

**Balls are essentially free** (~0.03s per extra ball).

## Blocks vs walls (20 steps, 1 ball, same total extra objects)

| Config                       | Extra objects | Time (s) |
|------------------------------|---------------|----------|
| 4 rows blocks                | 28 blocks     | 11.19    |
| 2 rows blocks + 2 rows walls| 14b + 14w     | 7.25     |
| 4 rows walls                 | 28 walls      | 0.12     |
| baseline                     | 0             | 0.06     |

**Walls alone are free** — 28 extra walls add 0.06s. But walls slow down blocks:

| Config                        | Blocks | Total extra | Time (s) |
|-------------------------------|--------|-------------|----------|
| 2 rows blocks                 | 14     | 14          | 3.43     |
| 2 rows blocks + 2 rows walls  | 14     | 28          | 6.42     |

Same 14 blocks, but adding 14 walls nearly doubles the time.

## Conclusion

The bottleneck is `block-kind`. Each block calls `facing-toward` via `any-of`, which scans **all** states every step. The cost is:

```
O(steps × n_blocks × n_total_objects)
```

- `steps`: linear (confirmed)
- `n_blocks`: each block adds an `any-of` scan → linear in blocks
- `n_total_objects`: each `any-of` scan is linear in total objects → linear in total objects

So the total cost is cubic in the "size" of the scene when blocks are a constant fraction of objects. The walls-vs-blocks experiment confirms it's specifically the `any-of` scan inside `block-kind` that drives cost, not the object count itself.

---

## Proposed Approaches

### 1. Pass blocks a filtered mover list

Walls never move. Blocks never move. Only balls (bouncers) can hit a block.
Currently `block-kind`'s `any-of` scans all 60+ states. Instead, filter
`sts` to just the movers (balls) once per step in `step`, and pass that
short list to block-kind. Blocks still run the same `facing-toward` logic,
just over ~1 ball instead of 60+ objects.

```
(define (step setup)
  (match setup
    Setup kinds sts ->
    (let ((movers (filter-movers kinds sts)))
      (Setup kinds (step-sts kinds sts sts movers)))))
```

Block-kind's `any-of` scans `movers` instead of `sts`.

**Cost change**: O(blocks × total) → O(total + blocks × n_balls)

**Trade-off**: Requires changing the `Kd` type signature so `nextlat` can
receive both `all-sts` (for bouncers/water that need `occupied`) and
`movers` (for blocks). Or: add a second list slot to `Setup` that carries
only the movers, updated each step.

**Difficulty**: Moderate — touches `Kd`, `step-st`, `step-sts`.

### 2. Precompute ball next-positions, blocks just check `pos-eq`

Go further than approach 1: instead of passing mover *states*, precompute
each ball's *next position* once in `step`. Pass that as a list of positions.
Each block does `any-of (fn pos -> (pos-eq pos my-obs)) next-positions`
— a bare `pos-eq`, no `facing-toward` at all.

Currently `facing-toward` does two things per block × per object:
1. Check the object is actually moving (not stationary)
2. Compute the object's next position from its latent and check `pos-eq`

Both computations are identical across all blocks — only the final `pos-eq`
target differs. Precomputing eliminates the redundant work.

**Cost change**: O(blocks × total) → O(balls + blocks × n_balls)

**Trade-off**: Deeper change to `step`. Need to compute next-positions
using each ball's latent state before stepping, which means partially
duplicating the bouncer logic in `step`. Also, `facing-toward` has a
subtlety: it reads the ball's *current-step* latent to predict the *next*
action (because alt-bouncer alternates axes). This precomputation must
replicate that logic correctly.

**Difficulty**: Hard — duplicates bouncer knowledge outside of bouncer-kind.

### 3. Runtime-level memoization / thunk sharing

Each block's `facing-toward` call computes the same sub-expressions:
`do-action other-obs act`, the hturn/hdir/vdir branch, etc. These are
identical across all 28 blocks checking the same ball. If the runtime
shares these thunks (or memoizes `pos-eq`-related computations), the
redundant work collapses without any game-logic changes.

**Cost change**: Depends on sharing granularity. If the ball's next-position
computation is shared across all blocks, approaches O(total + blocks) —
each block only pays for its own `pos-eq` check.

**Trade-off**: This is a runtime/engine change, not a game-logic change.
May already partially happen via lazy evaluation, but the `any-of` loop
creates separate closures per block, which may prevent sharing. Would need
to investigate whether the current Pluck evaluator shares thunks across
`any-of` iterations.

**Difficulty**: Depends on current runtime — could be easy if sharing
infrastructure exists, hard if it doesn't.

### Recommendation

**Approach 1** (filter to movers) is the clear first move: simple to
implement, expressible in current Pluck, no runtime changes, and with
1 ball it turns 60+ `facing-toward` calls per block into 1. That alone
should cut breakout from ~11s to well under 1s at 20 steps.
