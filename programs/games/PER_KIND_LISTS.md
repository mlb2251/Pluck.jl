# Per-Kind Lists: Design Sketch

## Current Architecture

Flat parallel lists — `(Setup kinds states)` where `kinds` and `states` are
same-length lists walked in lockstep. Every kind's `nextlat` receives the
full `all-sts` list.

```
Setup
├── kinds:  [wall, wall, ..., block, block, ..., bouncer]
└── states: [st,   st,   ..., st,    st,    ..., st     ]
```

## Proposed Architecture

Group objects by kind — `(Setup groups)` where each group bundles a kind
with its state list.

```
Setup
└── groups:
    ├── Group wall-kind   [st, st, ...]     (33 walls)
    ├── Group block-kind  [st, st, ...]     (28 blocks)
    └── Group bouncer-kind [st]             (1 ball)
```

```pluck
;; (define-type group (Group kind states))
;; (define-type setup (Setup groups))
```

## What Changes

### step

Before:
```pluck
(define (step setup)
  (match setup
    Setup kinds sts ->
    (Setup kinds (step-sts kinds sts sts))))
```

After:
```pluck
(define (step-group group all-groups)
  (match group
    Group kind sts ->
    (Group kind (map-ls (fn st -> (step-st kind st all-groups)) sts))))

(define (step setup)
  (match setup
    Setup groups ->
    (Setup (map-ls (fn g -> (step-group g groups)) groups))))
```

### nextlat signature

Before: `nextlat :: Latent -> Observable -> AllStates -> Latent`
After:  `nextlat :: Latent -> Observable -> Groups -> Latent`

Each kind receives the list of groups and picks what it needs.

### occupied

Needs to scan all groups (bouncers/water need to know about walls, other
bouncers, everything):

```pluck
(define (occupied-in-states pos sts)
  (any-of
    (fn st ->
      (let ((obs (cur-obs st)))
        (band (obs-alive obs) (pos-eq pos obs))))
    sts))

(define (occupied pos groups)
  (any-of
    (fn group ->
      (match group Group _ sts ->
        (occupied-in-states pos sts)))
    groups))
```

Same total cost as before — O(total objects). Just nested.

### block-kind

This is where the win is. Block-kind currently scans all 60+ states for
`facing-toward`. With per-kind groups, it can scan only the bouncer group:

```pluck
(define (make-block-kind bouncer-index)
  (Kd (fn lat obs groups ->
        (let ((bouncer-sts (group-states (nth groups bouncer-index)))
              (hit (any-of
                     (fn st ->
                       (match st St slices ->
                       (match (hd slices) Sc other-lat act other-obs ->
                       (band (obs-alive other-obs)
                             (band (bnot (pos-eq other-obs obs))
                                   (facing-toward other-obs other-lat act obs))))))
                     bouncer-sts)))
          (Lat hit (F) (F))))
      (fn lat ->
        (match lat Lat hit _ _ ->
          (ife hit (Despawn) (X))))))
```

`any-of` now scans ~1 ball instead of ~60 objects per block per step.

### Other kinds (no behavioral change)

```pluck
(define wall-kind
  (Kd (fn lat obs groups -> lat)
      (fn lat -> (X))))

(define bouncer-kind
  (Kd (fn lat obs groups ->
        (match lat
          Lat dir b c ->
          (let ((ahead (do-action obs (ife dir (R) (L)))))
            (ife (occupied ahead groups)
              (Lat (bnot dir) b c)
              lat))))
      (fn lat ->
        (match lat Lat dir _ _ -> (ife dir (R) (L))))))

;; alt-bouncer-kind, water-kind: same — just pass groups to occupied
```

## How block-kind finds the bouncer group

The groups list has no inherent labels. Options:

**A) Positional convention.** Bouncers are always at a known index.
`block-kind` is constructed with that index (see `make-block-kind` above).
Setup code in `run.jl` controls the ordering and passes the right index.

**B) Kind tags.** Add a tag field to `Kd` or `Group`:
```pluck
;; (define-type group (Group tag kind states))
```
Then `block-kind` searches groups for the one tagged `:bouncer`. More
flexible but adds a scan-groups cost (trivial — just ~3-4 groups).

**C) Explicit wiring.** Pass the bouncer state list directly to
`make-block-kind` at setup time as a closure variable. But states change
each step, so this doesn't work without re-closing each step.

Option A is simplest. The Julia `run.jl` already controls group ordering,
so it can just ensure bouncers are at index 0 (or wherever) and construct
`block-kind` accordingly.

## Cost Summary

| Operation | Before | After |
|-----------|--------|-------|
| block `any-of` | O(blocks × total) | O(blocks × n_balls) |
| bouncer `occupied` | O(total) | O(total) (nested over groups) |
| water `occupied` | O(total) | O(total) (nested over groups) |
| `step` overhead | O(total) | O(total) + O(n_groups) |

With 1 ball, block scanning goes from O(28 × 62) = 1736 to O(28 × 1) = 28
per step. ~60x reduction in the bottleneck.

## Open Questions

- Does the Pluck evaluator handle nested `any-of` (groups → states) as
  efficiently as flat `any-of`? Shouldn't matter in practice since the
  nesting is shallow (3-4 groups).
- Could water benefit similarly? Currently water calls `occupied` 3 times
  per step over all objects. With groups it's the same cost, but if water
  only cared about walls + other water (not blocks), it could skip groups
  too. For now that's not a bottleneck though.
- `extract_trajectory` in `run.jl` currently expects a flat states list.
  Would need to flatten groups back out for extraction, or adapt the
  extraction code.
