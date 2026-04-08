# Spatial Index: Design Sketch

## Idea

Instead of scanning all objects to answer "what's at position X?", build
a grid each step and do direct lookups. The grid is a 2D nested list —
`grid[x][y]` gives the list of objects at that cell.

## Current pain points

Both `occupied` and `block-kind`'s `facing-toward` scan all states:

```
occupied pos sts        → any-of (pos-eq pos ...) sts     O(total)
block facing-toward     → any-of facing-toward sts        O(total) per block
```

## Proposed structure

Coordinates range from -4 to 4. Offset to 0..8 to index a 9×9 nested list.

```pluck
;; A cell holds a list of entries at that position
;; Each entry has enough info for both occupied and facing-toward checks
;; (define-type entry (Entry latent action observable state))

;; Grid is a list of 9 columns, each a list of 9 cells
;; Each cell is a list of entries
;; (define-type grid (Grid columns))

;; Offset: convert signed coordinate to 0-based index
;; For half=4: add 4, so -4 → 0, 0 → 4, 4 → 8
(define (coord-to-index c half)
  (add c half))

;; grid-lookup: get the cell at (x, y)
(define (grid-lookup grid x y half)
  (nth (nth grid (coord-to-index x half))
       (coord-to-index y half)))
```

`nth` on a list is O(index), so lookup is O(x + y) ≈ 4-8 steps for
this grid. Comparable to one `int-eq` call but done once per query,
not once per object.

## Building the grid

Each step, scan all objects once and insert into grid by position:

```pluck
;; Start with empty 9×9 grid (each cell is Ni)
;; Insert each object into its cell based on cur-obs position

(define (empty-row size)
  ;; list of `size` empty cells (Ni)
  (match size
    Z -> (Ni)
    P n -> (Co (Ni) (empty-row n))))

(define (empty-grid size)
  ;; list of `size` empty rows
  (match size
    Z -> (Ni)
    P n -> (Co (empty-row size) (empty-grid n))))

;; Insert entry at (x, y) in grid — returns new grid
;; Walks to column x, then to row y, prepends entry to cell
(define (grid-insert grid x y entry)
  (list-update grid x
    (fn col -> (list-update col y
      (fn cell -> (Co entry cell))))))

;; list-update: replace element at index, returning new list
(define (list-update ls idx f)
  (match ls
    Co x rest ->
    (match idx
      Z -> (Co (f x) rest)
      P n -> (Co x (list-update rest n f)))))

;; Build grid from all objects
(define (build-grid sts half)
  (let ((size (add half (add half (P (Z))))))   ;; 2*half + 1
    (build-grid-iter sts (empty-grid size) half)))

(define (build-grid-iter sts grid half)
  (match sts
    Ni -> grid
    Co st rest ->
    (match st St slices ->
    (match (hd slices) Sc lat act obs ->
    (match obs Obs x y alive ->
    (ife alive
      (let ((entry (Entry lat act obs st))
            (ix (coord-to-index x half))
            (iy (coord-to-index y half)))
        (build-grid-iter rest (grid-insert grid ix iy entry) half))
      (build-grid-iter rest grid half)))))))
```

## How each kind uses the grid

### occupied (bouncers, water)

```pluck
;; O(1) cell lookup instead of O(total) scan
(define (occupied pos grid half)
  (match pos Obs x y _ ->
    (let ((cell (grid-lookup grid x y half)))
      (not-empty cell))))

(define (not-empty ls)
  (match ls Ni -> (F) Co _ _ -> (T)))
```

Bouncer-kind and water-kind replace `(occupied ahead sts)` with
`(occupied ahead grid half)`.

### block-kind (facing-toward)

Instead of scanning all 62 objects, check the 4 adjacent cells:

```pluck
(define (block-threatened obs grid half)
  (match obs Obs x y _ ->
    (let ((cells (Co (grid-lookup grid (pred x) y half)     ;; left
                (Co (grid-lookup grid (succ x) y half)      ;; right
                (Co (grid-lookup grid x (pred y) half)      ;; below
                (Co (grid-lookup grid x (succ y) half)      ;; above
                (Ni)))))))
      (any-of
        (fn cell ->
          (any-of
            (fn entry ->
              (match entry Entry other-lat act other-obs _ ->
              (band (obs-alive other-obs)
                    (facing-toward other-obs other-lat act obs))))
            cell))
        cells))))
```

4 cell lookups, then `facing-toward` on only the objects in those cells.
In breakout with 1 ball, most cells are empty or contain only walls —
so the inner `any-of` is typically 0-2 entries.

### block-kind updated

```pluck
(define block-kind
  (Kd (fn lat obs grid half ->
        (let ((hit (block-threatened obs grid half)))
          (Lat hit (F) (F))))
      (fn lat ->
        (match lat Lat hit _ _ ->
          (ife hit (Despawn) (X))))))
```

## step function

```pluck
(define (step setup)
  (match setup
    Setup kinds sts half ->
    (let ((grid (build-grid sts half)))
      (Setup kinds (step-sts kinds sts grid half) half))))

(define (step-st kind st grid half)
  (match st
    St slices ->
    (match (hd slices)
      Sc plat _ pobs ->
      (match kind
        Kd nextlat nextact ->
        (let ((new-lat (nextlat plat pobs grid half))
              (act (nextact new-lat))
              (new-obs (do-action pobs act)))
          (St (Co (Sc new-lat act new-obs) slices)))))))
```

The `nextlat` signature changes from `(lat, obs, all-sts)` to
`(lat, obs, grid, half)`. Grid is built once per step, shared by all.

## Cost summary

| Operation | Before | After |
|-----------|--------|-------|
| Build grid | — | O(total) per step |
| `occupied` | O(total) per call | O(half) per call (nth indexing) |
| Block hit check | O(total) per block | O(4 × half + objects-in-adjacent-cells) per block |
| Total per step | O(blocks × total + movers × total) | O(total + blocks × 4 + movers × half) |

For breakout (62 objects, 28 blocks, 1 ball, half=4):
- Before: 28 × 62 = 1736 facing-toward calls per step
- After: 28 × 4 lookups, ~0-2 facing-toward calls per block per step
- `occupied` calls (ball + water): ~4 per step, each O(4) instead of O(62)

## Trade-offs

**Pros:**
- Solves both `occupied` and `facing-toward` bottlenecks
- Grid is built once per step, used by everyone — clean separation
- Scales well: cost depends on local density, not total object count

**Cons:**
- `build-grid` is O(total) per step, with O(half) per insertion (nth indexing).
  For 62 objects × ~8 index steps ≈ 500 operations per step. Currently the
  non-block cost is already ~62, so this adds ~8x overhead to the cheap parts.
  Still dwarfed by the savings on blocks.
- `list-update` creates new list copies on each insertion (functional update).
  Building the grid means 62 insertions, each copying parts of the nested list.
  Not free, but small for a 9×9 grid.
- Grid coordinates must be bounded. Currently fine (half=4), but unbounded
  grids would need a different structure.
- More complex code — `empty-grid`, `grid-insert`, `list-update`, `coord-to-index`
  are all new machinery.
- Changes the `nextlat` signature for all kinds.

## Compared to per-kind lists approach

Per-kind lists (see PER_KIND_LISTS.md) are simpler: just filter the state
list so blocks scan ~1 ball instead of ~62 objects. That approach doesn't
help `occupied` (still O(total)), but `occupied` isn't currently a bottleneck.

The spatial index is more general — it helps any query that asks about
positions — but it's more machinery. If the game grows to have more
position-based interactions (e.g. objects checking surroundings, area
effects), the spatial index pays off more. For current breakout, per-kind
lists solve the immediate problem with less complexity.

| Approach | Block cost | occupied cost | Complexity |
|----------|-----------|---------------|------------|
| Current | O(blocks × total) | O(total) | Low |
| Per-kind lists | O(blocks × balls) | O(total) | Low-moderate |
| Spatial index | O(blocks × 4) | O(half) | Moderate-high |
