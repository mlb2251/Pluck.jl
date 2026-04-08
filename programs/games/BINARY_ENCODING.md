# Binary Position Encoding: Analysis

## Idea

Replace Peano integers `(Z) (P (P ...)) (N (N ...))` with fixed-width
binary bit strings for positions. Comparisons become O(log n) instead of
O(n), and laziness means mismatches on the MSB short-circuit without
forcing later bits.

## Current Peano behavior

Positions in breakout range from -4 to 4. `int-eq` is recursive:

```pluck
(define (int-eq a b)
  (match a
    Z -> (match b Z -> (T) P _ -> (F) N _ -> (F))
    P a' -> (match b Z -> (F) P b' -> (int-eq a' b') N _ -> (F))
    N a' -> (match b Z -> (F) P _ -> (F) N b' -> (int-eq a' b'))))
```

The signed Peano representation already gives a "free first bit":
- `P` vs `N` → instant reject (positive vs negative)
- `P` vs `Z` → instant reject
- `P` vs `P` → recurse, stripping one layer

For magnitude-4 numbers, worst case is 4 steps (equal numbers of same
sign). Most mismatches hit the `P`/`N`/`Z` split in 1-2 steps.

This is essentially a unary sign prefix — you get the first level of
binary MSB benefit already.

## What binary would look like

4-bit MSB-first representation (covers -8 to 7):

```pluck
;; (define-type bit (B0) (B1))
;; number is a list of bits, MSB first, with sign bit

(define (bits-eq a b)
  (match a
    Ni -> (match b Ni -> (T) Co _ _ -> (F))
    Co x xs ->
    (match b
      Ni -> (F)
      Co y ys ->
      (band (bit-eq x y) (bits-eq xs ys)))))
```

Comparison: check MSB first, short-circuit on mismatch. For small
magnitudes (-4 to 4), this is 2-4 bit checks — similar to Peano's
2-4 constructor peels.

## Arithmetic complexity

Peano arithmetic is trivial:
```pluck
(define (succ x) (match x Z -> (P (Z)) P n -> (P (P n)) N n -> n))
```

Binary arithmetic requires carry propagation:
```pluck
(define (succ-bits bits)
  (match bits
    Ni -> (Co (B1) (Ni))
    Co bit rest ->
    (match bit
      B0 -> (Co (B1) rest)
      B1 -> (Co (B0) (succ-bits rest)))))
```

`add` needs a full adder with carry. Signed binary adds sign handling
on top. Significantly more complex than Peano for the same operations.

## Cost comparison for breakout (half=4, positions -4..4)

| Operation   | Peano     | Binary (4-bit) |
|-------------|-----------|----------------|
| int-eq      | 1-4 steps | 1-4 bit checks |
| succ / pred | O(1)      | O(log n) with carry |
| add         | O(n)      | O(log n) with carry |
| storage     | n nodes   | log n nodes |

For magnitude ≤ 4, comparison cost is roughly the same. Peano's signed
constructors (`P`/`N`/`Z`) already provide an immediate sign-mismatch
rejection, which is the main thing binary MSB would give you.

## When binary would matter

- **Large coordinate spaces** — magnitude >> 10, where Peano comparison
  is O(n) and binary is O(log n)
- **Heavy arithmetic** — lots of `add` operations on large numbers
- **Memory pressure** — Peano stores magnitude-n numbers as n-node chains,
  binary uses log-n nodes

None of these apply to the current breakout game (magnitude ≤ 4, only
`succ`/`pred` used, small grid).

## Verdict

The signed Peano encoding already provides the most valuable property of
binary: immediate rejection on sign mismatch. For the small coordinates
in breakout, per-comparison cost is similar either way (~2-4 steps).

The bottleneck is comparison count (28 blocks × 62 objects), not
per-comparison cost. Structural changes (per-kind lists, mover filtering)
address the real problem. Binary encoding would be worth revisiting if the
game scales to larger grids.
