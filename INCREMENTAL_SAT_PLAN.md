# Incremental SAT Performance Plan

## Problem

On `programs/subsets/hmm_scaling.pluck hmm-50` (~100ms total), the CDCL-based SAT checking is slower than BDD-based `bdd_is_false`. Stats from a run:

```
CDCL Stats
──────────────────────────────────────
  Calls
    check_assuming!     1703
    new_selector!       1703
    solver_from         51
  Search
    propagations        380195  (223.3/check)
    conflicts           316
    decisions           378174
  Time breakdown (total 0.089s)
    check_assuming!     0.088s  99%
      propagation       0.025s
      other (decide+bt) 0.063s
    new_selector!       0.000s  0%
    solver_from         0.000s  0%
  Solver size (avg per check)
    variables           738.1
    clauses             1361.7
    assumption depth    25.1
──────────────────────────────────────
```

## Diagnosis

**378,174 decisions but only 316 conflicts.** The solver spends almost all its time finding satisfying assignments by brute force. Most checks are SAT, and without phase saving the solver blindly tries `true` for every variable until it stumbles into a model. This results in ~222 decisions per check on average.

The 0.063s in "other (decide+bt)" is almost entirely `_vsids_pop!` being called 378k times — heap operations to pick variables that would have been trivially satisfied with cached phases.

## Fixes (priority order)

### 1. Phase saving [HIGH IMPACT] — IMPLEMENTED

Add a `phase::Vector{Int8}` to `CDCLSolver`. On backtrack, save `assigns[v]` into `phase[v]` before clearing it. On decision, use the saved phase instead of always deciding `true`.

**Why:** If the previous call found a satisfying assignment, the solver will re-decide the same polarities and (in the common case where the formula barely changed between calls) find SAT with ~0 conflicts and ~0 wrong decisions. Should drop decisions from 378k to near-zero for SAT checks.

### 2. Level-0 propagation watermark [MEDIUM IMPACT]

`cdcl_check_assuming!` sets `s.qhead = 1` every call, re-propagating the entire level-0 trail (223 propagations/check). Track a `qhead_stable` high-water mark so only newly added Tseitin clauses trigger re-propagation.

**Why:** Avoids redundant BCP work across incremental calls. The level-0 trail only changes when new clauses are added via `cdcl_new_selector!`.

### 3. Restarts [MEDIUM IMPACT for UNSAT cases]

No restart strategy exists. Add Luby or geometric restarts to prevent getting stuck in bad search subtrees.

**Why:** The 316 conflicts that do occur could be resolved faster with restarts. Less critical than phase saving since most checks are SAT.

### 4. Learned clause deletion [LOW-MEDIUM IMPACT]

Clauses grow unboundedly (avg 1361 clauses). Add activity-based clause garbage collection: keep short/high-activity clauses, delete the rest.

**Why:** Prevents BCP slowdown as clause DB grows. Impact depends on how long the solver lives.

### 5. Learned clause minimization [LOW IMPACT]

`_cdcl_analyze!` does 1UIP but no recursive self-subsumption minimization. Smaller learned clauses propagate faster.

### 6. Assumption-level granularity [LOW IMPACT for this workload]

Currently all assumptions asserted at a single level 1. MiniSat-style puts each assumption at its own decision level for conflict-driven assumption pruning (learn *which* assumption caused UNSAT).

**Why:** Only helps UNSAT cases, which are the minority here.
