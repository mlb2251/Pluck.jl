# Plan: `make check` command

## Original prompt

> I'd like to be able to run "make check" much like "make test" except basically it would do the following. It would run all the queries including ones that are just `query` instead of `assert-query` just so that crashes are caught in those even tho they dont involve asserts. It would also run all asserts. It would print out only the PASS and FAIL statements. It would end with printing out how many fails there were and the overall thing would crash if there was at least one fail (but all fails would get printed, this is just about crashing at the end). Instead of printing the name + time + pass we would print on one line: pass/fail + name + file. And we wouldn't print results, so each would be just one line. And it wouldn't say "how many" passed/failed bc we dont care about that for subresults.

## Current state

- `make test` runs `Pluck.run_examples()` which iterates all `.pluck` files in `programs/` and calls `load_pluck_file(file)` on each.
- `load_pluck_file` → `run_toplevel` → parses and evaluates all top-level forms.
- **`query`** forms: execute query, print results (name, time, distribution/samples). No pass/fail.
- **`assert-query`** forms: execute query, print results, then check expected values and print PASS/FAIL.
- Output is verbose: full result distributions are printed for both query types.

### Key files
- `src/util/tests.jl` — `run_examples()`
- `src/toplevel/eval.jl` — `eval_toplevel` methods for `QueryOp` and `AssertQueryOp`
- `src/toplevel/printing.jl` — `print_query_results`, `print_query_results_by_type`
- `Makefile` — build targets

## Design

### New mode: `check` mode

Add a `check::Bool` parameter that flows through the system. When `check=true`:

1. **All queries run** (both `query` and `assert-query`) — so crashes are caught everywhere.
2. **No results printed** — suppress `print_query_results_by_type` calls entirely.
3. **One-line output per query:**
   - `assert-query`: `PASS: query-name (filename)` or `FAIL: query-name (filename): <reason>` — uses the existing assertion logic, just reformatted.
   - `query`: runs silently (no assertions to check, no output). It still executes so if it crashes Julia propagates the error normally.
4. **Accumulate fail count** across all files.
5. **At the end**: print total fail count and `error()` if > 0.

### Implementation steps

#### 1. Add `check` field to `ToplevelEvalState`

In `src/toplevel/eval.jl`, add a `check::Bool` field and a `fail_count::Ref{Int}` field to `ToplevelEvalState`:

```julia
mutable struct ToplevelEvalState
    defs::Dict{Symbol, Definition}
    parser::ParseState
    silent::Bool
    check::Bool
    fail_count::Ref{Int}  # shared across files so we can accumulate
    current_file::String   # for printing filename alongside pass/fail
end
```

Update the constructor call in `run_toplevel` to pass new fields (defaulting `check=false`, `fail_count=Ref(0)`, `current_file=filename`).

#### 2. Modify `eval_toplevel` for `QueryOp` in check mode

When `check=true`:
- Run the query as normal (no try-catch — if it crashes, it crashes Julia, which is fine).
- Don't print results (skip `print_query_results_by_type`).
- No PASS/FAIL output — plain `query` has no assertions, so nothing to report. It just needs to not crash.

#### 3. Modify `eval_toplevel` for `AssertQueryOp` in check mode

When `check=true`:
- Run query execution as normal (no try-catch).
- Don't print results (skip `print_query_results_by_type`).
- Run the existing assertion checks, but reformat the output:
  - If all assertions pass: print `PASS: <name> (<filename>)` in green.
  - If any fail: print `FAIL: <name> (<filename>): <reason>` in red for each failure, increment `fail_count`.
- This is the same logic that already exists in `eval_toplevel(AssertQueryOp)`, just with results suppressed and the PASS/FAIL lines reformatted to include filename and exclude time/assertion-count.

#### 4. Add `run_check()` function in `src/util/tests.jl`

```julia
function run_check()
    fail_count = Ref(0)
    for file in readdir(joinpath(@__DIR__, "..", "..", "programs"); join=true)
        if endswith(file, ".pluck")
            load_pluck_file(file; check=true, fail_count)
        end
    end
    n = fail_count[]
    if n > 0
        printstyled("\n$n failure$(n == 1 ? "" : "s")\n"; color=:red, bold=true)
        error("check failed with $n failure$(n == 1 ? "" : "s")")
    else
        printstyled("\nAll checks passed\n"; color=:green, bold=true)
    end
end
```

#### 5. Thread `check` and `fail_count` through `load_pluck_file` / `run_toplevel`

Add `check=false` and `fail_count=Ref(0)` keyword arguments to both functions, pass them into `ToplevelEvalState`.

#### 6. Add Makefile target

```makefile
check:
	julia --project -e 'using Pluck; Pluck.run_check()'
```

#### 7. Export `run_check`

Add `run_check` to the exports in the appropriate place (likely `src/util/tests.jl` or the main module file).

### Output format examples

```
PASS: first-two-elements-are-zero (fig2.pluck)
PASS: second-element-given-first-and-third (fig2.pluck)
FAIL: lazy-to-lucky (fig1.pluck): value (True) expected prob 1.5768926660718637e-10, got 0.0
PASS: goat-or-bat (fig1.pluck)
PASS: hmm-smoothing (hmm.pluck)

1 failure
ERROR: check failed with 1 failure
```

Plain `query` forms produce no output (they just run silently; if they crash, Julia errors out normally).

### What stays the same

- `make test` / `run_examples()` behavior is completely unchanged.
- Normal `load_pluck_file` usage (REPL, etc.) is unchanged — `check` defaults to `false`.
- No changes to parsing.
- No changes to the actual query execution logic.

### Edge cases

- **`PosteriorSamples` queries used with plain `query`**: Non-deterministic, can't be asserted against. In check mode they just run silently — no output unless they crash.
- **`include` directives**: These call `load_pluck_file` recursively. The `check` and `fail_count` should propagate through the `kwargs...` that already get forwarded.
