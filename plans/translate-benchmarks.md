# Translating Julia benchmark files to Pluck assert-query files

## Key insight

The code inside `@define "name" "..."` strings in the Julia `.jl` files **is already valid Pluck**. Pluck supports `Y`, `case ... of`, `constructors_equal`, `true`/`false`, etc. The translation is mostly direct copying with minimal wrapping.

## Inputs

1. **Julia source**: A `.jl` file in `/Users/maddy/proj/julia/PluckArtifact.jl/src/table1/` containing `@define` blocks and `add_benchmark!` calls.
2. **Expected results**: A `.json` file in `/Users/maddy/proj/julia/PluckArtifact.jl/expected_plots/table1_2025-07-29_12-10-08/ours/` with the expected probability distribution.
3. **Output location**: `programs/table1/<name>.pluck` in the Pluck.jl repo.

## Step-by-step process

### 1. Copy `@define` blocks as `(define name <expr>)`

Each `@define "name" "<expr>"` becomes `(define name <expr>)` — copy the expression string verbatim.

**Example** — from `hmm.jl`:
```julia
@define "hmm" """
(Y (λ rec z0 ->
  (let (z1 (flip (if z0 0.7 0.1)))
    (Cons (flip (if z1 0.3 0.6)) (rec z1)))))
"""
```
becomes:
```scheme
(define hmm
  (Y (λ rec z0 ->
    (let (z1 (flip (if z0 0.7 0.1)))
      (Cons (flip (if z1 0.3 0.6)) (rec z1))))))
```

That's it — the body is copied verbatim.

### 2. Convert `define_type!` calls to `(define-type ...)`

```julia
Pluck.define_type!(:pcfg_grammar_symbol, Dict(:SS => Symbol[], :XX => Symbol[], :YY => Symbol[], :a => Symbol[], :b => Symbol[], :c => Symbol[]))
```
becomes:
```scheme
(define-type pcfg_grammar_symbol (SS) (XX) (YY) (a) (b) (c))
```

For types with arguments, e.g. `Dict(:Foo => [:bar, :baz])`, write `(Foo bar baz)`.

### 3. Handle programmatic definitions

Some definitions are built in Julia code rather than `@define` strings. Two common patterns:

**`make_uniform(options)`** — constructs nested flips for uniform distribution. Replace with Pluck's `(uniform ...)`:
```julia
DEFINITIONS[:random_char] = Pluck.Definition(:random_char, make_uniform(CHARACTERS))
```
becomes:
```scheme
(define (random_char)
  (uniform (a_) (b_) (c_) (d_) (e_)))
```
Note: In the original, `random_char` is a bare value (each reference gets a fresh copy via inline substitution). In `.pluck` files, define it as a zero-arg function `(define (random_char) ...)` and call it as `(random_char)` at each use site. Update references in copied `@define` bodies: bare `random_char` → `(random_char)`.

**Julia string-building functions** — functions like `julia_string_to_expression`, `make_string_from_julia_list`, `pluck_list` construct Pluck list literals. Manually expand them. For example:
```julia
julia_string_to_expression("edcc")
# produces: (Cons (e_) (Cons (d_) (Cons (c_) (Cons (c_) (Nil)))))
```
```julia
pluck_list([0, 3, 7])
# produces: (Cons 0 (Cons 3 (Cons 7 (Nil))))
```

### 4. Assemble the query from `add_benchmark!`

Look at the `pluck_default` benchmark to find the query expression:
```julia
add_benchmark!("hmm", "pluck_default", PluckBenchmark("(hmm_example 50)"; pre=hmm_defs))
```

The query string `"(hmm_example 50)"` is the Pluck expression to run. If `hmm_example` is itself a `@define`'d function, inline it:
```julia
@define "hmm_example" "(λ n -> (prefix_equals? (hmm (False)) (generate_observations n)))"
```
So `(hmm_example 50)` = `(prefix_equals? (hmm (False)) (generate_observations 50))`.

### 5. Write `assert-query` with expected probabilities

Read the `.json` file:
```json
{
  "result": [
    [{"constructor": "False", "args": []}, 0.9999999999998197],
    [{"constructor": "True", "args": []}, 1.802995485540675e-13]
  ]
}
```

Format as:
```scheme
(assert-query
  'hmm
  (Marginal
    (prefix_equals? (hmm (False)) (generate_observations 50)))
  ((False) 0.9999999999998197)
  ((True) 1.802995485540675e-13))
```

### 6. Add to table1.pluck

Add `(include "table1/<name>.pluck")` to `programs/table1.pluck`.

## Complete examples

All four table1 sequence models have been translated — see:
- `programs/table1/sorted_list.pluck` ← `sorted_list.jl`
- `programs/table1/hmm.pluck` ← `hmm.jl`
- `programs/table1/string_editing.pluck` ← `string_editing.jl`
- `programs/table1/pcfg.pluck` ← `pcfg.jl`

## Checklist

- [ ] Copy each `@define` body verbatim into `(define name ...)`
- [ ] Convert `define_type!` to `(define-type ...)`
- [ ] Expand any Julia-side code generation (string building, `make_uniform`) manually
- [ ] Replace bare `random_char` references with `(random_char)` if it was a programmatic definition
- [ ] Find the `pluck_default` query in `add_benchmark!`, inline any helper lambdas
- [ ] Read expected `.json`, add probabilities to `assert-query`
- [ ] Add `(include ...)` to `table1.pluck`
