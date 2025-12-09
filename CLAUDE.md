You're working on a probabilistic programming system called Pluck. Files in this system are .pluck files.

To get up to speed, do the following:
- Read `USAGE.md`
- read the examples in `programs/*.pluck`
- read the standard library in `src/language/stdlib.pluck`

---

## Recent Development: Define Builtin and Auto-Marginal Wrapping (Dec 9, 2024)

### Overview
Converted the `define` toplevel form into a Pluck builtin with side-effecting semantics, making it usable inside expressions (e.g., conditional defines). Also added auto-wrapping of standalone expressions as Marginal queries for a more interactive REPL-like experience.

### Key Changes

#### 1. Define Builtin Implementation
**File**: `src/likelihood/lazy_knowledge_compilation/compile_inner.jl` (lines 250-260)

The `define` builtin modifies the global `DEFINITIONS` state at compile/runtime:

```julia
function compile_inner(expr::PExpr{DefineOp}, env, path_condition, state)
    bind_compile(expr.args[1], env, path_condition, state, 0) do name_val, path_condition
        @assert name_val isa NativeValue{Symbol}

        # Store the UNEVALUATED expression (expr.args[2]) directly
        Pluck.DEFINITIONS[name_val.value] = Pluck.Definition(name_val.value, expr.args[2])

        return pure_monad(Value(:Unit), path_condition, state)
    end
end
```

**Critical insight**: Only evaluate the first argument (the name symbol), store the second argument (expression) unevaluated.

#### 2. Toplevel Define Desugaring
**File**: `src/language/toplevel.jl` (lines 277-354)

Toplevel `(define x expr)` now desugars to `(query x-def (Marginal (define 'x expr)))`:

```julia
# Function definitions:
define_call = DefineOp()(ConstNative(fname)(), expr)
query_expr = Construct(:Marginal)(define_call)
process_query(query_expr, string(fname) * "-def"; silent=true)

# Value definitions:
define_call = DefineOp()(ConstNative(name)(), expr)
query_expr = Construct(:Marginal)(define_call)
process_query(query_expr, string(name) * "-def"; silent=true)
```

This provides a unified implementation - single code path for both toplevel and builtin defines.

#### 3. Auto-Marginal Wrapping
**File**: `src/language/toplevel.jl` (lines 387-421)

Any standalone parenthesized expression at toplevel automatically executes as a Marginal query:

```julia
# Non-parenthesized expressions error out
if token != "("
    error("Expected opening paren at start of toplevel form, got: $token")
end

# Parenthesized expressions (if not a special form like define, query, etc.)
else
    expr, rest = parse_expr_inner(tokens, ParseState(defs, []))
    query_expr = Construct(:Marginal)(expr)
    result = process_query(query_expr, "expr-" * string(hash(expr)); silent=silent)
    return (:expr, expr, result), rest
end
```

### Usage Examples

#### Conditional Defines (Key Use Case)
```scheme
;; Define different values based on a flip
(query test-conditional-define
  (let ((coin (flip 0.5)))
    (match (if coin
             (define 'result 100)
             (define 'result 200))
      Unit => (Marginal (lookup 'result)))))
;; Output: result → 100 (p=0.5), 200 (p=0.5)
```

#### Auto-Wrapped Expressions
```scheme
;; Toplevel defines work as before
(define x 5)
(define (square n) (* n n))

;; Parenthesized expressions automatically execute and show results:
(+ x 3)                     ;; → 8
(if (flip 0.7) 100 200)     ;; → 100 (p=0.7), 200 (p=0.3)
(square 5)                  ;; → 25

;; Note: Non-parenthesized expressions like just "x" are not allowed at toplevel
```

### Important Implementation Details

1. **Lazy Evaluation**: Defines must be forced to evaluate. Use pattern matching:
   ```scheme
   (match (define 'z 42)
     Unit => (Marginal (lookup 'z)))
   ```

2. **Runtime-Defined Names**: Names defined via the builtin at runtime aren't available to the parser. Access them via `(lookup 'name)`:
   ```scheme
   (match (define 'multiply (lambda a b -> (* a b)))
     Unit => (let ((mult (lookup 'multiply)))
               (Marginal (mult 6 7))))
   ```

3. **Toplevel vs Builtin**: Toplevel `(define x 5)` updates parser state immediately. Builtin `(define 'x 5)` only updates runtime DEFINITIONS.

### Test Files

- `programs/dec9-refactor.pluck` - Comprehensive tests for define builtin
- `programs/test-auto-marginal.pluck` - Tests for auto-wrapping feature
- `programs/demo-new-features.pluck` - Demo of all new features

All existing programs (simple_example.pluck, fig2.pluck, etc.) continue to work unchanged.

### Future Work (Not Yet Implemented)

The original plan included converting other toplevel forms to builtins:
- `define-type` - Type definitions
- `query` - Named queries
- `include` - File inclusion

These were explicitly deferred ("lets just do define first") and await future implementation.