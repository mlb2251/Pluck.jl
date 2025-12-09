You're working on a probabilistic programming system called Pluck. Files in this system are .pluck files.

To get up to speed, do the following:
- Read `USAGE.md`
- read the examples in `programs/*.pluck`
- read the standard library in `src/language/stdlib.pluck`

---

## Recent Development: Toplevel Forms as Builtins + Auto-Marginal Wrapping (Dec 9, 2024)

### Overview
Converted the `define` and `define-type` toplevel forms into Pluck builtins with side-effecting semantics. This makes `define` usable inside expressions (e.g., conditional defines). Also added auto-wrapping of standalone parenthesized expressions as Marginal queries for a more interactive REPL-like experience.

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

#### 2. Special Parsing for Define
**File**: `src/language/parsing.jl` (lines 275-330)

The `define` builtin has special parsing logic (not using `define_parser!`) that mirrors toplevel syntax:

```julia
elseif token == "define"
    tokens = view(tokens, 2:length(tokens))

    if tokens[1] == "("
        # Function definition: (define (fname args...) body)
        # Parse fname and args, construct lambda, return DefineOp()(ConstNative(fname)(), lambda)
        ...
    else
        # Value definition: (define x expr)
        # Parse name and expr, return DefineOp()(ConstNative(name)(), expr)
        ...
    end
end
```

This allows using define in expressions with the same syntax as toplevel:
- `(define (myadd a b) (+ a b))` instead of `(define 'myadd (fn a b -> (+ a b)))`
- `(define x 5)` instead of `(define 'x 5)`

#### 3. Toplevel Define Desugaring
**File**: `src/language/toplevel.jl` (lines 277-354)

Toplevel `(define x expr)` now desugars to `(query x-def (Marginal (define x expr)))`:

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

#### 4. Define-Type Builtin Implementation
**Files**:
- `src/language/pexpr.jl` (lines 332-333): DefineTypeOp head definition
- `src/likelihood/lazy_knowledge_compilation/compile_inner.jl` (lines 262-275): Builtin implementation
- `src/language/toplevel.jl` (lines 356-387): Toplevel desugaring

The `define-type` builtin modifies the global type definition dictionaries at compile/runtime:

```julia
function compile_inner(expr::PExpr{DefineTypeOp}, env, path_condition, state)
    bind_compile(expr.args[1], env, path_condition, state, 0) do type_name_val, path_condition
        bind_compile(expr.args[2], env, path_condition, state, 0) do constructors_val, path_condition
            # Define the type
            Pluck.define_type!(type_name_val.value, constructors_val.value)
            return pure_monad(Value(:Unit), path_condition, state)
        end
    end
end
```

**Toplevel define-type desugaring (lines 375-386)**:
```julia
# Define the type immediately at parse time so constructors are available to parser
define_type!(type_name, constructors)

# Create the desugared query: (Marginal (define-type 'name constructors))
define_type_call = DefineTypeOp()(ConstNative(type_name)(), ConstNative(constructors)())
query_expr = Construct(:Marginal)(define_type_call)

# Execute the query to update runtime type definitions
process_query(query_expr, string(type_name) * "-type-def"; silent=true)
```

**Important**: Type definitions happen at both parse time (so constructors are available to the parser) and runtime (via the builtin query execution).

#### 5. Auto-Marginal Wrapping
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
;; Define different values based on a flip - using new syntax!
(query test-conditional-define
  (let ((coin (flip 0.5)))
    (match (if coin
             (define result 100)
             (define result 200))
      Unit => (Marginal (lookup 'result)))))
;; Output: result → 100 (p=0.5), 200 (p=0.5)

;; Function definition in expression context - much nicer now!
(query test-function
  (match (define (myadd a b) (+ a b))
    Unit => (let ((add (lookup 'myadd)))
              (Marginal (add 10 20)))))
;; Output: 30
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
   (match (define z 42)
     Unit => (Marginal (lookup 'z)))
   ```

2. **Runtime-Defined Names**: Names defined via the builtin at runtime aren't available to the parser. Access them via `(lookup 'name)`:
   ```scheme
   (match (define (multiply a b) (* a b))
     Unit => (let ((mult (lookup 'multiply)))
               (Marginal (mult 6 7))))
   ```

3. **New Define Syntax**: The builtin now uses the same syntax as toplevel:
   - Function: `(define (fname args...) body)` - no quotes, no explicit lambda
   - Value: `(define x expr)` - no quotes
   - This is parsed specially to create `DefineOp()(ConstNative(name)(), expr_or_lambda)`

4. **Toplevel vs Builtin**: Toplevel `(define x 5)` updates parser state immediately. Builtin `(define x 5)` only updates runtime DEFINITIONS.

5. **Define-Type at Parse and Runtime**: `define-type` executes at both parse time (to make constructors available to the parser) and runtime (via the builtin). This dual execution ensures constructors work correctly in all contexts.

### Test Files

**Define builtin tests:**
- `programs/dec9-refactor.pluck` - Comprehensive tests for define builtin
- `programs/test-define-new-syntax.pluck` - Tests for new define syntax (without quotes)
- `programs/demo-new-features.pluck` - Demo of define and auto-wrapping features

**Define-type builtin tests:**
- `programs/test-define-type.pluck` - Simple define-type tests
- `programs/test-define-type-builtin.pluck` - Tests showing desugaring to builtin

**Auto-marginal tests:**
- `programs/test-auto-marginal.pluck` - Tests for auto-wrapping feature

All existing programs (simple_example.pluck, fig1.pluck, fig2.pluck, etc.) continue to work unchanged.

### Future Work (Not Yet Implemented)

The original plan included converting other toplevel forms to builtins:
- ✅ `define` - Value and function definitions (completed)
- ✅ `define-type` - Type definitions (completed)
- `query` - Named queries
- `include` - File inclusion

The remaining forms (`query` and `include`) await future implementation if needed.