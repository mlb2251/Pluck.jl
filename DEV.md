# Tour of Pluck's Internals for Developers

This guide provides a brief tour of Pluck's internals for developers who want to extend the library. It assumes familiarity with the Pluck source language, as described in USAGE.md. It also assumes that developers have read and understood the paper introducing Pluck's key inference algorithm, "Stochastic Lazy Knowledge Compilation for Inference in Discrete Probabilistic Programs" (PLDI '25).

Dependency Versions: Pluck was developed with Julia 1.11.4 and Rust 1.86.0

## Core Architecture

Pluck's source code can be broadly divided into three components, organized into separate subdirectories of `src`:

1. **Language Layer** (`src/language/`): Implements Pluck's abstract syntax, parser, standard library, and runtime value representations
2. **Inference Engine** (`src/likelihood/`): Implements Pluck's core probabilistic inference algorithms, as well as "runners" that use the core inference algorithms to resolve different various queries
3. **BDD Backend** (`src/RSDD/`): Provides bindings to the Rust `rsdd` library, which implements efficient binary decision diagram operations

Note that this repository also contains a good amount of code that is not exercised by standard Pluck programming and query execution. For example, `src/language/grammar.jl` contains utilities for defining probabilistic grammars over subsets of the Pluck language, and using them to generate random Pluck programs. The files in the `src/search` directory build on this capability to implement stochastic synthesis algorithms that automatically build Pluck programs to model a given dataset. This guide does not aim to explain these components.

### Language Layer

The language layer is responsible for parsing, type checking, and executing Pluck programs. Key components:

- `types.jl`: Defines a Julia type, `SumProductType`, for user-defined algebraic datatypes in Pluck. Initializes a top-level type environment with the unit type, natural numbers, lists, and Booleans.
- `pexpr.jl`: Implements Pluck's abstract syntax, via the `PExpr` abstract type. Also defines the parser, `parse_expr`, which converts `String`s containing Pluck's s-expression syntax into `PExpr`s.
- `values.jl`: Implements Julia types to represent Pluck values, including values of algebraic datatypes (`Value`) and closures (`Closure`).
- `primitives.jl`: Defines names and arities of built-in primitives. The two primitives used by our example programs and in our experiments are `flip` and `constructors_equal`.
- `define.jl`: Julia macros for programmatically adding new definitions to Pluck's top-level environment.
- `toplevel.jl`: Handles `.pluck` file format and top-level program execution. This includes "runners" for different queries that can appear in `.pluck` files.
- `stdlib.pluck`: Pluck standard library (implemented in Pluck)

**To extend the language:**

The core Pluck language can be extended in several ways.

* New standard library functions, and new algebraic datatypes, can be implemented directly in Pluck, inside the `stdlib.pluck` file.

* New primitive functions that cannot be implemented (or implemented efficiently) within Pluck can be added as `PrimOp`s to the `primitives.jl` file. Note that the inference engine must also be extended to handle any new primitives (see `likelihood/bdd.jl` in particular).

* New top-level forms (like `define`, `define-type`, and `query`) can be added to `toplevel.jl`. Note that new queries (like `Marginal`, `Posterior`, etc.) are implemented by (1) extending the `Query` type defined in `stdlib.pluck`, and then (2) extending `toplevel.jl` to handle the new query.

* New language constructs can be added by extending `pexpr.jl` with a new subtype of `PExpr` representing the new form, extending `parse_expr` to parse the new form, and extending the inference engine to handle the new expression.

### Inference Engine

The inference engine implements probabilistic inference using knowledge compilation.

The following files implement different inference methods:
- `lazy_enumerator.jl`: Enumerative inference (a generally inefficient baseline). Depending on the `strict` field of the `LazyEnumeratorEvalState` struct, either implements lazy or strict enumeration. The workhorse function is `lazy_enumerate`, which dispatches on the type of its `expr` argument.
- `bdd.jl`: The main lazy knowledge compilation algorithm. The key function is `bdd_forward`, which is implemented for each expression type. Like the lazy knowledge compilation algortihm in the paper, `bdd_forward` accepts an expression, an environment, and a path condition (`available_information`) as input. (The "rose tree path" input -- `σ` in the paper -- is `state.callstack` in the code.) As in the paper, we return two things: a symbolic representation of the distribution represented by the expression, and a minimum validity condition (often called `used_information` in the code).
- `bdd_eager.jl`: A baseline that reimplements *standard* (eager) knowledge compilation.
- `bdd_suspend.jl`: Implements lazy programmable subproblem Monte Carlo (`subproblem_monte_carlo`), our approximate inference algorithm.
- `sample_value.jl`: Another interpretation strategy that simply samples a complete value, either following strict or lazy semantics.
- `posterior_sample.jl`: Method for resolving posterior sampling queries.

**Extending inference:**

When new language features are added, new cases will need to be added for each inference method. New inference methods can be added following the same pattern we follow in `lazy_enumerator.jl`, `bdd.jl`, and `bdd_eager.jl`.

### BDD Backend

The BDD backend provides efficient operations on binary decision diagrams:

- `RSDD.jl`: Julia bindings for the Rust BDD library
- `rsdd/`: Rust implementation of BDD operations. This is a submodule pinned to a specific branch of (our fork of) the `rsdd` library.

**To extend the BDD layer:**

1. Modify the Rust implementation in `rsdd/` for core changes
2. Add any new methods to the foreign function interface in the Rust library.
3. Recompile the rust library with `make bindings`, or by running `cargo build --release --features=ffi` from `rsdd/`
4. Add Julia bindings in `RSDD.jl`.