# Using Pluck

Pluck is a probabilistic programming language designed for efficient inference on discrete probabilistic models.

This guide will walk you through how to write Pluck programs and run queries, while showcasing several examples that demonstrate the language's capabilities.

## Table of Contents

1. [Writing a Basic Pluck Program](#writing-a-basic-pluck-program)

2. [Running a Pluck Program](#running-a-pluck-program)

3. [Guided Exploration](#guided-exploration)
  * [String Editing (Figure 1)](#string-editing-example-from-figure-1)
  * [Sorted List (Figure 2)](#sorted-list-generation-example-from-figure-2)
  * [Other Example Programs](#other-programs)

4. [Language Reference](#language-reference)
  * [Syntax](#syntax)
  * [Algebraic Datatypes](#defining-and-using-algebraic-datatypes)
  * [Defining Functions](#defining-and-using-functions)
  * [Queries](#queries)
  * [Primitive Distributions](#primitive-distributions)

5. [Sharp Edges](#sharp-edges)
  * [Termination and Non-Termination](#termination-and-non-termination)
  * [Overwriting Prelude Definitions](#overwriting-prelude-definitions)
  * [Performance Considerations](#performance-considerations)

## Writing a Basic Pluck Program

A Pluck program consists of a sequence of *top-level forms*, which may be:
- type definitions (using `define-type`),
- function definitions (using `define`), and
- queries (using `query`).

For example, the following program defines a function and queries the probability that it returns a value greater than five.

```scheme
;; Define a function with parameter p.
(define (generate-number p) 
  ;; (geom p) samples from a geometric distribution
  ;; with parameter p.
  (+ (geom p) (geom 0.2)))

;; Example query:
;; Compute the marginal probability distribution
;; of the expression (> (generate-number 0.7) 5)
;; (that is, compute the probability that it returns
;;  true and that it returns false).
(query
  ;; Query name:
  num-greater-than-five
  ;; Query:
  (Marginal 
    (> (generate-number 0.7) 5)))

;; Example query:
;; Posterior distribution of the generated number,
;; given that it is less than 5.
;; Requires the posterior to have finite support.
(query 
  ;; Query name:
  posterior-given-less-than-five 
  ;; Query:
  (let ((n (generate-number 0.7)))
    ;; Compute the exact posterior P(n | n < 5)
    (Posterior 
      n 
      (< n 5))))
```

More examples can be found in the `programs` directory, including the programs from Figures 1 and 2 in our paper (`fig1.pluck` and `fig2.pluck`). 

In Visual Studio Code, we have found that when editing `.pluck` files, it is nice to set the language to Clojure (to use Clojure syntax highlighting and auto-formatting via the `cljfmt` extension).

## Running a Pluck Program

Start julia by running `julia --project` from the `Pluck.jl` folder. To compile a Pluck file, run:
```julia
julia> using Pluck
julia> load_pluck_file("programs/simple_example.pluck");

num-greater-than-five:
  false  0.7064862000000001
  true   0.2935138000000001

posterior-given-less-than-five:
  1  0.24317453299436276
  0  0.22106775726760244
  2  0.21443572454957446
  3  0.17751740908588484
  4  0.14380457610257547
```

All definitions will be loaded into the top-level environment, and the results of each query in `simple_example.pluck` will be printed to the console. Note that when Pluck is asked to compute an exact probability distribution, the distribution must have finite support for Pluck to terminate; see [Termination and Non-termination](#termination-and-non-termination) for details. The possible values are printed along with their probabilities when the query is run, sorted in descending order by probability.

The `load_pluck_file` function can be called multiple times from within the same Julia session. All `define`s from previously loaded files are visible in files loaded later.

## Guided Exploration

In this section, we explain some of the examples in the `programs` repository, and suggest follow-up ideas to explore using Pluck.
Feel free to jump around to whatever seems interesting. See also the [next section](#language-reference) for a more complete language reference and warnings about [sharp edges](#sharp-edges). All queries in this section should run in at most a few seconds, though Julia may take more time to compile Pluck's code the first time you load a file.

### String editing example from Figure 1.

Open `programs/fig1.pluck`. It defines the `perturb` function from Figure 1 of the paper, which models the process by which a typist noisily adds typos to a string: 

```scheme
;; new type with 26 constructors for the characters
;; of the English alphabet.
(define-type char
  (a_) (b_) (c_) (d_) (e_) (f_) (g_) (h_) (i_)
  (j_) (k_) (l_) (m_) (n_) (o_) (p_) (q_) (r_)
  (s_) (t_) (u_) (v_) (w_) (x_) (y_) (z_))

;; `(uniform e1 ... en)` randomly chooses one of its arguments to return.
(define (random_char)
  (uniform (a_) (b_) (c_) (d_) (e_) (f_) (g_) (h_) (i_)
           (j_) (k_) (l_) (m_) (n_) (o_) (p_) (q_) (r_)
           (s_) (t_) (u_) (v_) (w_) (x_) (y_) (z_)))

;; list=? (defined in src/language/stdlib.pluck) takes as an argument 
;; a predicate for comparing two elements for equality.
;; Here, we use the built-in `constructor=?` which checks if two values 
;; of user-defined types have the same constructor.
(define string=? (list=? constructor=?))

;; Code from Figure 1
(define (maybe_insert s)
  (if (flip 0.99) s (Cons (random_char) (maybe_insert s))))

(define (maybe_cons c cs)
  (if (flip 0.99) (Cons c cs) cs))

(define (maybe_substitute c)
  (if (flip 0.99) c (random_char)))

(define (perturb s)
  (match s
    Nil => (maybe_insert (Nil))
    Cons c cs =>
    (let ((perturbed_cs (perturb cs)))
      (maybe_insert (maybe_cons (maybe_substitute c) perturbed_cs)))))
```

It also demonstrates how to perform Pluck's three kinds of query:
* **Marginal probability queries:** the `lazy-to-lucky` query asks the marginal probability that a string is perturbed from "lazy" to "lucky".
  ```scheme
  (query
   ;; Query name
   lazy-to-lucky
   ;; Query
   (Marginal
    (string=?
      (perturb (Cons (l_) (Cons (a_) (Cons (z_) (Cons (y_) (Nil))))))
      (Cons (l_) (Cons (u_) (Cons (c_) (Cons (k_) (Cons (y_) (Nil)))))))))
  ```
  This outputs:
  ```
  lazy-to-lucky:
    false  0.9999999998423106
    true   1.5768926660718637e-10
  ```
  That is, under our model of typos, it would be highly unlikely for someone who intended to type "lazy" to accidentally type "lucky."

* **Posterior probability distribution queries:** the `goat-or-bat` query asks for the posterior P(original string | observed string = "gat"), when we know that the original string is either "goat" or "bat":
  ```scheme
  (query
    ;; Query name:
    goat-or-bat
    ;; Query:
    (let ((original_string
            ;; Uniform prior on "goat" vs. "bat"
            (if (flip 0.5)
              (Cons (g_) (Cons (o_) (Cons (a_) (Cons (t_) (Nil)))))
              (Cons (b_) (Cons (a_) (Cons (t_) (Nil))))))
          ;; Observe the string "gat"
          (observed_string
            (Cons (g_) (Cons (a_) (Cons (t_) (Nil))))))

      ;; Posterior over `original_string` variable,
      ;; conditioned on the observed string.
      (Posterior
        ;; Query expression -- A in "P(A | B)"
        original_string
        ;; Evidence -- B in "P(A | B)"
        (string=?
          (perturb original_string)
          observed_string))))
    ```
    This outputs:
    ```
    goat-or-bat:
      Any[(g_), (o_), (a_), (t_)]  0.9615418808827687
      Any[(b_), (a_), (t_)]        0.03845811911723137
    ```
    This indicates that under our model, "goat" is more likely to be the intended word. The reason is that it is less likely for the typist to have accidentally chosen *both* to replace the "b" in "bat" *and* to select "g" (out of all possible letters) as the replacement, than to have just accidentally deleted the "o" from "goat".
* **Posterior sample queries:** if a user intends to type "cat" and the third letter they type is an "a", what did they probably type? Because there are infinitely many possibilities, we cannot ask for the full distribution, but we can generate posterior samples. Here, we generate 15.
  ```scheme
  (query
    ;; Query name:
    cat-third-char
    ;; Query:
    (let ((typed-string
            (perturb
            (Cons (c_) (Cons (a_) (Cons (t_) (Nil)))))))
      (PosteriorSamples
        ;; query expression, A in P(A | B)
        typed-string
        ;; evidence expression, B in P(A | B)
        (constructor=? (index 2 typed-string) (a_))
        ;; number of samples to draw
        15)))
  ```
  This outputs different samples each run, but one example output is:
  ```
  cat-third-char:
    Any[(g_), (c_), (a_), (t_)]
    Any[(l_), (c_), (a_), (t_)]
    Any[(c_), (n_), (a_), (t_)]
    Any[(c_), (f_), (a_), (t_)]
    Any[(x_), (c_), (a_), (t_)]
    Any[(c_), (a_), (a_)]
    Any[(c_), (a_), (a_)]
    Any[(s_), (c_), (a_), (t_)]
    Any[(q_), (c_), (a_), (t_)]
    Any[(r_), (c_), (a_), (t_)]
    Any[(q_), (n_), (a_), (t_)]
    Any[(g_), (c_), (a_), (t_)]
    Any[(c_), (r_), (a_), (t_)]
    Any[(c_), (c_), (a_), (t_)]
    Any[(c_), (a_), (a_), (t_)]
  ```
  We see that under our model, the user likely inserted a letter somewhere before the "a" in "cat," but it is also not implausible that the "t" in "cat" was just replaced with an "a".

**Things to try:**
- Try altering the probabilities of insertions, deletions, and substitutions, by changing the literal 0.99s in the `maybe_insert`, `maybe_cons`, or `maybe_substitute` functions.
- Try making some substitutions more likely than others. For example, instead of just calling `(random_char)` in `maybe_substitute`, you could try `(if (constructor=? c (i_)) (uniform (a_) (e_) (o_) (u_) (random_char)) (random_char)))`, to encode the assumption that `i` is more likely to be subsituted with another vowel than with a different random character. Modify the goat-or-bat query to see the effects of this change (e.g., check whether "hat" is more likely a typo of "cat" or "hit"). Run the query with your changes and without your changes.
- Try writing a recursive `generate_word` function that takes in a length `n` and generates a list of `n` random characters. Implement a `PosteriorSamples` query to draw samples of what five-letter word the user may have intended to type, given an obesrved word. Note that natural numbers are just an algebraic datatype in our language, with constructors `(O)` (a capital o) representing zero, and `(S n)` for successor. The syntax 
    ```scheme
    (match n 
      O => expr-if-zero
      S m => expr-if-succ)
    ```
    can be used to pattern-match on them.
- We can rewrite `perturb` to also return a *trace* of the choices it makes. We define a new type for the elements of the trace, e.g. `(define-type action (Insert string) (Type char) (Delete char) (Substitute char char))`. Then we edit each helper function to return a pair (with syntax `(Pair a b)`) containing the modified string and a list of the edits it made. We can then draw posterior samples of traces given an observation. (It is generally too expensive to enumerate the full exact posterior.) For instance:
    ```scheme       
      (define-type action (Insert string) (Type char) (Delete char) (Substitute char char))

      ;; Version of `maybe_insert` that also returns a trace
      (define (random_string)
        (if (flip 0.99)
          (Nil)
          (Cons (random_char) (random_string))))
      (define (maybe_insert_traced s)
        (let ((insertion (random_string)))
          (Pair
          ;; Value
          (append insertion s)
          ;; Trace
          (match insertion
            Nil => (Nil)
            Cons _ _ => (Cons (Insert insertion) (Nil))))))

      ;; Version of `maybe_substitute` that also returns a trace
      (define (maybe_substitute_traced c)
        (if (flip 0.99)
          (Pair
          ;; Value
          c
          ;; Trace
          (Nil))
          (let ((new_c (random_char)))
            (Pair
            ;; Value
            new_c
            ;; Trace
            (Cons (Substitute c new_c) (Nil))))))

      ;; Version of `maybe_cons` that also returns a trace
      (define (maybe_cons_traced c cs)
        (if (flip 0.99)
          (Pair
          ;; Value
          (Cons c cs)
          ;; Trace
          (Cons (Type c) (Nil)))
          (Pair
          ;; Value
          cs
          ;; Trace
          (Cons (Delete c) (Nil)))))

      (define (perturb_traced s)
        (match s
          Nil => (maybe_insert_traced (Nil))
          Cons c cs =>
          (let ((perturbed_cs_traced (perturb_traced cs))
                (new_c_traced (maybe_substitute_traced c))
                (with_deletion_traced (maybe_cons_traced (fst new_c_traced) (fst perturbed_cs_traced)))
                (with_insertion_traced (maybe_insert_traced (fst with_deletion_traced))))
            (Pair (fst with_insertion_traced)
                  (append
                  (snd with_insertion_traced)
                  (append
                    (snd new_c_traced)
                    (append
                    (snd with_deletion_traced)
                    (snd perturbed_cs_traced))))))))

      ;; How might "hello" have been modified to yield "halo"?
      (query
      posterior-on-traces
      (let ((result (perturb_traced (Cons (h_) (Cons (e_) (Cons (l_) (Cons (l_) (Cons (o_) (Nil))))))))
            (typed-word (fst result))
            (trace (snd result)))
        (PosteriorSamples
          trace
          (string=? typed-word (Cons (h_) (Cons (a_) (Cons (l_) (Cons (o_) (Nil))))))
          10)))
    ```

### Sorted list generation example from Figure 2.

Open `programs/fig2.pluck`. It contains the program from Figure 2, which generates sorted lists of natural numbers. 

```scheme
(define (mkSortedList n)
  (if (flip 0.5)
    (Nil)
    (let (x (+ n (geom 0.5)))
      (Cons x (mkSortedList x)))))
```

It has queries that calculate (1) the probability that the first two elements of the list are zero; (2) the distribution of the second element, fixing the first and third; and (3) samples from the posterior conditioning on the sixth element being 3. Running the file should give you the following query results (with the last query varying each run, as it is a sampling query):
```
first-two-elements-are-zero:
  false  0.9375
  true   0.0625

second-element-given-first-and-third:
  2  0.25
  3  0.25
  4  0.25
  5  0.25

posterior-samples-given-sixth-elem-is-3:
  Any[0, 0, 0, 0, 1, 3]
  Any[1, 2, 2, 3, 3, 3]
  Any[0, 2, 2, 3, 3, 3]
  Any[0, 2, 2, 2, 2, 3, 5, 5]
  Any[0, 1, 2, 2, 3, 3]
  Any[2, 2, 3, 3, 3, 3, 4, 4, 6, 7, 7]
  Any[0, 0, 2, 2, 2, 3]
  Any[2, 2, 3, 3, 3, 3, 3, 3, 4, 10, 10, 13]
  Any[0, 0, 0, 3, 3, 3]
  Any[0, 0, 3, 3, 3, 3, 7, 8, 8, 8]
  Any[0, 1, 1, 1, 2, 3]
  Any[0, 1, 1, 1, 1, 3]
  Any[0, 0, 0, 0, 3, 3]
  Any[1, 1, 1, 1, 3, 3]
  Any[0, 0, 0, 0, 3, 3, 6]
```

**Things to try:**
- Write a query computing the posterior distribution of the third element of a randomly generated sorted list, given that it is less than 10.
- Change the model to generate lists that sorted in reverse, by changing + to -. Note that the argument `n` is now the maximum value, rather than the minimum value, of the generated list. Change the queries accordingly.

### Other programs

In the `programs` directory, you will also find:
* `programs/hmm.pluck`: a Hidden Markov Model with Boolean latent states and observations. It currently contains queries for (1) computing the *smoothing* posterior distribution of the 11th latent state, given 50 observations, and (2) sampling the full posterior over 50 latent states given 50 observations. You might try performing inference over different patterns of observations, or changing the HMM to have a larger latent state space.
* `programs/pcfg.pluck`: A program implementing two example probabilistic context-free grammars. The second PCFG is a toy English grammar that generates sentences like "the cat eats the tasty bone and the dog barks". Queries include the full distribution over sentences shorter than a given length; the full distribution over short sentences where the fifth word is "tasty"; and sampling from the posterior over long sentences (longer than 8 words) where the fifth word is "tasty". You might try implementing new queries, e.g. a "posterior probability of next word" query given a fixed prefix.


## Language Reference

### Syntax
A **program** is a sequence of **top-level forms.**

A **top-level form** is one of:

* a **value definition** of the form `(define <var> <expr>)`
* a **function definition** of the form `(define (<func-name> <arg-1> ... <arg-n>) <expr>)`.
* a **type definition** of the form `(define-type <type-name> (<constructor-1> <arg1-1> ... <arg1-n>) ... (<constructor-m> <argm-1> ... <argm-k>))`.
* a **query** of the form `(query <query-name> <expr>)`.

An **expression** is one of:

* a **variable** `<var>`
* a **let-expression** `(let ((<var> <expr>) ... (<var> <expr>)) <expr>)`.
* an **if-then-else expression**  of the form `(if <expr> <expr> <expr>)`.
* a **match expression** of the form 
  ```scheme
  (match <expr>
    <constructor-1> <var-1-1> ... <var-1-n> => <expr-1>
    ...
    <constructor-m> <var-m-1> ... <var-m-k> => <expr-m>)
  ```
* an **anonymous function** of the form `(lambda <arg1> ... <argn> -> <expr>)`.
* a **constructor expression** of the form `(<constructor> <expr-1> ... <expr-n>)`.
* an **application** of the form `(<expr> <expr-1> ... <expr-n>)`. 
* a **floating-point or natural-number constant** of the form `<const>`.
* a **random primitive** expression, of the form:
  - `(flip <expr>)`
  - `(uniform <expr-1> ... <expr-n>)`
  - `(discrete (<expr-1> <const-1>) ... (<expr-n> <const-n>))`, where the constants are floating-point numbers summing to 1.

Expressions used inside the `(query <expr>)` form must evaluate to a value of type `query`, defined in `language/src/stdlib.pluck`. See detailed notes below.

### Defining and Using Algebraic Datatypes

New (recursive) algebraic data types can be defined using the syntax `(define-type <type-name> (<constructor> <arg-type>...) ...)`. Note that currently, because the Pluck implementation is untyped, the `<arg-type>`s can be instantiated with any symbol, and primarily convey user intent. (However, the arity of each constructor is determined by the number of listed arguments.)

Several types are built in:
```scheme
;; Tuple type
(define-type pair (Pair any any))
;; Natural numbers -- either zero (O) or successor (S nat)
(define-type nat (O) (S nat))
;; Unit type
(define-type unit (Unit))
;; Boolean type
(define-type bool (True) (False))
;; List type
(define-type list (Nil) (Cons any list))
```

To construct a value of an algebraic datatype, use the syntax `(<constructor> <arg-1> ... <arg-n>)`. For instance, a tuple is constructed as `(Pair e1 e2)` and a list as `(Cons 3 (Cons 2 (Nil)))`. Natural number literals are automatically parsed as repeated applications of the `nat` constructors (e.g. `2` is automatically converted into `(S (S (O))))`).

Algebraic datatypes support pattern matching using the syntax 
```scheme
(match <scrutinee> 
  <constructor1> <var1-1> ... <var1-n>  => <expr1>
  <constructor2> <var2-1> ... <var2-m> => <expr2>
  ...)
```

For example, the standard library (in `src/language/stdlib.pluck`) implements several functions for processing the built-in types, including

```scheme
;; Extract first element from a pair
(define (fst pair)
  (match pair
    Pair a b => a))

;; Extract second element from a pair
(define (snd pair)
  (match pair
    Pair a b => b))

;; Map a function over a list
(define (map f l)
  (match l
    Nil => (Nil)
    Cons x xs => (Cons (f x) (map f xs))))
```

Note that all patterns have a single constructor and then one variable per argument. That is, nested patterns are not supported (e.g. you *cannot* match against `(Cons x (Nil))`). There is no "else" pattern.

Several built-in functions exist for equality comparison. The `constructor=?` function accepts two arguments, both of some algebraic datatype, and checks whether they have the same constructor. The function `==` compares natural numbers. The function `list=?` takes three arguments: a predicate for comparing elements of the lists, and two lists. For example, `(list=? ==)` is an equality predicate for lists of natural numbers.

### Defining and Using Functions

The top-level form `(define (<func-name> <arg-1> ... <arg-n>) <body>)` can be used to define new functions. Anonymous functions can be defined using `lambda`: `(lambda <arg-1> ... <arg-n> -> <body>)`. All multi-argument functions are automatically curried, and `(f x y z)` is sugar for `(((f x) y) z)`. 

As sugar, `(define (<fname>) <body>)`, `(lambda -> <body>)`, and `(<expr>)` can be used as shorthand for `(define (<fname> _) <body>)`, `(lambda _ -> <body>)`, and `(<expr> (Unit))`, respectively.

Functions defined with `define` may use any previously defined name in their body, including the name being defined (for recursive definitions). Anonymous recursive functions can be defined using the built-in Y-combinator `(Y (lambda <fname> <arg-1> ... <arg-n> -> <body>))`. We do not have special syntax for mutually recursive functions, but it is possible to define them using `Pair`, e.g.

```scheme
(define even-and-odd
  (let ((even (fst even-and-odd)) 
        (odd  (snd even-and-odd)))
    (Pair 
      (lambda n -> 
        (match n
          O => (True)
          S m => (odd m)))
      (lambda n -> 
        (match n 
          O => (False)
          S m => (even m))))))
(define even (fst even-and-odd))
(define odd (snd even-and-odd))
```

In general, `define` is intended to be used for *function* definitions, and possibly other deterministic constants. Evaluating a definition should not require making random choices (e.g. do **not** write `(define b (flip 0.5))`); intuitively, random choices are tracked when they happen while evaluating queries, either because the query expression itself makes random choices or because it calls previously defined functions that do.

### Queries

Query expressions have the form `(query <name> <expr>)`, where the expression must evaluate to a value of type `query`. The query type has three constructors, which correspond to three kinds of query you can execute:

* `(Marginal <expr>)`: compute the full marginal distribution over possible values that `<expr>` can take on.
* `(Posterior <expr> <bool-expr>)`: compute the posterior distribution over possible values that `<expr>` can take on, given that `<bool-expr>` is true. 
* `(PosteriorSamples <expr> <bool-expr> <nat-expr>)`: generate `<nat-expr>` samples from the posterior distribution over possible values that `<expr>` can take on, given that `<bool-expr>` is true.

A query commonly has the form
```scheme
(query
  <name>
  (let 
    ((x <expr>)
     (y <expr>)
     ...)
  (Posterior
    <some-expr-involving-local-vars>
    <some-expr-involving-local-vars>)))
```

A query expression should not require using randomness to figure out what the query is, e.g. `(query my-bad-query (if (flip 0.5) (Marginal ...) (Posterior ...)))` will result in an error.

### Primitive Distributions

The key primitive for random sampling is `flip`, which takes in a floating-point number `p` and returns `(True)` with probability `p`, and `(False)` with probability `1-p`.

The constructs `(uniform e1 ... en)` and `(discrete (e1 p1) ... (en pn))` are macros that the compiler automatically expands into "decision trees" of coin flips. In `flip`, the argument `p` can be a dynamically determined value, but in `discrete`, the probabilities must be constant floating-point literals that sum to 1. So, `(flip (if b 0.2 0.7))` is OK, but `(discrete (x (if b 0.2 0.7)) (y (if b 0.8 0.3)))` is not; write `(if b (discrete (x 0.2) (y 0.8)) (discrete (x 0.7) (y 0.3)))` instead.

The geometric distribution is defined in the standard library, using `flip`, and thus can accept a dynamic argument:

```scheme
;; geometric distribution
(define (geom p)
  (if (flip p)
    (O)
    (S (geom p))))
```

## Sharp Edges

### Termination and Non-termination

Executing a query may lead to non-termination. Each query has different requirements for termination, but they all rest on the notion of *lazy sure termination.* 

Intuitively, an expression `e` lazily surely terminates if `(print e)`, when executed by a lazy (call-by-need) interpreter, terminates for every possible random seed. 

(We do not implement `print` within Pluck, but we use it as an example of a function that would fully force its argument's value within a lazy language. For example, a lazy interpreter would halt immediately--without sampling any random values--when given the expression `(Cons (flip 0.5) (Nil))`, because it is already in weak-head normal form. But `(print (Cons (flip 0.5) (Nil)))` would force the coin flip to occur.)

As an example, `(geom 0.5)` is *not* lazily surely terminating, because there is a seed on which it never halts (where every `flip` comes up tails). But `(< (geom 0.5) 10)` is lazily surely terminating, because lazy evaluation only looks at (at most) the first 11 coin flips before halting.

By query, the requirements for termination are as follows:
- `(Marginal <expr>)` terminates if <expr> is lazily surely terminating.
- `(Posterior <expr> <bool>)` terminates if `(if <bool> <expr> (Unit))` lazily surely terminates. For example, the query `(let (n (geom 0.5)) (Posterior n (< n 10)))` will terminate, even though `(Posterior (geom 0.5) (True))` would not.
- `(PosteriorSamples <expr> <bool> <nat>)` terminates (with probability 1) if `<bool>` lazily surely terminates and `(if <bool> <expr> (Unit))` lazily *almost* surely terminates (i.e., terminates for all but a probability-0 set of random seeds). For example, the query `(PosteriorSamples (geom 0.5) (True) 20)` does terminate, because `(geom 0.5)` terminates for all but a probability-zero set of random seeds (those leading to an infinite stream of tails).

If you run a non-terminating query, using Ctrl+C inside the Julia REPL should cancel the query without exiting the Julia REPL.

### Overwriting Prelude Definitions

Consider the type definition

`(define-type non-terminal (S) (V) (N) (Adj) (V) (NP) (VP))`

that you might see in a definition of a probabilistic grammar for English. A subtle issue is that `S` is already a constructor defined by Pluck's prelude/standard library, for the successor of a natural number. Pluck allows the user to silently overwrite the definition of `S`, but all built-in functions relying on natural numbers no longer work, leading to runtime errors. A similar case to watch out for is `Y`, which is the Y combinator.

### Stack Overflows

Pluck's compiler is currently implemented recursively in Julia, and programs that are themselves recursive and make deeply nested function calls may lead to stack overflows. This will cause the query to fail but the Julia REPL should stay alive, so it is possible to edit the program and try again. We are hoping to implement optimizations to prevent this in the near future.

### Performance Considerations

In addition to [non-terminating queries](#termination-and-non-termination), it is also possible to write queries that run very slowly.

* **Lazy evaluation.** Pluck uses laziness to help prune the space of program executions it needs to explore. A good rule of thumb is to try to write query expressions and posterior conditioning predicates so that a lazy interpreter would be able to return the result of the query expression or predicate after generating only a small fraction of the data structure to which it is being applied. Similarly, it is useful to write the probabilistic programs themselves in such a way that they generate data lazily if possible, computing (e.g.) the first element of a list before the second.

  Because [non-termination](#termination-and-non-termination) is also based on the lazy operational semantics of a program, sometimes a non-terminating query can be rewritten into a terminating one. For example, consider a program that generates a random list of Booleans, and queries the probability that the length is less than 10 and all elements are `(True)`:

  ```scheme
  (define (generate-list) 
    (if (flip 0.5)
     (Nil) 
     (Cons (flip 0.3) (generate-list))))
  (define (all l)
    (match l
      Nil => (True)
      (Cons x xs) => (and x (all xs))))
  
  ;; A *non-terminating* query:
  ;; (query 
  ;;   bad-query
  ;;   (let (xs (generate-list))
  ;;     (Marginal (and (all xs) (< (length xs) 10)))))
  
  ;; A *terminating* query:
  (query 
    good-query
    (let (xs (generate-list)) 
      (Marginal (and (< (length xs) 10) (all xs)))))
  ```
  The first query (`bad-query`) will not terminate, because 
  there is a pathological random seed that causes `(all xs)` 
  to loop infinitely (the seed where `generate-list` never stops generating). The second query avoids this problem, by first checking whether the length is less than 10, and only evaluating `(all xs)` if it is. Note that `(< (length xs) 10)` terminates no matter what in a lazy language, because `<` short-circuits and returns `(False)` as soon as 10 elements have been generated.

* **Variable order**: Knowledge compilation, the technique that powers Pluck's inference, builds *binary decision diagrams* to represent a program's semantics. The performance of these BDDs can be sensitive to the *variable order*--an ordering on all the random choices a program makes. Queries that run quickly under one variable order can become exponentially slow under another. 

  In Pluck, variable order is based on the order in which a *strict* interpreter would encounter random choices. For example, in `(let ((x (flip 0.3)) (y (flip 0.4))) (or y x))`, `x` comes before `y` in the variable order, despite the fact that lazy evaluation looks at y first. Thus, users can change the variable order by (for instance) reordering let statements in their programs.

  In general, it is hard to reason clearly about how variable order affects performance. However, a desirable situation is that when A and C are conditionally independent given B, they are ordered as A B C (or C B A). That is, generating variables later in a program should ideally not have to "reach back" to the beginning of the program; they should ideally be able to rely only on more recently sampled variables.
  
  For instance, in our hidden Markov model (`programs/hmm.pluck`), we *could have* written the program to generate a stream of latents, then `map` the observation function over the latents. However, this would lead to a variable order in which all latents occur before all observations. This means that the very first observation has to "reach back" past all of the latents to find the first latent state (upon which it depends). This variable order does not allow us to exploit any of the conditional independence structure that is abundant in the model. By contrast, we implemented the program to interleave generation of latents and observations, so that each variable only depends on the previous one or two sampled variables.


* **Repeated sub-expressions**: An expression like `(+ (f x) (f x))` is not in general equivalent to `(let ((y (f x))) (+ y y))`, because `f` may make random choices; the first expression performs the random choices twice (independently) whereas the second performs them only once. However, if the shared sub-expression appears in a branch, e.g. `(if (flip 0.4) (+ 3 (f x)) (* 2 (f x)))`, it is recommended to assign a single variable for use in both branches: `(let ((y (f x))) (if (flip 0.4) (+ 3 y) (* 2 y)))`. This does not change the distribution denoted by the program, but operationally, allows us to create a single thunk for `(f x)`, rather than two.

