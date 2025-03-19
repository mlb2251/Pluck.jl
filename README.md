# coarse-to-fine-synthesis

## julia versioning
[Install julia](https://julialang.org/downloads/). Right now we're on julia version `1.10.3` though you can also check this in `Manifest.toml`. Probably anything past julia `1.10.0` is fine, which is when multithreaded garbage collection was added. Once you've installed the latest version fo julia you can switch versions with `juliaup add 1.10.3` and then `julia +1.10.3` to install and launch a specific version (or for latest version just do `juliaup update` and then just `julia`). Check version with `julia --version` or the `VERSION` global variable within a julia session.

## Viewing visualizations

Launch a server with `python3 -m http.server 8000` in the project directory. Now the links to visualizations (starting with [http://localhost:8000/](http://localhost:8000/)) should work

## Quick start and random things you might want to do

I generally start with a new julia session and run `using Revise; includet("examples/examples.jl"); def_constructors();` to load `examples/examples.jl` as a place I can write new test little functions and such (and `includet` to automatically reload it when you modify it). `def_constructors()` comes from `src/definitions.jl` and has tons of all user defined library functions.

### Likelihood evaluation through `constrain()`
Geometrically distributed nat is 2 with probability 1/8:
```
julia> exp(weight(constrain("randnat", [], to_value(2))))
0.12500000000000003
```

The odds that mapping a lambda that samples a random digit (0..9) over some length 6 list and getting the list [1,1,3,4,5,5] is 10^-6 because it involves 6 choices that each are a 1/10 chance of choosing the right digit:
```
julia> constrain("(map (λx -> make_random_digit) #1)", [to_value([0,0,0,0,0,0])], to_value([1,1,3,4,5,5])) |> weight |> exp
1.0000000000000023e-6
```

**Common gotcha / mistake** Note if you forget to wrap the environment variables or output variable in `to_value()` itll just report likelihood zero (but should probably actually be some sort of type error).

**Common gotcha / mistake** The first time you run constrain on something it might take way longer do to julia compiling things on first usage and therefore fail due to the time limit on likelihood calculations – so always rerun things.

Example of customizing time limit for likelihood evaluation and also recording the trace of the calculation in json that you can visualize (it will print a generated link): 
```
julia> constrain("(map (λx -> make_random_digit) #1)", [to_value([0,0,0,0,0,0])], to_value([1,1,3,4,5,5]), EvalState(;time_limit=1, record_json=true)) |> weight |> exp
```

`def_constructors()` in `src/definitions.jl` is also a good place to go to look for how to evaluate likelihoods through `constrain` because there are a bunch of tests at the end of that function.

### enumeration
This was only added yesterday so is very under construction but the basic usage is:
`test_prio(;steps=200)` which comes from `examples/examples.jl`

Note that the first time you run this the search might take really long and go the wrong direction because of julia just in time compilation – run it a second time and it should find the answer within around a second and like <30 search steps.

My next goal is to actually get this running across a whole benchmark of tests at once so we can start looking at how this enumeration approach works and where it might not be great (and how to adapt it to help with that!) – don't expect it to work out of the box, but we're interested to hear what does or doesnt work. Also please feel free to ask further clarification on this

For example I already know it gets stuck on this simple dreamcoder origami domain list program (the list length function) and debugging that is next on the list after getting a fuller evaluation of the datasets:

`task=load_tasks("data/origami/origami.json")[1]; print(task); test_prio(;steps=200, task=task, cfg=origami_cfg(), root=origami_graph_root(task.type));`

And meanwhile this dreamcoder list domain function similarly it runs into issues on, though it makes more progress:

`task=filter_tasks(load_tasks("data/compression_benchmark/io_examples/list.json"))[1]; print(task); test_prio(;steps=500, task=task, cfg=dc_list_cfg());`

I may not have included all the relevant data files for those so let me know if you need them and I should upload or submodule everything or something.

My next step is to get the benchmarks running on all the data and then start seeing what could help repair some of these search issues / where they're running into problems or if I just had some basic oversight with them that we can fix (and integrate some of the ideas like DSL learning, unrolled DSLs, possibly MCTS style search, etc).

## Files
Obviously this should be organized better

Files in `src/`

- Pluck.jl - toplevel package
- addresses.jl - used in a reachability analysis that is not currently being done
- bench.jl - utilities/structs for evaluating likelihoods
- cfgs.jl - definition of context free grammars (the "CFG" type)
- define.jl - the @define macro and friends
- definitions.jl - this is where we put all the user defined function definitions like `map` and `fold` and such. def_constructors() is the main thing in there that defines and tests a bunch of these. The other function def_classic() is more outdated and is from before we had sum product types.
- graph.jl - defines the `Graph` (and `Node`) type used to represent a search graph over the space of programs
- hash_spn.jl - this is the current version of sum product network (`SPN`) used to compactly store large sets of randomness traces. It's an adaptation of the older `spn.jl` to now use structural hashing for extra sharing.
- parse_yandp.jl - utilities for parsing all the yang and piantadosi data from their appendix
- pexpr.jl - exports the `PExpr` type which is our expression type! Note `Expr` is taken by julia itself.
- primitives.jl - primitive structs are defined in here, however note that many of them like `ConsOp` are from before we had sum product types and are thus no longer used. Also the logprob/enumerate definitions in here are unused (see note about `enumerate.jl` above). `primops_minimal` in this file is the one that we're using as our current small set of primitives. This should be split into two files to separate out the old stuff.
- productions.jl - defines the production rule type `ReplacementProd` used when expanding an expression in a coarse to fine way. `consistent_prods` here is function that should be renamed that checks whether an expression is a coarse to fine ancestor of another (ie can one be expanded through some sequence of expansions to get to the other)
- prof.jl - profiling utilites, in particular `@prof` is a profiler.
- solutions.jl - ground truth solutions for origami / dreamcoder list domains
- spe.jl - this is the core likelihood evaluation function `constrain` and its mutually recursive friend `forward`. 
- strategies.jl - search strategies. Right now enumeration and an old (probably not working but easily fixable) version of sampling based search are there.
- subexprs.jl - useful utilities provided through the `SubExpr` type which tracks a `PExpr` and its type `PType` and environment and such and thus allows some nice traversing of expressions while tracking envs/types etc.
- tasks.jl - `PTask` type and friends, which is our actual task struct (io-examples and type and such)
- test_yandp.jl - Some quick tests I wrote for basic yang and piantadosi likelihood stuff working.
- trial_util.jl - pretty print utilities for the type `BenchmarkTools.Trial` (adapted from `BenchmarkTools.jl`)
- types.jl - defines `PType` which is our type for types, along with sum product types through `SumProductType`
- util.jl - utils of course
- values.jl - `Value` which is sum product type values, also Thunk and Closure are defined in here. to_value() to_value() etc are there as helper functions for converting normal julia types to Values. There's old outdated stuff like `struct Cons` from before this era.

Files in `src/unused/`
- chains.jl - (not used) old approach to synthesis
- debruijn.jl - (not used) debruijn shifting logic we needed back when we used substitution
- dsl.jl - (not used) before the `CFG` era we were using this `DSL` type
- enumerate.jl - (not used, but could be revived) before the constrain/forward era we were using enumerate/logprob which does not account for memoized randomness (i.e. using the same random result in more than one place by passing it into a function as an argument). Parts of this might come back into the system as a likelihood optimization in places where memoization is unncessary.
- logprob.jl - (not used, but could be revived) see note from `enumerate.jl`
- spe_no_caseof.jl - (not used) extension of `spe.jl` for the things from before the era of sum product types
- old_spn.jl - (not used) older verison of `hash_spn.jl` we should delete this to avoid confusion
- streams.jl - (not used) backburner approach to likelihood evaluation that is a lazy version of some of the constrain/forward ideas and can get you upper/lower bounds on likelihood. But we are putting on hold to favor synthesis for now.
- top_down.jl - (not used) old top down search implementation
- tracing.jl - (not used) utilities for tracing the old logprob/enumerate likelihood stuff







