bindings:
	cd src/RSDD/rsdd && cargo build --release --features=ffi
julia-instantiate:
	julia --project -e 'using Pkg; Pkg.instantiate()'
test:
	julia --project -e 'using Pluck; Pluck.run_examples()'
# Settings for `make check`:
#   FILE       .pluck file(s) to check
#   ALLOW      only run queries whose name contains this substring
#   ONCE       warmstart + single trial (skip repeated timing)
#   WARMSTART  run a warmup trial before timing (avoids measuring JIT)
#   BEFORE     baseline results to diff against (relative to check-results/)
FILE=programs/all.pluck
ALLOW=
ONCE=false
WARMSTART=true
BEFORE=prev.json
check: generate-bayes-nets
	julia --project -e 'using Pluck; Pluck.run_check(ARGS; baseline="$(BEFORE)", allow="$(ALLOW)", once=$(ONCE), warmstart=$(WARMSTART))' -- $(FILE)
check-table1:
	$(MAKE) check FILE=programs/table1/table1.pluck

generate-bayes-nets:
	julia --project -e 'include("programs/table1/1-bayesian-networks/codegen/bayes-net-codegen.jl"); generate_benchmarks()'

AFTER=latest.json
diff:
	julia --project -e 'using Pluck; Pluck.diff_check_results(ARGS[1], ARGS[2])' -- $(BEFORE) $(AFTER)

NAME=latest
STABLE=stable
examples:
	mkdir -p out/examples
	julia --project -e 'using Pluck; Pluck.run_examples()' > out/examples/$(NAME).txt

examples-diff:
	diff -u out/examples/$(STABLE).txt out/examples/$(NAME).txt
