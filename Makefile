bindings:
	cd src/RSDD/rsdd && cargo build --release --features=ffi
julia-instantiate:
	julia --project -e 'using Pkg; Pkg.instantiate()'
test:
	julia --project -e 'using Pluck; Pluck.run_examples()'
check:
ifdef FILES
	julia --project -e 'using Pluck; Pluck.run_check(ARGS)' -- $(FILES)
else
	julia --project -e 'using Pluck; Pluck.run_check()'
endif

NAME=latest
STABLE=stable
examples:
	mkdir -p out/examples
	julia --project -e 'using Pluck; Pluck.run_examples()' > out/examples/$(NAME).txt


diff:
	diff -u out/examples/$(STABLE).txt out/examples/$(NAME).txt
