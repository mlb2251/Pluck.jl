bindings:
	cd src/RSDD/rsdd && cargo build --release --features=ffi
julia-instantiate:
	julia --project -e 'using Pkg; Pkg.instantiate()'
test:
	julia --project -e 'using Pluck; Pluck.run_examples(); Pluck.deriv_tests()'