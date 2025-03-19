bindings:
	cd src/RSDD/rsdd && cargo build --release --features=ffi
julia-instantiate:
	julia --project -e 'using Pkg; Pkg.instantiate()'