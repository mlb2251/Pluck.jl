bindings:
	cd src/RSDD/rsdd && cargo build --release --features=ffi
pull:
	cd src/RSDD/rsdd && git pull

m1-setup:
	julia --project -e 'using Pkg; Pkg.add(url="https://github.com/rtjoa/CUDD.jl.git", rev="m1compat")'

julia-instantiate:
	julia --project -e 'using Pkg; Pkg.instantiate()'