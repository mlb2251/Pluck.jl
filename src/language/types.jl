
const type_of_constructor = Dict{Symbol,Symbol}()
const constructors_of_type = Dict{Symbol,Vector{Symbol}}()
const args_of_constructor = Dict{Symbol,Vector{Symbol}}()

function define_type!(type::Symbol, constructors::Dict{Symbol,Vector{Symbol}})
    # haskey(constructors_of_type, type) && @warn "type $type already defined"
    constructors_of_type[type] = Symbol[]
    for (constructor, args) in constructors
        # haskey(type_of_constructor, constructor) && @warn "while defining $type: constructor $constructor already defined for another type $(type_of_constructor[constructor])"
        type_of_constructor[constructor] = type
        args_of_constructor[constructor] = args
        push!(constructors_of_type[type], constructor)
    end
    nothing
end

define_type!(:nat, Dict(:S => Symbol[:nat], :O => Symbol[]))
define_type!(:list, Dict(:Nil => Symbol[], :Cons => Symbol[:nat, :list]))
define_type!(:snoclist, Dict(:SNil => Symbol[], :Snoc => Symbol[:snoclist, :nat]))
define_type!(:bool, Dict(:True => Symbol[], :False => Symbol[]))
define_type!(:unit, Dict(:Unit => Symbol[]))

