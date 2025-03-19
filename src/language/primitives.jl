export ConsOp,
    NilOp,
    FlipOp,
    CarOp,
    CdrOp,
    IsEmptyOp,
    RandomDigitOp,
    EqualsOp,
    GreaterThanOp,
    RandomFloatOp,
    int_range,
    int_range_and_nan,
    AddOp,
    SubOp,
    prim_type,
    YOp,
    adt_mode
export prims_full, prims_minimal, RandomNatOp




struct FlipOp <: RandomPrimitive end
struct RandomNatOp <: RandomPrimitive end
struct RandomDigitOp <: RandomPrimitive end
struct FloatDivOp <: Primitive end
struct ConstructorEqOp <: Primitive end
struct MkIntOp <: Primitive end
struct IntDistEqOp <: Primitive end

Base.show(io::IO, e::FlipOp) = print(io, "flip")
Base.show(io::IO, e::RandomDigitOp) = print(io, "random_digit")
Base.show(io::IO, e::RandomNatOp) = print(io, "random_nat")
Base.show(io::IO, e::FloatDivOp) = print(io, "fdiv")
Base.show(io::IO, e::ConstructorEqOp) = print(io, "constructors_equal")
Base.show(io::IO, e::MkIntOp) = print(io, "mk_int")
Base.show(io::IO, e::IntDistEqOp) = print(io, "int_dist_eq")
const tflip = Arrow(PType[BaseType(:bool)], BaseType(:bool))
const tint = BaseType(:int)

prim_type(::FlipOp) = tflip
prim_type(::RandomDigitOp) = tint
prim_type(::RandomNatOp) = tint
prim_type(::MkIntOp) = tint
prim_type(::IntDistEqOp) = tbool

Base.:(==)(::RandomDigitOp, ::RandomDigitOp) = true
Base.:(==)(::RandomNatOp, ::RandomNatOp) = true
Base.:(==)(::FlipOp, ::FlipOp) = true
Base.:(==)(::FloatDivOp, ::FloatDivOp) = true
Base.:(==)(::ConstructorEqOp, ::ConstructorEqOp) = true
Base.:(==)(::MkIntOp, ::MkIntOp) = true
Base.:(==)(::IntDistEqOp, ::IntDistEqOp) = true

const primops::Dict{String, Tuple{Type, Int}} = Dict()

function prims_minimal()
    copy!(primops, primops_minimal)
end

const primops_minimal::Dict{String, Tuple{Type, Int}} = Dict([
    "flip" => (FlipOp, 1),
    "fdiv" => (FloatDivOp, 2),
    "random_digit" => (RandomDigitOp, 0),
    "random_nat" => (RandomNatOp, 0),
    "constructors_equal" => (ConstructorEqOp, 2),
    "mk_int" => (MkIntOp, 2),
    "int_dist_eq" => (IntDistEqOp, 2),
])
