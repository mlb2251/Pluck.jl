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
    adt_mode,
    GetConfig
export prims_full, prims_minimal, RandomNatOp




struct FlipOp <: RandomPrimitive end
struct GetConfig <: Primitive end
struct RandomNatOp <: RandomPrimitive end
struct RandomDigitOp <: RandomPrimitive end
struct FloatDivOp <: Primitive end
struct FloatMulOp <: Primitive end
struct FloatAddOp <: Primitive end
struct FloatSubOp <: Primitive end
# struct FloatRoundOp <: Primitive end
struct FloatPowOp <: Primitive end
struct FloatLessOp <: Primitive end
struct FloatCosOp <: Primitive end
struct FloatSinOp <: Primitive end
struct ConstructorEqOp <: Primitive end
struct ForceOp <: Primitive end

Base.show(io::IO, e::FlipOp) = print(io, "flip")
Base.show(io::IO, e::RandomDigitOp) = print(io, "random_digit")
Base.show(io::IO, e::RandomNatOp) = print(io, "random_nat")
Base.show(io::IO, e::FloatDivOp) = print(io, "fdiv")
Base.show(io::IO, e::FloatMulOp) = print(io, "fmul")
Base.show(io::IO, e::FloatAddOp) = print(io, "fadd")
Base.show(io::IO, e::FloatSubOp) = print(io, "fsub")
# Base.show(io::IO, e::FloatRoundOp) = print(io, "fround")
Base.show(io::IO, e::FloatPowOp) = print(io, "fpow")
Base.show(io::IO, e::FloatLessOp) = print(io, "fless")
Base.show(io::IO, e::FloatCosOp) = print(io, "fcos")
Base.show(io::IO, e::FloatSinOp) = print(io, "fsin")
Base.show(io::IO, e::ConstructorEqOp) = print(io, "constructors_equal")
Base.show(io::IO, e::GetConfig) = print(io, "get_config")
Base.show(io::IO, e::ForceOp) = print(io, "force")
const tflip = Arrow(PType[BaseType(:bool)], BaseType(:bool))
const tint = BaseType(:int)
const tfloat = BaseType(:float)

prim_type(::FlipOp) = tflip
prim_type(::RandomDigitOp) = tint
prim_type(::RandomNatOp) = tint
prim_type(::GetConfig) = tint
prim_type(::FloatDivOp) = Arrow(PType[tfloat, tfloat], tfloat)
prim_type(::FloatMulOp) = Arrow(PType[tfloat, tfloat], tfloat)
prim_type(::FloatAddOp) = Arrow(PType[tfloat, tfloat], tfloat)
prim_type(::FloatSubOp) = Arrow(PType[tfloat, tfloat], tfloat)
# prim_type(::FloatRoundOp) = Arrow(PType[tfloat], tint)
prim_type(::FloatPowOp) = Arrow(PType[tfloat, tfloat], tfloat)
prim_type(::FloatLessOp) = Arrow(PType[tfloat, tfloat], tbool)
prim_type(::FloatCosOp) = Arrow(PType[tfloat], tfloat)
prim_type(::FloatSinOp) = Arrow(PType[tfloat], tfloat)
Base.:(==)(::RandomDigitOp, ::RandomDigitOp) = true
Base.:(==)(::RandomNatOp, ::RandomNatOp) = true
Base.:(==)(::FlipOp, ::FlipOp) = true
Base.:(==)(::FloatDivOp, ::FloatDivOp) = true
Base.:(==)(::FloatMulOp, ::FloatMulOp) = true
Base.:(==)(::FloatAddOp, ::FloatAddOp) = true
Base.:(==)(::FloatSubOp, ::FloatSubOp) = true
# Base.:(==)(::FloatRoundOp, ::FloatRoundOp) = true
Base.:(==)(::FloatPowOp, ::FloatPowOp) = true
Base.:(==)(::ConstructorEqOp, ::ConstructorEqOp) = true
Base.:(==)(::GetConfig, ::GetConfig) = true
Base.:(==)(::FloatLessOp, ::FloatLessOp) = true
Base.:(==)(::FloatCosOp, ::FloatCosOp) = true
Base.:(==)(::FloatSinOp, ::FloatSinOp) = true
Base.:(==)(::ForceOp, ::ForceOp) = true
const primops::Dict{String, Tuple{Type, Int}} = Dict()

function prims_minimal()
    copy!(primops, primops_minimal)
end

const primops_minimal::Dict{String, Tuple{Type, Int}} = Dict([
    "flip" => (FlipOp, 1),
    "fdiv" => (FloatDivOp, 2),
    "fmul" => (FloatMulOp, 2),
    "fadd" => (FloatAddOp, 2),
    "fsub" => (FloatSubOp, 2),
    # "fround" => (FloatRoundOp, 1),
    "fpow" => (FloatPowOp, 2),
    "fless" => (FloatLessOp, 2),
    "fcos" => (FloatCosOp, 1),
    "fsin" => (FloatSinOp, 1),
    "get_config" => (GetConfig, 1),
    "random_digit" => (RandomDigitOp, 0),
    "random_nat" => (RandomNatOp, 0),
    "constructors_equal" => (ConstructorEqOp, 2),
    "force" => (ForceOp, 1),
])
