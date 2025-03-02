import C.Representation

/-!
# 6.3 Conversions

Several operators convert operand values from one type to another automatically. This subclause specifies the result required from such an *implicit conversion•, as well as those that result from a cast operation (an *explicit conversion&). The list in 6.3.1.8 summarizes the conversions performed by most ordinary operators; it is supplemented as required by the discussion of each operator in 6.5.1.

Unless explicitly stated otherwise, conversion of an operand value to a compatible type causes no change to the value or the representation.

**Forward references:**  cast operators (6.5.5).

## 6.3.1 Arithmetic operands

### 6.3.1.1 Boolean, characters, and integers

Every integer type has an *integer conversion rank* defined as follows:
- No two signed integer types shall have the same rank, even if they have the same representation.
- The rank of a signed integer type shall be greater than the rank of any signed integer type with less precision.
- The rank of `long long int` shall be greater than the rank of `long int`, which shall be greater than the rank of `int`, which shall be greater than the rank of `short int`, which shall be greater than the rank of `signed char`.
- The rank of a bit-precise signed integer type shall be greater than the rank of any standard integer type with less width or any bit-precise integer type with less width.
- The rank of any unsigned integer type shall equal the rank of the corresponding signed integer type, if any.
- The rank of any standard integer type shall be greater than the rank of any extended integer type with the same width or bit-precise integer type with the same width.
- The rank of any bit-precise integer type relative to an extended integer type of the same width is **implementation-defined**.
- The rank of `char` shall equal the rank of `signed char` and `unsigned char`.
- The rank of `bool` shall be less than the rank of all other standard integer types.
- The rank of any enumerated type shall equal the rank of the compatible integer type (see 6.7.3.3).
- The rank of any extended signed integer type relative to another extended signed integer type with the same precision is **implementation-defined**, but still subject to the other rules for determining the integer conversion rank.
- For all integer types `T1`, `T2`, and `T3`, if `T1` has greater rank than `T2` and `T2` has greater rank than `T3`, then `T1` has greater rank than `T3`.
-/

namespace ArithmeticType

def width : ArithmeticType → Nat := sorry

/-- `RankGt U T` denotes that the rank of type `U` is greater than that of type `T`. -/
inductive RankGt : ArithmeticType → ArithmeticType → Prop
  | longlong_gt_long : RankGt «long long int» «long int»
  | long_gt_int : RankGt «long int» int
  | int_gt_short : RankGt int «short int»
  | short_gt_schar : RankGt «short int» «signed char»
  | bitint_gt {N T} (ge2 : N ≥ 2) : N > T.width → RankGt (_BitInt N ge2) T

/-- `RankEq U T` denotes that the rank of type `U` is equal to that of type `T`. -/
inductive RankEq : ArithmeticType → ArithmeticType → Prop
  | char : RankEq «signed char» «unsigned char»
  | short : RankEq «short int» «unsigned short int»
  | int : RankEq int «unsigned int»
  | long : RankEq «long int» «unsigned long int»
  | longlong : RankEq «long long int» «unsigned long long int»
  | bitint {N} (ge2 : N ≥ 2) :
    RankEq (_BitInt N ge2) («unsigned _BitInt» N (Nat.lt_trans .refl ge2))

/-!
| enum (name : Identifier) (values : Array (Identifier × Nat))
/- basic types -/
| char
/- signed integer types -/
  /- standard signed integer types -/
  | «signed char»
  | «short int»
  | int
  | «long int»
  | «long long int»
  /- bit-precise signed integer types -/
  | _BitInt (N : Nat) (ge2 : N ≥ 2 := by decide)
  /- extended signed integer types -/
/- unsigned integer type -/
  /- standard unsigned integer types -/
  | bool
  | «unsigned char»
  | «unsigned short int»
  | «unsigned int»
  | «unsigned long int»
  | «unsigned long long int»
  /- bit-precise unsigned integer types -/
  | «unsigned _BitInt» (N : Nat) (ge1 : N ≥ 1 := by decide)
  /- extended unsigned integer types -/
/- floating types -/
  /- real floating types -/
    /- standard floating types -/
    | float
    | double
    | «long double»
    /- decimal floating types -/
    | _Decimal32
    | _Decimal64
    | _Decimal128
  /- complex types -/
  | «float _Complex»
  | «double _Complex»
  | «long double _Complex»
-/

end ArithmeticType
