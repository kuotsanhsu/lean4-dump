import C.Namespaces

/-!
# 6.2.5 Types

## 1
The meaning of a value stored in an object or returned by a function is determined by the *type* of the expression used to access it. (An identifier declared to be an object is the simplest such expression; the type is specified in the declaration of the identifier.) Types are partitioned into *object types* (types that describe objects) and *function types* (types that describe functions). At various points within a translation unit an object type may be *incomplete*) (lacking sufficient information to determine the size of objects of that type) or *complete* (having sufficient information).

## 2 Type `bool`
An object declared as type `bool` is large enough to store the values `false` and `true`.

## 3 Type `char`
An object declared as type `char` is large enough to store any member of the basic execution character set. If a member of the basic execution character set is stored in a `char` object, its value is guaranteed to be nonnegative. If any other character is stored in a `char` object, the resulting value is implementation-defined but shall be within the range of values that can be represented in that type.

## 4 Standard signed integer types
There are five *standard signed integer types*, designated as `signed char`, `short int`, `int`, `long int`, and `long long int`. (These and other types may be designated in several additional ways, as described in 6.7.3.)

## 5 Bit-precise signed integer types
A *bit-precise signed integer type* is designated as `_BitInt(N)` where $N$ is an integer constant expression that specifies the number of bits that are used to represent the type, including the sign bit. Each value of $N$ designates a distinct type.

## 6 Extended signed integer types
There may also be implementation-defined *extended signed integer types*. The standard signed integer types, bit-precise signed integer types, and extended signed integer types are collectively called *signed integer types*.

## 7
An object declared as type `signed char` occupies the same amount of storage as a "plain" `char` object. A "plain" `int` object has the natural size suggested by the architecture of the execution environment (large enough to contain any value in the range `INT_MIN` to `INT_MAX` as defined in the header `<limits.h>`).

## 8 Unsigned integer types
For each of the signed integer types, there is a *corresponding* (but different) *unsigned integer type* (designated with the keyword `unsigned`) that uses the same amount of storage (including sign information) and has the same alignment requirements. The type `bool` and the unsigned integer types that correspond to the standard signed integer types are the *standard unsigned integer types*. The unsigned integer types that correspond to the extended signed integer types are the *extended unsigned integer types*. In addition to the unsigned integer types that correspond to the bit-precise signed integer types there is the type `unsigned _BitInt(1)`, which uses one bit to represent the type. Collectively, `unsigned _BitInt(1)` and the unsigned integer types that correspond to the bit-precise signed integer types are the *bit-precise unsigned integer types*. The standard unsigned integer types, bit-precise unsigned integer types, and extended unsigned integer types are collectively called *unsigned integer types*.

## 9 Standard integer types, bit-precise integer types, extended integer types
The standard signed integer types and standard unsigned integer types are collectively called the *standard integer types*; the bit-precise signed integer types and bit-precise unsigned integer types are collectively called the *bit-precise integer types*; the extended signed integer types and extended unsigned integer types are collectively called the *extended integer types*.

## 10
For any two integer types with the same signedness and different integer conversion rank (see 6.3.1.1), the range of values of the type with smaller integer conversion rank is a subrange of the values of the other type.

## 11
The range of nonnegative values of a signed integer type is a subrange of the corresponding unsigned integer type, and the representation of the same value in each type is the same.34) The range of representable values for the unsigned type is $0$ to $2^N - 1$ (inclusive). A computation involving unsigned operands can never produce an overflow, because arithmetic for the unsigned type is performed modulo $2^N$.

## 12 Standard floating types
There are three *standard floating types*, designated as `float`, `double`, and `long double`. The set of values of the type `float` is a subset of the set of values of the type `double`; the set of values of the type `double` is a subset of the set of values of the type `long double`.

## 13 Decimal floating types
There are three *decimal floating types*, designated as `_Decimal32`, `_Decimal64`, and `_Decimal128`. Respectively, they have the ISO/IEC 60559 formats: decimal32, decimal64, and decimal128. (Decimal floating types are a conditional feature that implementations may not support; see 6.10.10.4.)

## 14 Real floating types
The standard floating types and the decimal floating types are collectively called the *real floating types*.

## 15 Complex types, floating types
There are three complex types, designated as `float _Complex`, `double _Complex`, and `long double _Complex`. (Complex types are a conditional feature that implementations may not support; see 6.10.10.4.) The real floating and complex types are collectively called the *floating types*.

## 16 Corresponding real type
For each floating type there is a *corresponding real type*, which is always a real floating type. For real floating types, it is the same type. For complex types, it is the type given by deleting the keyword `_Complex` from the type name.

## 17
Each complex type has the same representation and alignment requirements as an array type containing exactly two elements of the corresponding real type; the first element is equal to the real part, and the second element to the imaginary part, of the complex number.

## 18 Basic types
The type `char`, the signed and unsigned integer types, and the floating types are collectively called the *basic types*. The basic types are complete object types. Even if the implementation defines two or more basic types to have the same representation, they are nevertheless distinct types.

## 19 NOTE
An implementation can define new keywords that provide alternative ways to designate a basic (or any other) type; this does not violate the requirement that all basic types be different. Implementation-defined keywords have the form of an identifier reserved for any use as described in 7.1.3.

## 20 Character types
The three types `char`, `signed char`, and `unsigned char` are collectively called the *character types*. The implementation shall define `char` to have the same range, representation, and behavior as either `signed char` or `unsigned char`.

## 21 enumerated types
An *enumeration* comprises a set of named integer constant values. Each distinct enumeration
constitutes a different *enumerated type*.

## 22 Integer types, real types
The type `char`, the signed and unsigned integer types, and the enumerated types are collectively
called *integer types*. The integer and real floating types are collectively called *real types*.

## 23 Arithmetic types, type domains
Integer and floating types are collectively called *arithmetic types*. Each arithmetic type belongs to one *type domain*: the *real type domain* comprises the real types, the *complex type domain* comprises the complex types.

## 24 Type `void`
The `void` type comprises an empty set of values; it is an incomplete object type that cannot be
completed.

## 25 Derived types
Any number of *derived types* can be constructed from the object and function types, as follows:
- An *array type* describes a contiguously allocated nonempty set of objects with a particular member object type, called the *element type*. The element type shall be complete whenever the array type is specified. Array types are characterized by their element type and by the number of elements in the array. An array type is said to be derived from its element type, and if its element type is *T*, the array type is sometimes called "array of *T*". The construction of an array type from an element type is called "array type derivation".
- A *structure type* describes a sequentially allocated nonempty set of member objects (and, in certain circumstances, an incomplete array), each of which has an optionally specified name and possibly distinct type.
- A *union type* describes an overlapping nonempty set of member objects, each of which has an optionally specified name and possibly distinct type.
- A *function type* describes a function with specified return type. A function type is characterized by its return type and the number and types of its parameters. A function type is said to be derived from its return type, and if its return type is *T*, the function type is sometimes called "function returning *T*". The construction of a function type from a return type is called "function type derivation".
- A *pointer type* may be derived from a function type or an object type, called the *referenced type*. A pointer type describes an object whose value provides a reference to an entity of the referenced type. A pointer type derived from the referenced type *T* is sometimes called "pointer to *T*". The construction of a pointer type from a referenced type is called "pointer type derivation". A pointer type is a complete object type.
- An *atomic type* describes the type designated by the construct `_Atomic`(*type-name*). (Atomic types are a conditional feature that implementations may not support; see 6.10.10.4.)

These methods of constructing derived types can be applied recursively.

## 26 Type `nullptr_t, scalar types, aggregate types
Arithmetic types, pointer types, and the `nullptr_t` type are collectively called *scalar types*. Array and structure types are collectively called *aggregate types*.

## 27
An array type of unknown size is an incomplete type. It is completed, for an identifier of that type, by specifying the size in a later declaration (with internal or external linkage). A structure or union type of unknown content (as described in 6.7.3.4) is an incomplete type. It is completed, for all declarations of that type, by declaring the same structure or union tag with its defining content later in the same scope.

## 28 Known constant size
A complete type shall have a size that is less than or equal to `SIZE_MAX`. A type has *known constant size* if it is complete and is not a variable length array type.

## 29 Derived declarator types
Array, function, and pointer types are collectively called *derived declarator types*. A *declarator type derivation* from a type T is the construction of a derived declarator type from *T* by the application of an array-type, a function-type, or a pointer-type derivation to *T*.

## 30 Type categories
A type is characterized by its *type category*, which is either the outermost derivation of a derived type (as noted previously in this subclause in the construction of derived types), or the type itself if the type consists of no derived types.

## 31 Unqualified types, qualified types
Any type so far mentioned is an *unqualified type*. Each unqualified type has several *qualified versions* of its type, corresponding to the combinations of one, two, or all three of the `const`, `volatile`, and `restrict` qualifiers. The qualified or unqualified versions of a type are distinct types that belong to the same type category and have the same representation and alignment requirements. An array and its element type are always considered to be identically qualified. Any other derived type is not qualified by the qualifiers (if any) of the type from which it is derived.

## 32 Atomic types
Further, there is the `_Atomic` qualifier. The presence of the `_Atomic` qualifier designates an atomic type. The size, representation, and alignment of an atomic type may not be the same as those of the corresponding unqualified type. Therefore, this document explicitly uses the phrase "atomic, qualified, or unqualified type" whenever the atomic version of a type is permitted along with the other qualified versions of a type. The phrase "qualified or unqualified type", without specific mention of atomic, does not include the atomic types.

## 33 `void` pointers
A pointer to `void` shall have the same representation and alignment requirements as a pointer to a character type. Similarly, pointers to qualified or unqualified versions of compatible types shall have the same representation and alignment requirements. All pointers to structure types shall have the same representation and alignment requirements as each other. All pointers to union types shall have the same representation and alignment requirements as each other. Pointers to other types may not have the same representation or alignment requirements.

## 34 EXAMPLE 1
The type designated as "`float *`" has type "pointer to `float`". Its type category is pointer, not a floating type. The const-qualified version of this type is designated as "`float * const`" whereas the type designated as "`const float *`" is not a qualified type — its type is "pointer to const-qualified `float`" and is a pointer to a qualified type.

## 35 EXAMPLE 2
The type designated as "`struct tag (*[5])(float)`" has type "array of pointer to function returning `struct tag`". The array has length five and the function has a single parameter of type float. Its type category is array.

**Forward references:**  compatible type and composite type (6.2.7), declarations (6.7).
-/

inductive ArithmeticType
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

mutual

inductive IncompleteUnqualifiedType
  | struct (name : Identifier)
  | union (name : Identifier)
  | array (elementType : CompleteQualifiedType)

inductive CompleteUnqualifiedType
  | arith (type : ArithmeticType)
  | struct (name : Identifier) (values : Array (Identifier × CompleteQualifiedType))
  | union (name : Identifier) (values : Array (Identifier × CompleteQualifiedType))
  | array (elementType : CompleteQualifiedType) (size : Nat)
  | function (returnType : CompleteQualifiedType) (parameterTypes : Array CompleteQualifiedType)
  | pointer (referenceType : QualifiedType)

inductive CompleteQualifiedType
  | complete (type : CompleteUnqualifiedType) (const volatile restrict : Bool := false)
  | nullptr_t

inductive QualifiedType
  | ofComplete (type : CompleteQualifiedType)
  | incomplete (type : IncompleteUnqualifiedType) (const volatile restrict : Bool := false)
  | void

end

namespace QualifiedType

instance : Coe ArithmeticType CompleteUnqualifiedType where
  coe := .arith
instance : Coe CompleteUnqualifiedType CompleteQualifiedType where
  coe := .complete
instance : Coe CompleteQualifiedType QualifiedType where
  coe := ofComplete

export ArithmeticType (
  enum
  char
  /- signed integer types -/
  «signed char» «short int» int «long int» «long long int» _BitInt
  /- unsigned integer type -/
  bool
  «unsigned char» «unsigned short int» «unsigned int» «unsigned long int» «unsigned long long int»
  «unsigned _BitInt»
  /- floating types -/
  float double «long double»
  _Decimal32 _Decimal64 _Decimal128
  «float _Complex» «double _Complex» «long double _Complex»
)
example (name : Identifier) : QualifiedType := enum name #[]
example : QualifiedType := char
example : QualifiedType := «signed char»
example : QualifiedType := «short int»
example : QualifiedType := int
example : QualifiedType := «long int»
example : QualifiedType := «long long int»
example : QualifiedType := _BitInt 2
example : QualifiedType := _BitInt 7
example : QualifiedType := bool
example : QualifiedType := «unsigned char»
example : QualifiedType := «unsigned short int»
example : QualifiedType := «unsigned int»
example : QualifiedType := «unsigned long int»
example : QualifiedType := «unsigned long long int»
example : QualifiedType := «unsigned _BitInt» 1
example : QualifiedType := «unsigned _BitInt» 7
example : QualifiedType := float
example : QualifiedType := double
example : QualifiedType := «long double»
example : QualifiedType := _Decimal32
example : QualifiedType := _Decimal64
example : QualifiedType := _Decimal128
example : QualifiedType := «float _Complex»
example : QualifiedType := «double _Complex»
example : QualifiedType := «long double _Complex»
example (T : ArithmeticType) : QualifiedType := T

export CompleteUnqualifiedType (function pointer)
example (T : CompleteQualifiedType) : QualifiedType := function T #[]
example (T : CompleteQualifiedType) : QualifiedType := pointer T
example : QualifiedType := pointer void
example (T : CompleteUnqualifiedType) : QualifiedType := T

export CompleteQualifiedType (complete nullptr_t)
example (T : CompleteUnqualifiedType) : QualifiedType := complete T true true true
example : QualifiedType := nullptr_t

example (T : IncompleteUnqualifiedType) : QualifiedType := incomplete T true true true
example : QualifiedType := void

end QualifiedType

/-!
## Bibliography

- https://stackoverflow.com/questions/7147008/the-usage-of-anonymous-enums
-/
