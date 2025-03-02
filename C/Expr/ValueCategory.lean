import C.Types

/-!
https://en.cppreference.com/w/c/language/value_category

# 6.3.2 Other operands

## 6.3.2.1 Lvalues, arrays, and function designators

An *lvalue* is an expression (with an object type other than `void`) that potentially designates an object; if an lvalue does not designate an object when it is evaluated, **the behavior is undefined**. When an object is said to have a particular type, the type is specified by the lvalue used to designate the object. A *modifiable lvalue* is an lvalue that does not have array type, does not have an incomplete type, does not have a const-qualified type, and if it is a structure or union, does not have any member (including, recursively, any member or element of all contained aggregates or unions) with a const-qualified type.

Except when it is the operand of the sizeof operator, or the typeof operators, the unary & operator, the ++ operator, the-- operator, or the left operand of the. operator or an assignment operator, an lvalue that does not have array type is converted to the value stored in the designated object (and is no longer an lvalue); this is called lvalue conversion. If the lvalue has qualified type, the value has the unqualified version of the type of the lvalue; additionally, if the lvalue has atomic type, the value has the non-atomic version of the type of the lvalue; otherwise, the value has the type of the lvalue. If the lvalue has an incomplete type and does not have array type, the behavior is undefined. If the lvalue designates an object of automatic storage duration that could have been declared with the register storage class (never had its address taken), and that object is uninitialized (not declared with an initializer and no assignment to it has been performed prior to use), the behavior is undefined.

Except when it is the operand of the sizeof operator, or typeof operators, or the unary & operator, or is a string literal used to initialize an array, an expression that has type "array of type" is converted to an expression with type "pointer to type" that points to the initial element of the array object and is not an lvalue. If the array object has register storage class, the behavior is undefined.

A function designator is an expression that has function type. Except when it is the operand of the sizeof operator,56) a typeof operator, or the unary & operator, a function designator with type "function returning type" is converted to an expression that has type "pointer to function returning type".

**Forward references:**  address and indirection operators (6.5.4.2), assignment operators (6.5.17),
common definitions <stddef.h> (7.21), initialization (6.7.11), postfix increment and decrement
operators (6.5.3.5), prefix increment and decrement operators (6.5.4.1), the sizeof and alignof
operators (6.5.4.4), structure and union members (6.5.3.4).
-/
