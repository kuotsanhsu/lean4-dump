import Mathlib.Data.Fin.VecNotation

#check BitVec.instIntCast
#check decidableGetElem?
#check Matrix.vecCons
#check tacticGet_elem_tactic_trivial
#check Lean.RArray

/-
https://github.com/leanprover/lean4-nightly/commit/f6c5aed7ef6758f8357d5cee9c509ebc64c4e45a#diff-b4b5e504e6b8f2b07aa8846220cc5721760a789c37ddf9a802b8c9d9a31542b9R6
-/

/-- Notation for splitting bit vectors. `x#[m, n, k]`  -/
syntax:max term noWs "#[" withoutPosition(term,+) "]" : term
macro_rules
  | `($x#[$ns:term,*, $m:term]) =>
    let rec genProd : List Lean.Term → Lean.MacroM (Lean.Term × Lean.Term)
      | [] => return ⟨← ``(BitVec.extractLsb' 0 $m $x), m⟩
      | n::ns => do
        let ⟨xs, sum⟩ ← genProd ns
        return ⟨← ``(Prod.mk (BitVec.extractLsb' $sum $n $x) $xs), ← `($n + $sum)⟩
    return (← genProd ns.getElems.toList).1
  | `($x#[$n:term]) => ``(($x : BitVec $n))

#check_failure (0#7)#[1]
#check_failure (0#7)#[10]
-- #check_failure (rfl : (0#7)#[5 + 4]'_ = 0#7)
-- example (a b : Nat) : (0#(a+b))#[7]'(show a + b = 7 from sorry) = 0#7 := rfl
example : (0#7)#[7] = 0#7 := rfl
example : (0#7)#[7] = (0#7) := rfl
example : (0#7)#[3, 4] = (0#3, 0#4) := rfl
#check (0#7)#[3, 2, 3]  -- FIXME: should fail
example : (0#7)#[3, 2, 2] = (0#3, 0#2, 0#2) := rfl
example : (1#7)#[3, 2, 2] = (0#3, 0#2, 1#2) := rfl
example : (0b001_01_01#7)#[3, 2, 2] = (1#3, 1#2, 1#2) := rfl
example : (1#7)#[3, 2, 2] =
    ((1#7).extractLsb' 4 3, (1#7).extractLsb' 2 2, (1#7).extractLsb' 0 2) :=
  rfl

-- def extractLsb' (start len : Nat) (x : BitVec n) : BitVec len := .ofNat _ (x.toNat >>> start)
#check Int.ofNat
inductive BitField : Nat → Type
  | ofBitVec {w} : BitVec w → BitField w
  -- | append {w v} : BitField w → BitField v → BitField (w + v)
  | cons {v w} : BitField v → BitVec w → BitField (v + w)

namespace BitField
variable {u v w}

instance : Coe (BitVec w) (BitField w) where
  coe := ofBitVec

def mk₃ : BitVec u → BitVec v → BitVec w → BitField (u + v + w)
  | x, y, z => .cons (.cons x y) z

def toBitVec {w} : BitField w → BitVec w
  | ofBitVec x => x
  | cons xs x => xs.toBitVec ++ x

def split (xs : BitField (v + w)) : BitVec v × BitVec w :=
  ⟨xs.toBitVec.extractLsb' w v, xs.toBitVec.extractLsb' 0 w⟩

end BitField

/-
* https://leanprover-community.github.io/lean4-metaprogramming-book/main/06_macros.html
* https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Lean.Macro.throwUnsupported
-/

abbrev BitVec.extract {w} (x : BitVec w) (start len : Nat) (_h : start + len ≤ w) : BitVec len :=
  x.extractLsb' start len

macro:max x:term noWs kt:"%[" ns:term,* "]" : term =>
  match ns.getElems.toList with
  | [] => Lean.Macro.throwErrorAt kt "must have at least 1 element"
  | m::ns =>
  let rec genProd : List Lean.Term → Lean.MacroM (Lean.Term × Lean.Term)
    | [] => return ⟨← ``(BitVec.extractLsb' 0 $m $x), m⟩
    | n::ns => do
      let ⟨xs, sum⟩ ← genProd ns
      return ⟨← ``(Prod.mk (BitVec.extractLsb' $sum $n $x) $xs), ← `($n + $sum)⟩
  return x
  -- return (← genProd ns.getElems.toList).1

#check_failure (0#7)%[]
#check (0#7)%[6]
example : (0#7)%[7] = 0#7 := rfl
example : (0#7)%[7] = (0#7) := rfl
-- example : (0#7)%[3, 4] = (0#3, 0#4) := rfl
#check (0#7)%[3, 2, 3]  -- FIXME: should fail
