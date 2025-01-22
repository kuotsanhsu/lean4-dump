import Mathlib.Data.Fin.VecNotation

#check BitVec.instIntCast
#check decidableGetElem?
#check Matrix.vecCons
#check tacticGet_elem_tactic_trivial

/-- Notation for splitting bit vectors. `x#[m, n, k]`  -/
syntax:max term noWs "#[" withoutPosition(term,+) "]" : term
macro_rules
  | `($x#[$ns:term,*, $m:term]) => do
    let rec genProd (ns : List Lean.Term) : Lean.MacroM (Lean.Term × Lean.Term) := do
      match ns with
      | [] => return ⟨← `(BitVec.extractLsb' 0 $m $x), m⟩
      | n::ns =>
        let ⟨xs, sum⟩ ← genProd ns
        return ⟨← `(Prod.mk (BitVec.extractLsb' $sum $n $x) $xs), ← `($n + $sum)⟩
    return (← genProd ns.getElems.toList).1
  | `($x#[$n:term]) => `(($x : BitVec $n))

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
