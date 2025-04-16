import Lean.Data.RBMap
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.NeZero

namespace Ring
variable {α} [ring : Ring α] [nontrivial : Nontrivial α]

theorem one_ne_zero (h : (1 : α) = 0) : False :=
  have ⟨x, y, (hxy : x ≠ y)⟩ := nontrivial.exists_pair_ne
    suffices ∀ x : α, x = 0 from hxy <| (this x).trans (this y).symm
    fun x =>
      calc x
        _ = x * 1 := ring.mul_one x |>.symm
        _ = x * 0 := congrArg _ h
        _ = 0 := ring.mul_zero x

instance : NeZero (1 : α) where
  out := one_ne_zero

end Ring

abbrev Poly α [CommRing α] := Lean.RBMap ℕ {x : α // x ≠ 0} instOrdNat.compare

namespace Poly
variable {α} [CommRing α] [Nontrivial α] [DecidableEq α]

def zero : Poly α := ∅

instance : Zero (Poly α) where
  zero := zero

def add (p q : Poly α) : Poly α :=
  p.fold (init := p) fun r i ⟨a, _⟩ =>
    if let some ⟨b, _⟩ := q.find? i then
      let c := a + b
      if hc : c = 0 then r.erase i else r.insert i ⟨c, hc⟩
    else
      r

instance : Add (Poly α) where
  add := add

def one : Poly α := zero.insert 0 ⟨1, one_ne_zero⟩

instance : One (Poly α) where
  one := one

def smul (x : α) (p : Poly α) : Poly α :=
  if x = 0 then p else p.fold (init := 0) fun r i a =>
    let c := x * a.val
    if hc : c = 0 then r else r.insert i ⟨c, hc⟩

instance : SMul α (Poly α) where
  smul := smul

def mul (p q : Poly α) : Poly α :=
  p.fold (init := 0) fun r i ⟨a, _⟩ =>
    if a = 0 then r else q.fold (init := r) fun r j ⟨b, _⟩ =>
      let k := i + j
      let x := a * b
      if let some c := r.find? k then
        let d := c + x
        if hd : d = 0 then r.erase k else r.insert k ⟨d, hd⟩
      else
        if hx : x = 0 then r else r.insert k ⟨x, hx⟩

instance : Mul (Poly α) where
  mul := mul

def eval (p : Poly α) (x : α) : α :=
  p.fold (init := 0) fun y i ⟨a, _⟩ => y + a * x ^ i

end Poly
