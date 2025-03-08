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

abbrev Poly α [Zero α] := Lean.RBMap ℕ {x : α // x ≠ 0} instOrdNat.compare

namespace Poly
variable {α}

section
variable [Zero α]

def zero  : Poly α := ∅

instance : Zero (Poly α) where
  zero := zero

end

section
variable [AddZeroClass α] [DecidableEq α]

def add (p q : Poly α) : Poly α :=
  p.fold (init := p) fun r i a =>
    if let some b := q.find? i then
      let c := a.val + b.val
      if hc : c = 0 then
        r.erase i
      else
        r.insert i ⟨c, hc⟩
    else
      r

instance : Add (Poly α) where
  add := add

end

section
variable [Ring α] [Nontrivial α]

def one : Poly α := zero.insert 0 ⟨1, one_ne_zero⟩

variable [DecidableEq α]

def smul (a : α) (p : Poly α) : Poly α :=
  if a = 0 then
    p
  else
    p.fold (init := 0) fun q i b =>
      let c := a * b.val
      if hc : c = 0 then
        q
      else
        q.insert i ⟨c, hc⟩

instance : SMul α (Poly α) where
  smul := smul

def mul (p q : Poly α) : Poly α :=
  p.fold (init := 0) fun r i ⟨a, _⟩ =>
    if a = 0 then
      r
    else
      q.fold (init := r) fun r j ⟨b, _⟩ =>
        let k := i + j
        let x := a * b
        if let some c := r.find? k then
          let d := c + x
          if hd : d = 0 then
            r.erase k
          else
            r.insert k ⟨d, hd⟩
        else
          if hx : x = 0 then
            r
          else
            r.insert k ⟨x, hx⟩

end

end Poly
