import Mathlib.Data.Set.Defs
import Mathlib.Logic.Nontrivial.Defs

class NEq {α} (a b : α) : Prop where
  neq : a ≠ b

namespace NEq
variable {α} {a b : α} [NEq a b]

instance : NEq b a where
  neq := neq.symm

end NEq

class Between (α) where
  between (a b c : α) [NEq a c] : Prop

namespace Between
variable {α} [Between α]

notation:40 a "#" b:50 "#" c:40 => Between.between a b c

def Segment (a b : α) [NEq a b] := { x : α | a#x#b }
def Ray (a b : α) [NEq a b] := { x : α | a#x#b ∨ a ≠ x ∧ ∀ [NEq a x], a#b#x }
def Line (a b : α) [NEq a b] := { x : α | (∀ [NEq x b], x#a#b) ∨ a#x#b ∨ ∀ [NEq a x], a#b#x }
def Collinear (a b c : α) : Prop := ∃ x y, x ≠ y ∧ ∀ [NEq x y], a ∈ Line x y ∧ b ∈ Line x y ∧ c ∈ Line x y
def Triangular (a b c : α) : Prop := ¬Collinear a b c

-- structure Line where

end Between

open Between in
class Geometry (α) extends Between α, Nontrivial α where
  axiom2 {a b c : α} [NEq a c] : a#b#c → c#b#a
  axiom3 {a b c : α} [NEq a c] : a#b#c → ¬a#c#b
  axiom4 {a b c : α} : a#b#c → a ≠ c
  axiom5 {a b : α} : a ≠ b → ∃ c, a#b#c
  axiom6 {a b c d : α} : a ≠ b → c ≠ d → Collinear a b c → Collinear a b d → Collinear c d a
  axiom7 : ∃ a b c : α, Triangular a b c
  axiom8 {a b c d e : α} : Triangular a b c → a#b#d → b#e#c → ∃ f, c#f#a ∧ d#e#f

namespace Geometry
export Between (Collinear)
variable {α} [Geometry α] {a b c : α}

theorem between_fst [NEq a b] : a#a#b := sorry
theorem between_snd [NEq a b] : a#b#b := sorry

theorem collinear_self : Collinear a a a := sorry
theorem collinear_two : Collinear a a b := sorry

end Geometry
