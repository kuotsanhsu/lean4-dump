import Mathlib.Data.Set.Defs

class Geometry1 (α) where
  r : α → α → α → Prop
  -- axiom1 : ∃ a b : α, a ≠ b
  axiom2 {a b c} : r a b c → r c b a
  axiom3 {a b c} : r a b c → ¬r b c a
  axiom4 {a b c} : r a b c → a ≠ c
  axiom5 {a b} : a ≠ b → ∃ c, r a b c

class NEq {α} (a b : α) : Prop where
  neq : a ≠ b

namespace Geometry1
variable {α} [Geometry1 α]

-- Segment
-- Ray
def Line (a b : α) [NEq a b] := { x : α | r x a b ∧ r a x b ∧ r a b x }
def Collinear (a b c : α) [NEq a b] : Prop := r a b c ∨ r b c a ∨ r c a b
class Triangular (a b c : α) extends NEq a b : Prop where
  triangular : ¬Collinear a b c

end Geometry1

open Geometry1 in
class Geometry2 (α) extends Geometry1 α where
  axiom6 {a b c d : α} [NEq a b] [NEq c d] : Collinear a b c → Collinear a b d → Collinear c d a
  -- axiom6 {a b c d : α} [NEq a b] [NEq c d] : c ∈ Line a b → d ∈ Line a b → a ∈ Line c d
  -- axiom7 : ∃ a b c, ¬r a b c ∧ ¬r c b a ∧ ¬r b a c

class NEq3 {α} (a b c : α) extends NEq a b : Prop where
  -- neq₃ : a ≠ b
  neq₁ : b ≠ c
  neq₂ : c ≠ a

-- namespace NEq3
-- variable {α} {a b c : α} [self : NEq3 a b c]

-- instance (c : α) [NEq3 a b c] : NEq a b where neq := (self.neq₃ : a ≠ b)

-- end NEq3

namespace Geometry2
export Geometry1 (Line Collinear Triangular)
variable {α} [Geometry2 α]

structure PreTriangle where
  (v₁ v₂ v₃ : α)
  -- (ne₃ : NEq v₁ v₂) (ne₁ : NEq v₂ v₃) (ne₂ : NEq v₃ v₁)
  distinct : NEq3 v₁ v₂ v₃
  -- (h₁ : v₁ ∉ Line v₂ v₃) (h₂ : v₂ ∉ Line v₃ v₁) (h₃ : v₃ ∉ Line v₁ v₂)
  triangular : ¬Collinear v₁ v₂ v₃

end Geometry2

open Geometry2 in
class Geometry3 (α) extends Geometry2 α where
  axiom8 {a b c d e : α} [Triangular a b c] : r a b d → r b e c → ∃ f, r c f a ∧ r d e f
