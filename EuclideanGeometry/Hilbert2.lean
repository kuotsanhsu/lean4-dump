-- import Mathlib.Data.Set.Defs

variable {α}

-- def Join (A B : α) := {l : Line // A ∈ l ∧ B ∈ l}
-- def Meet (l m : Line) := {A : Point // A ∈ l ∧ A ∈ m}
-- def Colinear (A B C : Point) := ∃ l : Line, A ∈ l ∧ B ∈ l ∧ C ∈ l
-- def Disjoint (A B C : Point) (l : Line) := A ∉ l ∧ B ∉ l ∧ C ∉ l

-- def I1 : Prop := ∀ A B : Point, A ≠ B → ∃ l : Join A B, ∀ m : self.Join A B, m = l
-- def I2 : Prop := ∀ l : Line, ∃ A ∈ l, ∃ B ∈ l, A ≠ B
-- def I3 : Prop := ∃ A B C : Point, ¬self.Colinear A B C
-- def Parallel (l m : Line) : Prop := l ≠ m → Meet l m → False
-- def P : Prop := ∀ A : Point, ∀ l : Line, Subsingleton {m : Line // A ∈ m ∧ Parallel l m}

class Straight {α} (r : (a b : α) → a ≠ b → Prop) : Prop where
  symm {a b : α} {ne : a ≠ b} : r a b ne → r b a ne.symm

/-- Ternary equivalence relation
* https://en.wikipedia.org/wiki/Ternary_equivalence_relation
* https://math.stackexchange.com/a/3191561
-/
class Collinear {α} (r : α → α → α → Prop) : Prop where
  symm {a b c : α} : r a b c → r b c a → r c b a
  refl {a b : α} : r a b b
  trans (a b c d : α) : a ≠ b → r a b c → r a b d → r b c d

namespace Collinear
variable {a b c d : α} {r : α → α → α → Prop} [self : Collinear r]

section symm
variable (rabc : r a b c) (rbca : r b c a)

example : r c b a := self.symm rabc rbca
example : r a c b := symm rbca _
example : r b a c := sorry
example : r c a b := sorry

end symm

theorem one : r a a a := self.refl

example : r b a b := Classical.byCases (fun h : a = b => h.rec one)
  fun h : a ≠ b => self.trans a b a b h _ _
example : r b b a :=

theorem two1 : r a a b := Classical.byCases (fun h : a = b => h.rec one)
  -- fun h : a ≠ b => self.trans b a a b h.symm self.refl _
  fun h : a ≠ b => self.trans a b _ _ h _ _
theorem two2 : r a b a := Classical.byCases (fun h : a = b => h.rec one)
  fun h : a ≠ b => self.trans b a b a h.symm _ self.refl
-- abb bba bab
theorem two3 : r b a a := self.refl

section three
variable (h : r a b c)

theorem perm1 : r a b c := sorry
theorem perm2 : r a c b := sorry
theorem perm3 : r b a c := sorry
theorem perm4 : r b c a := sorry
theorem perm5 : r c a b := sorry
theorem perm6 : r c b a := sorry

end three

end Collinear
