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

class inductive Straight (α) : Prop where
  | mk (A B : α) : A ≠ B → Straight α
