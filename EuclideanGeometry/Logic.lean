namespace Membership
variable {Point Line} [self : Membership Point Line]

def Join (A B : Point) := {l : Line // A ∈ l ∧ B ∈ l}
def Meet (l m : Line) := {A : Point // A ∈ l ∧ A ∈ m}
def Colinear (A B C : Point) := ∃ l : Line, A ∈ l ∧ B ∈ l ∧ C ∈ l
def Disjoint (A B C : Point) (l : Line) := A ∉ l ∧ B ∉ l ∧ C ∉ l

def I1 : Prop := ∀ A B : Point, A ≠ B → ∃ l : Join A B, ∀ m : self.Join A B, m = l
def I2 : Prop := ∀ l : Line, ∃ A ∈ l, ∃ B ∈ l, A ≠ B
def I3 : Prop := ∃ A B C : Point, ¬self.Colinear A B C
def Parallel (l m : Line) : Prop := l ≠ m → Meet l m → False
def P : Prop := ∀ A : Point, ∀ l : Line, Subsingleton {m : Line // A ∈ m ∧ Parallel l m}

end Membership

class Incidence (Point Line) extends Membership Point Line where
  i1 : toMembership.I1
  i2 : toMembership.I2
  i3 : toMembership.I3

section
variable {α} (p : α → α → α → Prop) (a b c : α)

def Distinct := a ≠ b ∧ b ≠ c ∧ c ≠ a
def AtLeast1 := p a b c ∨ p b c a ∨ p c a b
def AtMost1 := ¬(p a b c ∧ p b c a) ∧ ¬(p b c a ∧ p c a b) ∧ ¬(p c a b ∧ p a b c)
def Exactly1 := AtLeast1 p a b c ∧ AtMost1 p a b c
-- def Exactly1 :=
--   p a b c ∧ ¬p b c a ∧ ¬p c a b ∨
--   ¬p a b c ∧ p b c a ∧ ¬p c a b ∨
--   ¬p a b c ∧ ¬p b c a ∧ p c a b
def EitherOr (p q : Prop) := p ∧ ¬q ∨ ¬p ∧ q -- (p ∨ q) ∧ ¬(p ∧ q)

end

class Betweenness (Point Line) extends Incidence Point Line where
  /-- `between A B C` denotes that `B` is between `A` and `C`. -/
  between (A B C : Point) : Prop
  b1 A B C : between A B C → toIncidence.Colinear A B C ∧ between C B A
  b2 A B : A ≠ B → ∃ C, between A B C
  b3 A B C : Distinct A B C → toIncidence.Colinear A B C → Exactly1 between A B C
  /-- Pasch's axiom. -/
  b4 A B C l : ¬toIncidence.Colinear A B C → ¬toIncidence.Disjoint A B C l →
    (∃ D ∈ l, between A D B) → EitherOr (∃ P ∈ l, between A P C) (∃ P ∈ l, between B P C)
