/-!
# Hilbert's Axioms

## Bibliography

- Wikipedia, *[Hilbert's axioms](https://en.wikipedia.org/wiki/Hilbert%27s_axioms)*
- David Hilbert, *[The Foundations of Geometry](https://www.gutenberg.org/files/17384/17384-pdf.pdf)*
- Robin Hartshorne, *[Geometry: Euclid and Beyond](https://link.springer.com/book/10.1007/978-0-387-22676-7)*
- Francis Borceux, *[An Axiomatic Approach to Geometry: Geometric Trilogy I](https://link.springer.com/book/10.1007/978-3-319-01730-3)*
- Ja1941, *[hilberts-axioms](https://github.com/Ja1941/hilberts-axioms/blob/master/src/incidence/basic.lean)*
- Euclid, *[Elements](http://aleph0.clarku.edu/~djoyce/elements/bookI/bookI.html)*

-/

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

namespace Incidence
variable {Point Line} [self : Incidence Point Line]

/-- Two distinct lines can have at most one point in common. -/
example {l m : Line} (hlm : l ≠ m) (A B : self.Meet l m) : A = B :=
  Classical.byContradiction fun hAB : A ≠ B =>
    suffices l = m from hlm this
    have ⟨⟨n, _⟩, h⟩ := self.i1 A.val B.val (hAB ∘ Subtype.ext)
    calc l
      _ = n := Subtype.ext_iff.mp <| h ⟨l, A.property.1, B.property.1⟩
      _ = m := Subtype.ext_iff.mp <| h ⟨m, A.property.2, B.property.2⟩ |>.symm

example (l : Line) : self.Parallel l l
  | (h : l ≠ l), _ => h rfl
example {l m : Line} : l ≠ m → self.Meet l m → ¬self.Parallel l m
  | hlm, P, h => h hlm P

end Incidence

class Playfair (Point Line) extends Incidence Point Line where
  p : toMembership.P

namespace Membership.Independence

/- Example 6.1.2 satsifies all -/
namespace Three

inductive Point | A | B | C
inductive Line | AB | BC | CA
local instance self : Membership Point Line where
  mem | .AB, .A | .AB, .B | .BC, .B | .BC, .C | .CA, .C | .CA, .A => True | _, _ => False

example : self.I1
  | .A, .B, _ | .B, .A, _ => ⟨⟨.AB, trivial, trivial⟩, fun | ⟨.AB, _⟩ => rfl⟩
  | .B, .C, _ | .C, .B, _ => ⟨⟨.BC, trivial, trivial⟩, fun | ⟨.BC, _⟩ => rfl⟩
  | .C, .A, _ | .A, .C, _ => ⟨⟨.CA, trivial, trivial⟩, fun | ⟨.CA, _⟩ => rfl⟩
example : self.I2
  | .AB => ⟨.A, trivial, .B, trivial, nofun⟩
  | .BC => ⟨.B, trivial, .C, trivial, nofun⟩
  | .CA => ⟨.C, trivial, .A, trivial, nofun⟩
example : self.I3 := ⟨.A, .B, .C, nofun⟩
example : self.P
  | .A, .AB => .intro fun
    | ⟨.AB, _⟩, ⟨.AB, _⟩ => rfl
    | ⟨.AB, _⟩, ⟨.CA, _, h⟩ | ⟨.CA, _, h⟩, _ => nomatch h nofun ⟨.A, trivial, trivial⟩
  | .A, .CA => .intro fun
    | ⟨.CA, _⟩, ⟨.CA, _⟩ => rfl
    | ⟨.CA, _⟩, ⟨.AB, _, h⟩ | ⟨.AB, _, h⟩, _ => nomatch h nofun ⟨.A, trivial, trivial⟩
  | .A, .BC => .intro fun
    | ⟨.AB, _⟩, ⟨.AB, _⟩ => rfl
    | ⟨.AB, _⟩, ⟨.CA, _, h⟩ | ⟨.CA, _, h⟩, _ => nomatch h nofun ⟨.C, trivial, trivial⟩
  | .B, .AB => .intro fun
    | ⟨.AB, _⟩, ⟨.AB, _⟩ => rfl
    | ⟨.AB, _⟩, ⟨.BC, _, h⟩ | ⟨.BC, _, h⟩, _ => nomatch h nofun ⟨.B, trivial, trivial⟩
  | .B, .BC => .intro fun
    | ⟨.BC, _⟩, ⟨.BC, _⟩ => rfl
    | ⟨.BC, _⟩, ⟨.AB, _, h⟩ | ⟨.AB, _, h⟩, _ => nomatch h nofun ⟨.B, trivial, trivial⟩
  | .B, .CA => .intro fun
    | ⟨.AB, _⟩, ⟨.AB, _⟩ => rfl
    | ⟨.AB, _⟩, ⟨.BC, _, h⟩ | ⟨.BC, _, h⟩, _ => nomatch h nofun ⟨.C, trivial, trivial⟩
  | .C, .AB => .intro fun
    | ⟨.CA, _⟩, ⟨.CA, _⟩ => rfl
    | ⟨.CA, _⟩, ⟨.BC, _, h⟩ | ⟨.BC, _, h⟩, _ => nomatch h nofun ⟨.B, trivial, trivial⟩
  | .C, .BC => .intro fun
    | ⟨.BC, _⟩, ⟨.BC, _⟩ => rfl
    | ⟨.BC, _⟩, ⟨.CA, _, h⟩ | ⟨.CA, _, h⟩, _ => nomatch h nofun ⟨.C, trivial, trivial⟩
  | .C, .CA => .intro fun
    | ⟨.CA, _⟩, ⟨.CA, _⟩ => rfl
    | ⟨.CA, _⟩, ⟨.BC, _, h⟩ | ⟨.BC, _, h⟩, _ => nomatch h nofun ⟨.C, trivial, trivial⟩

end Three

/- Example 6.1.3 does not satisfy P. -/
namespace Five

inductive Point | A | B | C | D | E
inductive Line | AB | BC | CD | DE | EA | AC | CE | EB | BD | DA
local instance self : Membership Point Line where
  mem
    | .AB, .A | .EA, .A | .AC, .A | .DA, .A
    | .AB, .B | .BC, .B | .EB, .B | .BD, .B
    | .BC, .C | .CD, .C | .AC, .C | .CE, .C
    | .CD, .D | .DE, .D | .BD, .D | .DA, .D
    | .DE, .E | .EA, .E | .CE, .E | .EB, .E => True
    | _, _ => False

example : self.I1
  | .A, .B, _ | .B, .A, _ => ⟨⟨.AB, trivial, trivial⟩, fun | ⟨.AB, _⟩ => rfl⟩
  | .B, .C, _ | .C, .B, _ => ⟨⟨.BC, trivial, trivial⟩, fun | ⟨.BC, _⟩ => rfl⟩
  | .C, .D, _ | .D, .C, _ => ⟨⟨.CD, trivial, trivial⟩, fun | ⟨.CD, _⟩ => rfl⟩
  | .D, .E, _ | .E, .D, _ => ⟨⟨.DE, trivial, trivial⟩, fun | ⟨.DE, _⟩ => rfl⟩
  | .E, .A, _ | .A, .E, _ => ⟨⟨.EA, trivial, trivial⟩, fun | ⟨.EA, _⟩ => rfl⟩
  | .A, .C, _ | .C, .A, _ => ⟨⟨.AC, trivial, trivial⟩, fun | ⟨.AC, _⟩ => rfl⟩
  | .C, .E, _ | .E, .C, _ => ⟨⟨.CE, trivial, trivial⟩, fun | ⟨.CE, _⟩ => rfl⟩
  | .E, .B, _ | .B, .E, _ => ⟨⟨.EB, trivial, trivial⟩, fun | ⟨.EB, _⟩ => rfl⟩
  | .B, .D, _ | .D, .B, _ => ⟨⟨.BD, trivial, trivial⟩, fun | ⟨.BD, _⟩ => rfl⟩
  | .D, .A, _ | .A, .D, _ => ⟨⟨.DA, trivial, trivial⟩, fun | ⟨.DA, _⟩ => rfl⟩
example : self.I2
  | .AB => ⟨.A, trivial, .B, trivial, nofun⟩
  | .BC => ⟨.B, trivial, .C, trivial, nofun⟩
  | .CD => ⟨.C, trivial, .D, trivial, nofun⟩
  | .DE => ⟨.D, trivial, .E, trivial, nofun⟩
  | .EA => ⟨.E, trivial, .A, trivial, nofun⟩
  | .AC => ⟨.A, trivial, .C, trivial, nofun⟩
  | .CE => ⟨.C, trivial, .E, trivial, nofun⟩
  | .EB => ⟨.E, trivial, .B, trivial, nofun⟩
  | .BD => ⟨.B, trivial, .D, trivial, nofun⟩
  | .DA => ⟨.D, trivial, .A, trivial, nofun⟩
example : self.I3 := ⟨.A, .B, .C, nofun⟩
example : ¬self.P | h => nomatch (h .A .DE).elim ⟨.AB, trivial, nofun⟩ ⟨.AC, trivial, nofun⟩

end Five

/- Model does not satisfy I3. -/
namespace Two

local instance self : Membership Bool Unit where
  mem _ _ := True

example : self.I1 | _, _, _ => ⟨⟨(), trivial, trivial⟩, fun _ => rfl⟩
example : self.I2 | _ => ⟨true, trivial, false, trivial, nofun⟩
example : ¬self.I3 | ⟨_, _, _, h⟩ => h ⟨(), trivial, trivial, trivial⟩
example : self.P | _, _ => .intro fun ⟨_, _⟩ _ => rfl

end Two

/- Model does not satisfy I2. -/
namespace Four

inductive Point | A | B | C
inductive Line | A | AB | BC | CA
local instance self : Membership Point Line where
  mem | .A, .A | .AB, .A | .AB, .B | .BC, .B | .BC, .C | .CA, .C | .CA, .A => True | _, _ => False

example : self.I1
  | .A, .B, _ | .B, .A, _ => ⟨⟨.AB, trivial, trivial⟩, fun | ⟨.AB, _⟩ => rfl⟩
  | .B, .C, _ | .C, .B, _ => ⟨⟨.BC, trivial, trivial⟩, fun | ⟨.BC, _⟩ => rfl⟩
  | .C, .A, _ | .A, .C, _ => ⟨⟨.CA, trivial, trivial⟩, fun | ⟨.CA, _⟩ => rfl⟩
example : ¬self.I2 := (nomatch · .A)
example : self.I3 := ⟨.A, .B, .C, nofun⟩
example : self.P
  | .A, .A => .intro fun
    | ⟨.A, _⟩, ⟨.A, _⟩ => rfl
    | ⟨.A, _⟩, ⟨.AB, _, h⟩ | ⟨.AB, _, h⟩, _
    | ⟨.A, _⟩, ⟨.CA, _, h⟩ | ⟨.CA, _, h⟩, _ => nomatch h nofun ⟨.A, trivial, trivial⟩
  | .A, .AB => .intro fun
    | ⟨.AB, _⟩, ⟨.AB, _⟩ => rfl
    | ⟨.AB, _⟩, ⟨.CA, _, h⟩ | ⟨.CA, _, h⟩, _
    | ⟨.AB, _⟩, ⟨.A, _, h⟩ | ⟨.A, _, h⟩, _ => nomatch h nofun ⟨.A, trivial, trivial⟩
  | .A, .CA => .intro fun
    | ⟨.CA, _⟩, ⟨.CA, _⟩ => rfl
    | ⟨.CA, _⟩, ⟨.AB, _, h⟩ | ⟨.AB, _, h⟩, _
    | ⟨.CA, _⟩, ⟨.A, _, h⟩ | ⟨.A, _, h⟩, _ => nomatch h nofun ⟨.A, trivial, trivial⟩
  | .A, .BC => .intro fun
    | ⟨.A, _⟩, ⟨.A, _⟩ => rfl
    | ⟨.A, _⟩, ⟨.AB, _, h⟩ | ⟨.AB, _, h⟩, _ => nomatch h nofun ⟨.B, trivial, trivial⟩
    | ⟨.A, _⟩, ⟨.CA, _, h⟩ | ⟨.CA, _, h⟩, _ => nomatch h nofun ⟨.C, trivial, trivial⟩
  | .B, .A => .intro fun
    | ⟨.BC, _⟩, ⟨.BC, _⟩ => rfl
    | ⟨.BC, _⟩, ⟨.AB, _, h⟩ | ⟨.AB, _, h⟩, _ => nomatch h nofun ⟨.A, trivial, trivial⟩
  | .B, .AB => .intro fun
    | ⟨.AB, _⟩, ⟨.AB, _⟩ => rfl
    | ⟨.AB, _⟩, ⟨.BC, _, h⟩ | ⟨.BC, _, h⟩, _ => nomatch h nofun ⟨.B, trivial, trivial⟩
  | .B, .BC => .intro fun
    | ⟨.BC, _⟩, ⟨.BC, _⟩ => rfl
    | ⟨.BC, _⟩, ⟨.AB, _, h⟩ | ⟨.AB, _, h⟩, _ => nomatch h nofun ⟨.B, trivial, trivial⟩
  | .B, .CA => .intro fun
    | ⟨.AB, _⟩, ⟨.AB, _⟩ => rfl
    | ⟨.AB, _⟩, ⟨.BC, _, h⟩ | ⟨.BC, _, h⟩, _ => nomatch h nofun ⟨.C, trivial, trivial⟩
  | .C, .A => .intro fun
    | ⟨.BC, _⟩, ⟨.BC, _⟩ => rfl
    | ⟨.BC, _⟩, ⟨.CA, _, h⟩ | ⟨.CA, _, h⟩, _ => nomatch h nofun ⟨.A, trivial, trivial⟩
  | .C, .AB => .intro fun
    | ⟨.CA, _⟩, ⟨.CA, _⟩ => rfl
    | ⟨.CA, _⟩, ⟨.BC, _, h⟩ | ⟨.BC, _, h⟩, _ => nomatch h nofun ⟨.B, trivial, trivial⟩
  | .C, .BC => .intro fun
    | ⟨.BC, _⟩, ⟨.BC, _⟩ => rfl
    | ⟨.BC, _⟩, ⟨.CA, _, h⟩ | ⟨.CA, _, h⟩, _ => nomatch h nofun ⟨.C, trivial, trivial⟩
  | .C, .CA => .intro fun
    | ⟨.CA, _⟩, ⟨.CA, _⟩ => rfl
    | ⟨.CA, _⟩, ⟨.BC, _, h⟩ | ⟨.BC, _, h⟩, _ => nomatch h nofun ⟨.C, trivial, trivial⟩

end Four

/- Model does not satisfy I1. -/
namespace Discrete

local instance self : Membership (Fin 3) Empty where
  mem _ _ := False

example : ¬self.I1 := (nomatch · 0 1 nofun)
example : self.I2 := nofun
example : self.I3 := ⟨0, 1, 2, nofun⟩
example : self.P := nofun

end Discrete

end Membership.Independence

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

end

class Betweenness (Point Line) extends Incidence Point Line where
  /-- `between A B C` denotes that `B` is between `A` and `C`. -/
  between (A B C : Point) : Prop
  b1 A B C : between A B C → toIncidence.Colinear A B C ∧ between C B A
  b2 A B : A ≠ B → ∃ C, between A B C
  b3 A B C : Distinct A B C → toIncidence.Colinear A B C → Exactly1 between A B C
  /-- Pasch's axiom. -/
  b4 A B C l : ¬toIncidence.Colinear A B C → ¬toIncidence.Disjoint A B C l →
    (∃ D ∈ l, between A D B) →
    (∃ P ∈ l, between A P C ∨ between B P C) ∧ ∀ P ∈ l, ∀ Q ∈ l, ¬(between A P C ∧ between B Q C)
