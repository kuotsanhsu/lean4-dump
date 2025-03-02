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

abbrev ExistsUnique {α} (p : α → Prop) := ∃ a : α, p a ∧ ∀ b : α, p b → a = b

open Lean TSyntax.Compat in
macro "∃!" xs:explicitBinders ", " b:term : term => expandExplicitBinders ``ExistsUnique xs b

class Incidence (Points Lines) extends Membership Points Lines where
  I1 (A B : Points) : A ≠ B → ∃! l : Lines, A ∈ l ∧ B ∈ l
  I2 (l : Lines) : ∃ A ∈ l, ∃ B ∈ l, A ≠ B
  I3 : ∃ A : Points, ∃ l : Lines, A ∉ l

namespace Incidence
variable {Points Lines} [self : Incidence Points Lines] {A B : Points}

def Join (A B : Points) := {l : Lines // A ∈ l ∧ B ∈ l}

example (h : A ≠ B) : ∃ l : Join A B, ∀ m : self.Join A B, l = m :=
  match I1 A B h with
  | ⟨l, hl, h⟩ => ⟨⟨l, hl⟩, fun ⟨m, hm⟩ => Subtype.ext (h m hm)⟩

example : (∃ l : Join A B, ∀ m : self.Join A B, l = m) → ∃! l : Lines, A ∈ l ∧ B ∈ l
  | ⟨⟨l, hl⟩, h⟩ => ⟨l, hl, fun m hm => Subtype.ext_iff.mp (h ⟨m, hm⟩)⟩

def Meet (l m : Lines) := {P : Points // P ∈ l ∧ P ∈ m}

/-- Two distinct lines can have at most one point in common. -/
example {l m : Lines} (hlm : l ≠ m) (A B : self.Meet l m) : A = B :=
  Classical.byContradiction fun hAB : A ≠ B => suffices l = m from hlm this
    have ⟨n, _, h⟩ := self.I1 A.val B.val (hAB ∘ Subtype.ext)
    calc l
      _ = n := h l ⟨A.property.1, B.property.1⟩ |>.symm
      _ = m := h m ⟨A.property.2, B.property.2⟩

inductive Points3 | A | B | C
inductive Lines3 | AB | BC | CA
example : Incidence Points3 Lines3 where
  mem
    | .AB, .A | .AB, .B | .BC, .B | .BC, .C | .CA, .C | .CA, .A => True
    | _, _ => False
  I1
    | .A, .B, _ | .B, .A, _ => ⟨.AB, ⟨trivial, trivial⟩, fun | .AB, _ => rfl⟩
    | .B, .C, _ | .C, .B, _ => ⟨.BC, ⟨trivial, trivial⟩, fun | .BC, _ => rfl⟩
    | .C, .A, _ | .A, .C, _ => ⟨.CA, ⟨trivial, trivial⟩, fun | .CA, _ => rfl⟩
  I2
    | .AB => ⟨.A, trivial, .B, trivial, nofun⟩
    | .BC => ⟨.B, trivial, .C, trivial, nofun⟩
    | .CA => ⟨.C, trivial, .A, trivial, nofun⟩
  I3 := ⟨.A, .BC, nofun⟩

def Parallel (l m : Lines) : Prop := l ≠ m → self.Meet l m → False

example (l : Lines) : self.Parallel l l
  | (h : l ≠ l), _ => h rfl
example {l m : Lines} : l ≠ m → self.Meet l m → ¬self.Parallel l m
  | hlm, P, h => h hlm P


end Incidence

/-!
class Join (α β) where
  join : α → α → β
class Meet (α β) where
  meet : α → α → β
/- `Mathlib.Order.Notation`: `Max.max`, `Min.min` -/
@[inherit_doc] infixl:68 " ⊔ " => Join.join
@[inherit_doc] infixl:69 " ⊓ " => Meet.meet


structure Incidence' (Points Lines) extends Membership Points Lines where
  line (A B : Points) : A ≠ B → Lines
  I1symm {A B} (h : A ≠ B) : line B A h.symm = line A B h
  I1 {A B} (h : A ≠ B) : A ∈ line A B h ∧ B ∈ line A B h
  I2 (l : Lines) : ∃ A ∈ l, ∃ B ∈ l, A ≠ B
  I3 : ∃ A : Points, ∃ l : Lines, A ∉ l
-/

class Playfair (Points Lines) extends Incidence Points Lines where
  P (A : Points) (l : Lines) : Subsingleton {m : Lines // A ∈ m ∧ toIncidence.Parallel l m}
