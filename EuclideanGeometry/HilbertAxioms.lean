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

structure Incidence (Points Lines) [Membership Points Lines] : Prop where
  I1 {A B : Points} : A ≠ B → ∃! l : Lines, A ∈ l ∧ B ∈ l
  I2 (l : Lines) : ∃ A ∈ l, ∃ B ∈ l, A ≠ B
  I3 : ∃ A : Points, ∃ l : Lines, A ∉ l

section
variable (Points Lines) [Membership Points Lines] (self : Incidence Points Lines)
variable {A B : Points}

example (h : A ≠ B) : ∃ l : Lines, A ∈ l ∧ B ∈ l ∧ ∀ m : Lines, A ∈ m ∧ B ∈ m → l = m :=
  match self.I1 h with
  | ⟨l, (hl : A ∈ l ∧ B ∈ l), (hm: ∀ m : Lines, A ∈ m ∧ B ∈ m → l = m)⟩ => ⟨l, hl.1, hl.2, hm⟩

example : (∃ l, A ∈ l ∧ B ∈ l ∧ ∀ m : Lines, A ∈ m ∧ B ∈ m → l = m) → ∃! l : Lines, A ∈ l ∧ B ∈ l
  | ⟨l, hA, hB, hm⟩ => ⟨l, ⟨hA, hB⟩, hm⟩

end
