/-!
# Tarski's Axioms

## Bibliography

- Wikipedia, *[Tarski's axioms](https://en.wikipedia.org/wiki/Tarski%27s_axioms)*
- Alfred Tarski, Steven Givant, *[Tarski's System of Geometry](https://doi.org/10.2307/421089)*

-/

structure TarskiSystem (Points) where
  /-- Betweenness: `between a b c` intuitively means that the point `b` lies on the line segment
  joining `a` and `c`.
  -/
  between (a b c : Points) : Prop
  /-- Equidistance or congruence of segments: `equidistant a b c d` intuitively means that the distance from `a` to `b` is the same as the distance from `c` to `d`, or, put another way, the line segment joining `a` and `b` is congruent to the line segment joining `c` and `d`.
  -/
  equidistant (a b c d : Points) : Prop

  refl4 {a b} : equidistant a b b a
  id4 {a b c} : equidistant a b c c → a = b
  trans4 {a b c d e f} : equidistant a b c d ∧ equidistant c d e f → equidistant a b e f

  id3 {a b} : between a b a → a = b
  pasch {c a x a' c'} : between c a x → between x a' c' → ∃ b, between a b c' ∧ between a' b c
