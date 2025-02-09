import Unicode.Iterator

/-! # Unicode

- https://www.unicode.org/glossary/#unicode_scalar_value

-/
namespace Unicode

/-- [*Code Point*](https://www.unicode.org/glossary/#code_point). (1) Any value in the Unicode codespace; that is, the range of integers from 0 to 10FFFF₁₆. (See definition D10 in [Section 3.4, Characters and Encoding](https://www.unicode.org/versions/latest/core-spec/#G2212).) Not all code points are assigned to encoded characters. See [code point type](https://www.unicode.org/glossary/#code_point_type). (2) A value, or position, for a character, in any coded character set.

[*Codespace*](https://www.unicode.org/glossary/#codespace). (1) A range of numerical values available for encoding characters. (2) For the Unicode Standard, a range of integers from 0 to 10FFFF₁₆. (See definition D9 in [Section 3.4, Characters and Encoding](https://www.unicode.org/versions/latest/core-spec/#G2212).)
-/
structure CodePoint where
  val : UInt32
  valid : val < 0x11_0000

/-! ## [3.8 Surrogates](https://www.unicode.org/versions/Unicode16.0.0/core-spec/chapter-3/#G2630)
-/

namespace CodePoint
variable (c : CodePoint)

/-- [High-surrogate code point](https://www.unicode.org/versions/Unicode16.0.0/core-spec/chapter-3/#G2626): A Unicode code point in the range U+D800 to U+DBFF.
-/
def IsHighSurrogate : Prop := 0xD800 ≤ c.val ∧ c.val < 0xDC00

/-- [Low-surrogate code point](https://www.unicode.org/versions/Unicode16.0.0/core-spec/chapter-3/#G1707): A Unicode code point in the range U+DC00 to U+DFFF.
-/
def IsLowSurrogate : Prop := 0xDC00 ≤ c.val ∧ c.val < 0xE000

end CodePoint

/-! ## [3.9 Unicode Encoding Forms](https://www.unicode.org/versions/Unicode16.0.0/core-spec/chapter-3/#G7404)
-/

/-- [Unicode scalar value](https://www.unicode.org/versions/Unicode16.0.0/core-spec/chapter-3/#G25539): Any Unicode code point except high-surrogate and low-surrogate code points.

See `Char`.
-/
structure ScalarValue where
  val : UInt32
  valid : val < 0xD800 ∨ 0xE000 ≤ val ∧ val < 0x11_0000

namespace ScalarValue

instance : Coe ScalarValue CodePoint where
  coe c := {c with valid := c.valid.elim (Nat.lt_trans · (by decide)) And.right}

/-- A Unicode scalar value is coerced to a code point with the value preserved. -/
theorem coe (c : ScalarValue) : c.val = CodePoint.val c := rfl

/-- An unreadable compact version of `ScalarValue.not_HighSurrogate`. -/
example (c : ScalarValue) (h : CodePoint.IsHighSurrogate c) : False :=
  c.valid.elim (Nat.le_lt_asymm h.1) <| Nat.lt_le_asymm (Nat.lt_trans h.2 (by decide)) ∘ And.left

/-- A Unicode scalar value is not a high-surrogate code point. -/
theorem not_HighSurrogate : (c : ScalarValue) → ¬CodePoint.IsHighSurrogate c
  | ⟨val, .inl (h : val < 0xD800)⟩, ⟨(h' : 0xD800 ≤ val), _⟩ => Nat.lt_le_asymm h h'
  | ⟨val, .inr ⟨(h : 0xE000 ≤ val), _⟩⟩, ⟨_, (h' : val < 0xDC00)⟩ => Nat.lt_le_asymm h' <|
    calc 0xDC00
      _ ≤ 0xE000 := by decide
      _ ≤ val.toNat := h

/-- A Unicode Scalar Value is not a low-surrogate code point. -/
theorem not_LowSurrogate : (c : ScalarValue) → ¬CodePoint.IsLowSurrogate c
  | ⟨val, .inr ⟨(h : 0xE000 ≤ val), _⟩⟩, ⟨_, (h' : val < 0xE000)⟩ => Nat.le_lt_asymm h h'
  | ⟨val, .inl (h : val < 0xD800)⟩, ⟨(h' : 0xDC00 ≤ val), _⟩ => Nat.lt_le_asymm h <|
    calc 0xD800
      _ ≤ 0xDC00 := by decide
      _ ≤ val.toNat := h'

/-- A code point that is neither high-surrogate nor low-surrogate is a Unicode scalar value. -/
def ofCodePoint : {c : CodePoint} → ¬c.IsHighSurrogate → ¬c.IsLowSurrogate → ScalarValue
  | {val, valid}, h₁, h₂ =>
    suffices valid : val < 0xD800 ∨ 0xE000 ≤ val ∧ val < 0x11_0000 from {val, valid}
    match aux h₁, aux h₂ with
    | .inl (h₁ : val < 0xD800), _ => .inl h₁
    | _, .inr (h₂ : 0xE000 ≤ val) => .inr ⟨h₂, valid⟩
    | .inr (h₁ : 0xDC00 ≤ val), .inl (h₂ : val < 0xDC00) => (Nat.le_lt_asymm h₁ h₂).elim
where
  aux {a b x : Nat} (hn : ¬(a ≤ x ∧ x < b)) : x < a ∨ b ≤ x :=
    (x.lt_or_ge a).imp_right (Nat.ge_of_not_lt ∘ not_and.mp hn)

end ScalarValue

/-- [Code unit sequence](https://www.unicode.org/versions/Unicode16.0.0/core-spec/chapter-3/#G25570): An ordered sequence of one or more code units.

[Code unit](https://www.unicode.org/versions/Unicode16.0.0/core-spec/chapter-3/#G25549): The minimal bit combination that can represent a unit of encoded text for processing or interchange.

[Unicode encoding form](https://www.unicode.org/versions/Unicode16.0.0/core-spec/chapter-3/#G25583): A mapping from each Unicode scalar value to a unique code unit sequence.

[Unicode string](https://www.unicode.org/versions/Unicode16.0.0/core-spec/chapter-3/#G32765): A code unit sequence containing code units of a particular Unicode encoding form.

[Well-formed](https://www.unicode.org/versions/Unicode16.0.0/core-spec/chapter-3/#G32849): A Unicode code unit sequence that purports to be in a Unicode encoding form is called well-formed if and only if it does follow the specification of that Unicode encoding form.

[Minimal well-formed code unit subsequence](https://www.unicode.org/versions/Unicode16.0.0/core-spec/chapter-3/#G47292): A well-formed Unicode code unit sequence that maps to a single Unicode scalar value.
-/
abbrev CodeUnitSeq CodeUnit σ := Iterator CodeUnit σ

namespace Utf8

abbrev CodeUnit := UInt8

/-- Require `lowerBound < 255` so that `lowerBound + 1` won't overflow 8 bits. -/
def InRange (x lowerBound upperBound : CodeUnit) (_ : lowerBound < 255 := by decide) :=
  lowerBound ≤ x ∧ x < upperBound

/-- The trailing byte range, 80..BF -/
abbrev IsTrailing (x : CodeUnit) := InRange x 0x80 0xC0

/-- [Minimal well-formed code unit subsequence](https://www.unicode.org/versions/Unicode16.0.0/core-spec/chapter-3/#G47292): A well-formed Unicode code unit sequence that maps to a single Unicode scalar value.
-/
inductive MinSeq
  | one a : InRange a 0x00 0x80 → MinSeq
  | two a b : InRange a 0xC2 0xE0 → IsTrailing b → MinSeq
  | three₁ a b c : a = 0xE0 → InRange b 0xA0 0xC0 → IsTrailing c → MinSeq
  | three₂ a b c : InRange a 0xE1 0xED → IsTrailing b → IsTrailing c → MinSeq
  | three₃ a b c : a = 0xED → InRange b 0x80 0xA0 → IsTrailing c → MinSeq
  | three₄ a b c : InRange a 0xEE 0xF0 → IsTrailing b → IsTrailing c → MinSeq
  | four₁ a b c d : a = 0xF0 → InRange b 0x90 0xC0 → IsTrailing c → IsTrailing d → MinSeq
  | four₂ a b c d : InRange a 0xF1 0xF4 → IsTrailing b → IsTrailing c → IsTrailing d → MinSeq
  | four₃ a b c d : a = 0xF4 → InRange b 0x80 0x90 → IsTrailing c → IsTrailing d → MinSeq

abbrev Seq := CodeUnitSeq CodeUnit

namespace Seq
mutual
variable {σ} [seq : Seq σ]

/-- [Well-formed UTF-8 code unit sequence](https://www.unicode.org/versions/Unicode16.0.0/core-spec/chapter-3/#G32854): A well-formed Unicode code unit sequence of UTF-8 code units.

[Table 3-7](https://www.unicode.org/versions/Unicode16.0.0/core-spec/chapter-3/#G27506). Well-Formed UTF-8 Byte Sequences
-/
inductive WellFormed : σ → Prop
  | zero {s} : ¬seq.good s → WellFormed s
  | more {s h} : WellFormed.One (seq.value s h) (seq.next s h) → WellFormed s

@[inherit_doc WellFormed]
inductive WellFormed.One : CodeUnit → σ → Prop
  | one a {s} : InRange a 0x00 0x80 → WellFormed s → WellFormed.One a s
  | more {a s} h : WellFormed.Two a (seq.value s h) (seq.next s h) → WellFormed.One a s

@[inherit_doc WellFormed]
inductive WellFormed.Two : CodeUnit → CodeUnit → σ → Prop
  | two a b s : InRange a 0xC2 0xE0 → IsTrailing b → WellFormed s → WellFormed.Two a b s
  | more {a b} s h :
    WellFormed.Three a b (seq.value s h) (seq.next s h) → WellFormed.Two a b s

@[inherit_doc WellFormed]
inductive WellFormed.Three : CodeUnit → CodeUnit → CodeUnit → σ → Prop
  | three₁ a b c s : a = 0xE0 → InRange b 0xA0 0xC0 → IsTrailing c →
    WellFormed s → WellFormed.Three a b c s
  | three₂ a b c s : InRange a 0xE1 0xED → IsTrailing b → IsTrailing c →
    WellFormed s → WellFormed.Three a b c s
  | three₃ a b c s : a = 0xED → InRange b 0x80 0xA0 → IsTrailing c →
    WellFormed s → WellFormed.Three a b c s
  | three₄ a b c s : InRange a 0xEE 0xF0 → IsTrailing b → IsTrailing c →
    WellFormed s → WellFormed.Three a b c s
  | more {a b c} s h :
    WellFormed.Four a b c (seq.value s h) (seq.next s h) → WellFormed.Three a b c s

@[inherit_doc WellFormed]
inductive WellFormed.Four : CodeUnit → CodeUnit → CodeUnit → CodeUnit → σ → Prop
  | four₁ a b c d s : a = 0xF0 → InRange b 0x90 0xC0 → IsTrailing c → IsTrailing d →
    WellFormed s → WellFormed.Four a b c d s
  | four₂ a b c d s : InRange a 0xF1 0xF4 → IsTrailing b → IsTrailing c → IsTrailing d →
    WellFormed s → WellFormed.Four a b c d s
  | four₃ a b c d s : a = 0xF4 → InRange b 0x80 0x90 → IsTrailing c → IsTrailing d →
    WellFormed s → WellFormed.Four a b c d s

end
end Seq

end Utf8

namespace Utf32

abbrev CodeUnit := UInt32

abbrev Seq := CodeUnitSeq CodeUnit

namespace Seq
mutual
variable {σ} [seq : Seq σ]

inductive WellFormed : σ → Prop
  | zero s : ¬seq.good s → WellFormed s
  | more s h : WellFormed.One (seq.value s h) (seq.next s h) → WellFormed s

@[inherit_doc WellFormed]
inductive WellFormed.One : CodeUnit → σ → Prop
  | one a s : a < 0xD800 ∨ 0xE000 ≤ a ∧ a < 0x11_0000 → WellFormed s → WellFormed.One a s

end
end Seq

end Utf32

abbrev Utf32 (σ) [seq : Utf32.Seq σ] := Subtype seq.WellFormed

/-- [Unicode 8-bit string](https://www.unicode.org/versions/Unicode16.0.0/core-spec/chapter-3/#G32748): A Unicode string containing only UTF-8 code units.
-/
abbrev Utf8 (σ) [seq : Utf8.Seq σ] := Subtype seq.WellFormed

/-- [Table 3-6](https://www.unicode.org/versions/Unicode16.0.0/core-spec/chapter-3/#G27288). UTF-8 Bit Distribution
-/
example {σ} [seq : Utf8.Seq σ] : Iterator Utf8.MinSeq (Utf8 σ) where
  good | ⟨s, _⟩ => seq.good s
  more
  | ⟨s, wf⟩, (h : seq.good s) =>
  match e : seq.more s h with
  | ⟨a, sa⟩ =>
    if ha : a < 0x80 then
      suffices Utf8.Seq.WellFormed sa from ⟨.one a ⟨a.toNat.zero_le, ha⟩, sa, this⟩
      match wf with
      | .zero hn => absurd h hn
      | .more (.one _ _ h') => have : (seq.more s h).2 = sa := congrArg Prod.snd e ; this ▸ h'
      | _ => sorry
    else
      sorry

instance {σ} [seq : Utf8.Seq σ] : Utf32.Seq σ := sorry

example {σ} [seq : Utf8.Seq σ] (s : Utf8 σ) : Utf32 σ := sorry

end Unicode

example (m : Nat × Nat) : Nat :=
  let ⟨a, b⟩ := m
  have : m.2 = b := rfl /-
  type mismatch
    rfl
  has type
    ?m.36775 = ?m.36775 : Prop
  but is expected to have type
    b = m.snd : Prop
  -/
  a

example (m : Nat × Nat) : Nat :=
  match e : m with
  | ⟨a, b⟩ =>
    have : m.2 = b := congrArg Prod.snd e
    a

#check Prod.eta