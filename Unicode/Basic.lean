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
  | three₁ (a b c : CodeUnit) : a = 0xE0 → InRange b 0xA0 0xC0 → IsTrailing c → MinSeq
  | three₂ (a b c : CodeUnit) : InRange a 0xE1 0xED → IsTrailing b → IsTrailing c → MinSeq
  | three₃ (a b c : CodeUnit) : a = 0xED → InRange b 0x80 0xA0 → IsTrailing c → MinSeq
  | three₄ (a b c : CodeUnit) : InRange a 0xEE 0xF0 → IsTrailing b → IsTrailing c → MinSeq
  | four₁ (a b c d : CodeUnit) : a = 0xF0 → InRange b 0x90 0xC0 → IsTrailing c → IsTrailing d →
    MinSeq
  | four₂ (a b c d : CodeUnit) : InRange a 0xF1 0xF4 → IsTrailing b → IsTrailing c → IsTrailing d →
    MinSeq
  | four₃ (a b c d : CodeUnit) : a = 0xF4 → InRange b 0x80 0x90 → IsTrailing c → IsTrailing d →
    MinSeq

/-- [Unicode 8-bit string](https://www.unicode.org/versions/Unicode16.0.0/core-spec/chapter-3/#G32748): A Unicode string containing only UTF-8 code units.
-/
abbrev Seq := CodeUnitSeq CodeUnit

namespace Seq

mutual
variable {σ} [seq : Seq σ]

/-- [Well-formed UTF-8 code unit sequence](https://www.unicode.org/versions/Unicode16.0.0/core-spec/chapter-3/#G32854): A well-formed Unicode code unit sequence of UTF-8 code units.

[Table 3-7](https://www.unicode.org/versions/Unicode16.0.0/core-spec/chapter-3/#G27506). Well-Formed UTF-8 Byte Sequences
-/
inductive WellFormed : σ → Prop
  | zero {s} : ¬seq.good s → WellFormed s
  | more {s} h : WellFormed.One (seq.value s h) (seq.next s h) → WellFormed s

@[inherit_doc WellFormed]
inductive WellFormed.One : CodeUnit → σ → Prop
  | one {a s} : InRange a 0x00 0x80 → WellFormed s → WellFormed.One a s
  | more {a s} h : WellFormed.Two a (seq.value s h) (seq.next s h) → WellFormed.One a s

@[inherit_doc WellFormed]
inductive WellFormed.Two : CodeUnit → CodeUnit → σ → Prop
  | two {a b s} : InRange a 0xC2 0xE0 → IsTrailing b → WellFormed s → WellFormed.Two a b s
  | more {a b s} h : WellFormed.Three a b (seq.value s h) (seq.next s h) → WellFormed.Two a b s

@[inherit_doc WellFormed]
inductive WellFormed.Three : CodeUnit → CodeUnit → CodeUnit → σ → Prop
  | three₁ {a b c s} : a = 0xE0 → InRange b 0xA0 0xC0 → IsTrailing c →
    WellFormed s → WellFormed.Three a b c s
  | three₂ {a b c s} : InRange a 0xE1 0xED → IsTrailing b → IsTrailing c →
    WellFormed s → WellFormed.Three a b c s
  | three₃ {a b c s} : a = 0xED → InRange b 0x80 0xA0 → IsTrailing c →
    WellFormed s → WellFormed.Three a b c s
  | three₄ {a b c s} : InRange a 0xEE 0xF0 → IsTrailing b → IsTrailing c →
    WellFormed s → WellFormed.Three a b c s
  | more {a b c s} h :
    WellFormed.Four a b c (seq.value s h) (seq.next s h) → WellFormed.Three a b c s

@[inherit_doc WellFormed]
inductive WellFormed.Four : CodeUnit → CodeUnit → CodeUnit → CodeUnit → σ → Prop
  | four₁ {a b c d s} : a = 0xF0 → InRange b 0x90 0xC0 → IsTrailing c → IsTrailing d →
    WellFormed s → WellFormed.Four a b c d s
  | four₂ {a b c d s} : InRange a 0xF1 0xF4 → IsTrailing b → IsTrailing c → IsTrailing d →
    WellFormed s → WellFormed.Four a b c d s
  | four₃ {a b c d s} : a = 0xF4 → InRange b 0x80 0x90 → IsTrailing c → IsTrailing d →
    WellFormed s → WellFormed.Four a b c d s

end

namespace WellFormed
variable {σ} [seq : Seq σ] {s h₁ h₂ h₃ h₄} (ha hb hc hd h)

abbrev one    := @more _ seq s h₁ <| .one ha h
abbrev two    := @more _ seq s h₁ <| .more h₂ <| .two ha hb h
abbrev three₁ := @more _ seq s h₁ <| .more h₂ <| .more h₃ <| .three₁ ha hb hc h
abbrev three₂ := @more _ seq s h₁ <| .more h₂ <| .more h₃ <| .three₂ ha hb hc h
abbrev three₃ := @more _ seq s h₁ <| .more h₂ <| .more h₃ <| .three₃ ha hb hc h
abbrev three₄ := @more _ seq s h₁ <| .more h₂ <| .more h₃ <| .three₄ ha hb hc h
abbrev four₁  := @more _ seq s h₁ <| .more h₂ <| .more h₃ <| .more h₄ <| .four₁ ha hb hc hd h
abbrev four₂  := @more _ seq s h₁ <| .more h₂ <| .more h₃ <| .more h₄ <| .four₂ ha hb hc hd h
abbrev four₃  := @more _ seq s h₁ <| .more h₂ <| .more h₃ <| .more h₄ <| .four₃ ha hb hc hd h

end WellFormed

end Seq

end Utf8

namespace Utf32

abbrev CodeUnit := UInt32

/-- [Unicode 32-bit string](https://www.unicode.org/versions/Unicode16.0.0/core-spec/chapter-3/#G32752): A Unicode string containing only UTF-32 code units.
-/
abbrev Seq := CodeUnitSeq CodeUnit

namespace Seq

mutual
variable {σ} [seq : Seq σ]

/-- [Well-formed UTF-32 code unit sequence](https://www.unicode.org/versions/Unicode16.0.0/core-spec/chapter-3/#G32858): A well-formed Unicode code unit sequence of UTF-32 code units.
-/
inductive WellFormed : σ → Prop
  | zero {s} : ¬seq.good s → WellFormed s
  | more {s} h : WellFormed.One (seq.value s h) (seq.next s h) → WellFormed s

@[inherit_doc WellFormed]
inductive WellFormed.One : CodeUnit → σ → Prop
  | one {a s} : a < 0xD800 ∨ 0xE000 ≤ a ∧ a < 0x11_0000 → WellFormed s → WellFormed.One a s

end

namespace WellFormed
variable {σ} [seq : Seq σ] {s h₁} (ha h)

abbrev one := @more _ seq s h₁ <| .one ha h

end WellFormed

end Seq

end Utf32

@[inherit_doc Utf32.Seq.WellFormed]
abbrev Utf32 (σ) [seq : Utf32.Seq σ] := Subtype seq.WellFormed

example {σ} [seq : Utf32.Seq σ] : Iterator ScalarValue (Utf32 σ) where
  good | ⟨s, _⟩ => seq.good s
  more
  | ⟨s, wf⟩, (h₁ : seq.good s) =>
    let A := seq.more s h₁; let s := A.2; let a := A.1
    suffices _ ∧ _ from match this with | ⟨ha, h⟩ => ⟨⟨a, ha⟩, s, h⟩
    match wf with
    | .zero hn => absurd h₁ hn
    | .one ha h => ⟨ha, h⟩

@[inherit_doc Utf8.Seq.WellFormed]
abbrev Utf8 (σ) [seq : Utf8.Seq σ] := Subtype seq.WellFormed

example {σ} [seq : Utf8.Seq σ] : Iterator Utf8.MinSeq (Utf8 σ) where
  good | ⟨s, _⟩ => seq.good s
  more
  | ⟨s, wf⟩, (h₁ : seq.good s) =>
    let a := seq.more s h₁; let s := a.2; let a := a.1
    if ha' : a < 0x80 then
      suffices _ ∧ _ from match this with | ⟨ha, h⟩ => ⟨.one a ha, s, h⟩
      match wf with
      | .zero hn => absurd h₁ hn
      | .one ha h => ⟨ha, h⟩
      | .two ha .. | .three₂ ha .. | .three₄ ha .. | .four₂ ha .. => absurd_le ha' ha.1
      | .three₁ ha .. | .three₃ ha .. | .four₁ ha .. | .four₃ ha .. => absurd_eq ha' ha
    else
    let b := suffices seq.good s from seq.more s this
      match wf with
      | .zero hn => absurd h₁ hn
      | .one ha .. => absurd ha.2 ‹_›
      | .more _ (.more h₂ _) => h₂
    let s := b.2; let b := b.1
    if ha' : a < 0xE0 then
      suffices _ ∧ _ ∧ _ from match this with | ⟨ha, hb, h⟩ => ⟨.two a b ha hb, s, h⟩
      match wf with
      | .zero hn => absurd h₁ hn
      | .one ha .. => absurd ha.2 ‹_›
      | .two ha hb h => ⟨ha, hb, h⟩
      | .three₂ ha .. | .three₄ ha .. | .four₂ ha .. => absurd_le ha' ha.1
      | .three₁ ha .. | .three₃ ha .. | .four₁ ha .. | .four₃ ha .. => absurd_eq ha' ha
    else
    let c := suffices seq.good s from seq.more s this
      match wf with
      | .zero hn => absurd h₁ hn
      | .one ha .. | .two ha .. => absurd ha.2 ‹_›
      | .more _ (.more _ (.more h₃ _)) => h₃
    let s := c.2; let c := c.1
    if ha' : a = 0xE0 then
      have ha' : a < 0xE1 := trans ha' Nat.le.refl
      suffices _ ∧ _ ∧ _ ∧ _ from
        match this with | ⟨ha, hb, hc, h⟩ => ⟨.three₁ a b c ha hb hc, s, h⟩
      match wf with
      | .zero hn => absurd h₁ hn
      | .one ha .. | .two ha .. => absurd ha.2 ‹_›
      | .three₁ ha hb hc h => ⟨ha, hb, hc, h⟩
      | .three₂ ha .. | .three₄ ha .. | .four₂ ha .. => absurd_le ha' ha.1
      | .three₃ ha .. | .four₁ ha .. | .four₃ ha .. => absurd_eq ha' ha
    else if ha' : a < 0xED then
      suffices _ ∧ _ ∧ _ ∧ _ from
        match this with | ⟨ha, hb, hc, h⟩ => ⟨.three₂ a b c ha hb hc, s, h⟩
      match wf with
      | .zero hn => absurd h₁ hn
      | .three₁ ha .. => absurd ha ‹_›
      | .one ha .. | .two ha .. => absurd ha.2 ‹_›
      | .three₂ ha hb hc h => ⟨ha, hb, hc, h⟩
      | .three₄ ha .. | .four₂ ha .. => absurd_le ha' ha.1
      | .three₃ ha .. | .four₁ ha .. | .four₃ ha .. => absurd_eq ha' ha
    else if ha' : a = 0xED then
      have ha' : a < 0xEE := trans ha' Nat.le.refl
      suffices _ ∧ _ ∧ _ ∧ _ from
        match this with | ⟨ha, hb, hc, h⟩ => ⟨.three₃ a b c ha hb hc, s, h⟩
      match wf with
      | .zero hn => absurd h₁ hn
      | .three₁ ha .. => absurd ha ‹_›
      | .one ha .. | .two ha .. | .three₂ ha .. => absurd ha.2 ‹_›
      | .three₃ ha hb hc h => ⟨ha, hb, hc, h⟩
      | .three₄ ha .. | .four₂ ha .. => absurd_le ha' ha.1
      | .four₁ ha .. | .four₃ ha .. => absurd_eq ha' ha
    else if ha' : a < 0xF0 then
      suffices _ ∧ _ ∧ _ ∧ _ from
        match this with | ⟨ha, hb, hc, h⟩ => ⟨.three₄ a b c ha hb hc, s, h⟩
      match wf with
      | .zero hn => absurd h₁ hn
      | .three₁ ha .. | .three₃ ha .. => absurd ha ‹_›
      | .one ha .. | .two ha .. | .three₂ ha .. => absurd ha.2 ‹_›
      | .three₄ ha hb hc h => ⟨ha, hb, hc, h⟩
      | .four₂ ha .. => absurd_le ha' ha.1
      | .four₁ ha .. | .four₃ ha .. => absurd_eq ha' ha
    else
    let d := suffices seq.good s from seq.more s this
      match wf with
      | .zero hn => absurd h₁ hn
      | .three₁ ha .. | .three₃ ha .. => absurd ha ‹_›
      | .one ha .. | .two ha .. | .three₂ ha .. | .three₄ ha .. => absurd ha.2 ‹_›
      | .more _ (.more _ (.more _ (.more h₄ _))) => h₄
    let s := d.2; let d := d.1
    if ha' : a = 0xF0 then
      have ha' : a < 0xF1 := trans ha' Nat.le.refl
      suffices _ ∧ _ ∧ _ ∧ _ ∧ _ from
        match this with | ⟨ha, hb, hc, hd, h⟩ => ⟨.four₁ a b c d ha hb hc hd, s, h⟩
      match wf with
      | .zero hn => absurd h₁ hn
      | .three₁ ha .. | .three₃ ha .. => absurd ha ‹_›
      | .one ha .. | .two ha .. | .three₂ ha .. | .three₄ ha .. => absurd ha.2 ‹_›
      | .four₁ ha hb hc hd h => ⟨ha, hb, hc, hd, h⟩
      | .four₂ ha .. => absurd_le ha' ha.1
      | .four₃ ha .. => absurd_eq ha' ha
    else if ha' : a < 0xF4 then
      suffices _ ∧ _ ∧ _ ∧ _ ∧ _ from
        match this with | ⟨ha, hb, hc, hd, h⟩ => ⟨.four₂ a b c d ha hb hc hd, s, h⟩
      match wf with
      | .zero hn => absurd h₁ hn
      | .three₁ ha .. | .three₃ ha .. | .four₁ ha .. => absurd ha ‹_›
      | .one ha .. | .two ha .. | .three₂ ha .. | .three₄ ha .. => absurd ha.2 ‹_›
      | .four₂ ha hb hc hd h => ⟨ha, hb, hc, hd, h⟩
      | .four₃ ha .. => absurd_eq ha' ha
    else
      suffices _ ∧ _ ∧ _ ∧ _ ∧ _ from
        match this with | ⟨ha, hb, hc, hd, h⟩ => ⟨.four₃ a b c d ha hb hc hd, s, h⟩
      match wf with
      | .zero hn => absurd h₁ hn
      | .three₁ ha .. | .three₃ ha .. | .four₁ ha .. => absurd ha ‹_›
      | .one ha .. | .two ha .. | .three₂ ha .. | .three₄ ha .. | .four₂ ha .. => absurd ha.2 ‹_›
      | .four₃ ha hb hc hd h => ⟨ha, hb, hc, hd, h⟩
where
  absurd_le {α} {x a b : Utf8.CodeUnit} (ha : x < a) (hb : b ≤ x) (h : a ≤ b := by decide) : α :=
    nomatch Nat.lt_le_asymm ha (Nat.le_trans h hb)
  absurd_eq {α} {x a b : Utf8.CodeUnit} (ha : x < a) (hb : x = b) (h : a ≤ b := by decide) : α :=
    nomatch Nat.lt_le_asymm ha (hb ▸ h)

/-- [Table 3-6](https://www.unicode.org/versions/Unicode16.0.0/core-spec/chapter-3/#G27288). UTF-8 Bit Distribution
```
0xxxxxxx ← 0xxxxxxx
00000yyy yyxxxxxx ← 110yyyyy 10xxxxxx
zzzzyyyy yyxxxxxx ← 1110zzzz 10yyyyyy 10xxxxxx
000uuuuu zzzzyyyy yyxxxxxx ← 11110uuu 10uuzzzz 10yyyyyy 10xxxxxx
```
-/
instance Utf8.Seq.toUtf32Seq {σ} [seq : Utf8.Seq σ] : Utf32.Seq (Utf8 σ) where
  good | ⟨s, _⟩ => seq.good s
  more
  | ⟨s, wf⟩, (h₁ : seq.good s) =>
    let A := seq.more s h₁; let s := A.2; let a := A.1
    if ha' : a < 0x80 then -- 0xxxxxxx ← 0xxxxxxx
      suffices _ from ⟨a.toUInt32, s, this⟩
      match wf with
      | .zero hn => absurd h₁ hn
      | .one _ h => h
      | .two ha .. | .three₂ ha .. | .three₄ ha .. | .four₂ ha .. => absurd_le ha' ha.1
      | .three₁ ha .. | .three₃ ha .. | .four₁ ha .. | .four₃ ha .. => absurd_eq ha' ha
    else
    let B := suffices seq.good s from seq.more s this
      match wf with
      | .zero hn => absurd h₁ hn
      | .one ha .. => absurd ha.2 ‹_›
      | .more _ (.more h₂ _) => h₂
    let s := B.2; let b := B.1
    if ha' : a < 0xE0 then -- 00000yyy yyxxxxxx ← 110yyyyy 10xxxxxx
      let y := a.toBitVec.extractLsb' 0 5
      let x := b.toBitVec.extractLsb' 0 6
      suffices _ from ⟨toUInt32 (y ++ x), s, this⟩
      match wf with
      | .zero hn => absurd h₁ hn
      | .one ha .. => absurd ha.2 ‹_›
      | .two _ _ h => h
      | .three₂ ha .. | .three₄ ha .. | .four₂ ha .. => absurd_le ha' ha.1
      | .three₁ ha .. | .three₃ ha .. | .four₁ ha .. | .four₃ ha .. => absurd_eq ha' ha
    else
    let C := suffices seq.good s from seq.more s this
      match wf with
      | .zero hn => absurd h₁ hn
      | .one ha .. | .two ha .. => absurd ha.2 ‹_›
      | .more _ (.more _ (.more h₃ _)) => h₃
    let s := C.2; let c := C.1
    if ha' : a < 0xF0 then -- zzzzyyyy yyxxxxxx ← 1110zzzz 10yyyyyy 10xxxxxx
      let z := a.toBitVec.extractLsb' 0 4
      let y := b.toBitVec.extractLsb' 0 6
      let x := c.toBitVec.extractLsb' 0 6
      suffices _ from ⟨toUInt32 (z ++ y ++ x), s, this⟩
      match wf with
      | .zero hn => absurd h₁ hn
      | .one ha .. | .two ha .. => absurd ha.2 ‹_›
      | .three₁ _ _ _ h | .three₂ _ _ _ h | .three₃ _ _ _ h | .three₄ _ _ _ h => h
      | .four₂ ha .. => absurd_le ha' ha.1
      | .four₁ ha .. | .four₃ ha .. => absurd_eq ha' ha
    else -- 000uuuuu zzzzyyyy yyxxxxxx ← 11110uuu 10uuzzzz 10yyyyyy 10xxxxxx
    have ha' : a ≥ 0xF0 := Nat.le_of_not_lt ha'
    let D := suffices seq.good s from seq.more s this
      match wf with
      | .zero hn => absurd h₁ hn
      | .one ha .. | .two ha .. | .three₂ ha .. | .three₄ ha .. => absurd_le ha.2 ha'
      | .three₁ ha .. | .three₃ ha .. => absurd_eq' ha ha'
      | .more _ (.more _ (.more _ (.more h₄ _))) => h₄
    let s := D.2; let d := D.1
      let u := a.toBitVec.extractLsb' 0 3
      let z := b.toBitVec.extractLsb' 0 4
      let y := c.toBitVec.extractLsb' 0 6
      let x := d.toBitVec.extractLsb' 0 6
      suffices _ from ⟨toUInt32 (u ++ z ++ y ++ x), s, this⟩
      match wf with
      | .zero hn => absurd h₁ hn
      | .one ha .. | .two ha .. | .three₂ ha .. | .three₄ ha .. => absurd_le ha.2 ha'
      | .three₁ ha .. | .three₃ ha .. => absurd_eq' ha ha'
      | .four₁ _ _ _ _ h | .four₂ _ _ _ _ h | .four₃ _ _ _ _ h => h
where
  absurd_le {α} {x a b : Utf8.CodeUnit} (ha : x < a) (hb : b ≤ x) (h : a ≤ b := by decide) : α :=
    nomatch Nat.lt_le_asymm ha (Nat.le_trans h hb)
  absurd_eq {α} {x a b : Utf8.CodeUnit} (ha : x < a) (hb : x = b) (h : a ≤ b := by decide) : α :=
    nomatch Nat.lt_le_asymm ha (hb ▸ h)
  absurd_eq' {α} {x a b : Utf8.CodeUnit} (ha : x = a) (hb : b ≤ x) (h : a < b := by decide) : α :=
    absurd_eq h ha.symm hb
  toUInt32 {w} (x : BitVec w) (h : w ≤ 32 := by decide) : UInt32 :=
    .mk (x.setWidth' h)

example {σ} [seq : Utf8.Seq σ] (s : Utf8 σ) /-[Decidable (seq.good s)]-/ : Utf32 (Utf8 σ) where
  val := s
  property :=
    let seq' := seq.toUtf32Seq
    show seq'.WellFormed s from
    haveI : Decidable (seq.good s) := Classical.propDecidable _
    if h₁ : seq'.good s then
      let A := seq'.more s h₁; let s := A.2; let a := A.1
      suffices (a < 0xD800 ∨ 0xE000 ≤ a ∧ a < 0x11_0000) ∧ seq'.WellFormed s from .one this.1 this.2
      if ha : a < 0x80 then -- 0xxxxxxx ← 0xxxxxxx
        let a' := a.toUInt8
        have e : a = a'.toUInt32 := sorry
        have ha' : a' < 0x80 := sorry
        sorry
      else
       sorry
    else
      .zero h₁
  /-
  good | ⟨s, _⟩ => seq.good s
  more
  | ⟨s, wf⟩, (h₁ : seq.good s) =>
    let a := seq.more s h₁; let s := a.2; let a := a.1
    if ha' : a < 0x80 then -- 0xxxxxxx ← 0xxxxxxx
      suffices _ from ⟨a.toUInt32, s, this⟩
      match wf with
      | .zero hn => absurd h₁ hn
      | .one _ h => h
      | .two ha .. | .three₂ ha .. | .three₄ ha .. | .four₂ ha .. => absurd_le ha' ha.1
      | .three₁ ha .. | .three₃ ha .. | .four₁ ha .. | .four₃ ha .. => absurd_eq ha' ha
    else
    let b := suffices seq.good s from seq.more s this
      match wf with
      | .zero hn => absurd h₁ hn
      | .one ha .. => absurd ha.2 ‹_›
      | .more _ (.more h₂ _) => h₂
    let s := b.2; let b := b.1
    if ha' : a < 0xE0 then -- 00000yyy yyxxxxxx ← 110yyyyy 10xxxxxx
      let y := a.toBitVec.extractLsb' 0 5
      let x := b.toBitVec.extractLsb' 0 6
      suffices _ from ⟨toUInt32 (y ++ x), s, this⟩
      match wf with
      | .zero hn => absurd h₁ hn
      | .one ha .. => absurd ha.2 ‹_›
      | .two _ _ h => h
      | .three₂ ha .. | .three₄ ha .. | .four₂ ha .. => absurd_le ha' ha.1
      | .three₁ ha .. | .three₃ ha .. | .four₁ ha .. | .four₃ ha .. => absurd_eq ha' ha
    else
    let c := suffices seq.good s from seq.more s this
      match wf with
      | .zero hn => absurd h₁ hn
      | .one ha .. | .two ha .. => absurd ha.2 ‹_›
      | .more _ (.more _ (.more h₃ _)) => h₃
    let s := c.2; let c := c.1
    if ha' : a < 0xF0 then -- zzzzyyyy yyxxxxxx ← 1110zzzz 10yyyyyy 10xxxxxx
      let z := a.toBitVec.extractLsb' 0 4
      let y := b.toBitVec.extractLsb' 0 6
      let x := c.toBitVec.extractLsb' 0 6
      suffices _ from ⟨toUInt32 (z ++ y ++ x), s, this⟩
      match wf with
      | .zero hn => absurd h₁ hn
      | .one ha .. | .two ha .. => absurd ha.2 ‹_›
      | .three₁ _ _ _ h | .three₂ _ _ _ h | .three₃ _ _ _ h | .three₄ _ _ _ h => h
      | .four₂ ha .. => absurd_le ha' ha.1
      | .four₁ ha .. | .four₃ ha .. => absurd_eq ha' ha
    else -- 000uuuuu zzzzyyyy yyxxxxxx ← 11110uuu 10uuzzzz 10yyyyyy 10xxxxxx
    have ha' : a ≥ 0xF0 := Nat.le_of_not_lt ha'
    let d := suffices seq.good s from seq.more s this
      match wf with
      | .zero hn => absurd h₁ hn
      | .one ha .. | .two ha .. | .three₂ ha .. | .three₄ ha .. => absurd_le ha.2 ha'
      | .three₁ ha .. | .three₃ ha .. => absurd_eq' ha ha'
      | .more _ (.more _ (.more _ (.more h₄ _))) => h₄
    let s := d.2; let d := d.1
      let u := a.toBitVec.extractLsb' 0 3
      let z := b.toBitVec.extractLsb' 0 4
      let y := c.toBitVec.extractLsb' 0 6
      let x := d.toBitVec.extractLsb' 0 6
      suffices _ from ⟨toUInt32 (u ++ z ++ y ++ x), s, this⟩
      match wf with
      | .zero hn => absurd h₁ hn
      | .one ha .. | .two ha .. | .three₂ ha .. | .three₄ ha .. => absurd_le ha.2 ha'
      | .three₁ ha .. | .three₃ ha .. => absurd_eq' ha ha'
      | .four₁ _ _ _ _ h | .four₂ _ _ _ _ h | .four₃ _ _ _ _ h => h
  -/
where
  absurd_le {α} {x a b : Utf8.CodeUnit} (ha : x < a) (hb : b ≤ x) (h : a ≤ b := by decide) : α :=
    nomatch Nat.lt_le_asymm ha (Nat.le_trans h hb)
  absurd_eq {α} {x a b : Utf8.CodeUnit} (ha : x < a) (hb : x = b) (h : a ≤ b := by decide) : α :=
    nomatch Nat.lt_le_asymm ha (hb ▸ h)
  absurd_eq' {α} {x a b : Utf8.CodeUnit} (ha : x = a) (hb : b ≤ x) (h : a < b := by decide) : α :=
    absurd_eq h ha.symm hb
  toUInt32 {w} (x : BitVec w) (h : w ≤ 32 := by decide) : UInt32 :=
    .mk (x.setWidth' h)

end Unicode

/-!
## 1 byte
0xxxxxxx ← a(0xxxxxxx)
a
## 2 bytes
00000yyy yyxxxxxx ← a(110yyyyy) b(10xxxxxx)
11_0yyy_yy  _
  _    _10xx_xxxx
11_0000_1000_0000
(a << 6) ^ (b ^ 0x3080)
((a << 6) ^ 0x1000) ^ (b ^ 0x2080)
((a ^ 0x20) << 6) ^ (b ^ 0x2080)
11_000010_000000
((a ^ 0xC2) << 6) ^ b
## 3 bytes
zzzzyyyy yyxxxxxx ← a(1110zzzz) b(10yyyyyy) c(10xxxxxx)
1110_zzzz_    _    _
    _  10_yyyy_yy  _
    _    _     10xx_xxxx
1110_0010_0000_1000_0000
((a << 12) ^ (b << 6)) ^ (c ^ 0xE_2080)
(((a << 12) ^ (b << 6)) ^ 0xE_0000) ^ (c ^ 0x2080)
(((a ^ 0xE0) << 12) ^ (b << 6)) ^ (c ^ 0x2080)
11_100010_000010_000000
((a ^ 0XE2) << 12) ^ ((b ^ 0x2) << 6) ^ c
## 4 bytes
000uuuuu zzzzyyyy yyxxxxxx ← a(11110uuu) b(10uuzzzz) c(10yyyyyy) d(10xxxxxx)
11_110u_uu  _    _    _    _
  _    _10uu_zzzz_    _    _
  _    _    _  10_yyyy_yy  _
  _    _    _    _    _10xx_xxxx
11_1100_1000_0010_0000_1000_0000
((a << 18) ^ (b << 12)) ^ ((c << 6) ^ (d ^ 0x3C8_2080))
((a << 18) ^ ((b ^ 0x3C80) << 12)) ^ ((c << 6) ^ (d ^ 0x2080))
0x1C00 = 0b1_1100_0000_0000 = 0b111_0000 << 6 = 0x70 << 6
(((a ^ 0x70) << 18) ^ ((b ^ 0x2080) << 12)) ^ ((c << 6) ^ (d ^ 0x2080))
11_110010_000010_000010_000000
((a ^ 0xF2) << 18) ^ ((b ^ 0x2) << 12) ^ ((c ^ 0x2) << 6) ^ d
## SIMD
- [UTF-8 processing using SIMD (SSE4)](https://woboq.com/blog/utf-8-processing-using-simd.html)
- [Validating UTF-8 In Less Than One Instruction Per Byte](https://arxiv.org/pdf/2010.03090)
-/

#check Nat.rec
#check Unicode.Utf8.Seq.WellFormed.rec
def Unicode.Utf8.moreRec.{u} {σ} [seq : Seq σ] {motive : ∀ s, seq.good s → Sort u}
    (s : Utf8 σ) (h₁ : seq.good s)
    (one : seq.value s h₁ < 0x80 → seq.WellFormed (seq.next s h₁) → motive s h₁)
    (two : ∀ h₂, InRange (seq.value s h₁) 0xC2 0xE0 → IsTrailing (seq.value (seq.next s h₁) h₂) →
      seq.WellFormed (seq.next (seq.next s h₁) h₂) → motive s h₁)
    (three : ∀ h₂ h₃, InRange (seq.value s h₁) 0xE0 0xF0 →
      seq.WellFormed (seq.next (seq.next (seq.next s h₁) h₂) h₃) → motive s h₁)
    (four : ∀ h₂ h₃ h₄, InRange (seq.value s h₁) 0xF0 0xF5 →
      seq.WellFormed (seq.next (seq.next (seq.next (seq.next s h₁) h₂) h₃) h₄) → motive s h₁)
  : motive s h₁ :=
  let wf := s.2; let s := s.1
  let A := seq.more s h₁; let s := A.2; let a := A.1
  if ha' : a < 0x80 then
    suffices _ from one ha' this
    match wf with
    | .zero hn => absurd h₁ hn
    | .one _ h => h
    | .two ha .. | .three₂ ha .. | .three₄ ha .. | .four₂ ha .. => absurd_le ha' ha.1
    | .three₁ ha .. | .three₃ ha .. | .four₁ ha .. | .four₃ ha .. => absurd_eq ha' ha
  else
  have h₂ : seq.good s :=
    match wf with
    | .zero hn => absurd h₁ hn
    | .one ha .. => absurd ha.2 ‹_›
    | .more _ (.more h₂ _) => h₂
  let B := seq.more s h₂; let s := B.2; let b := B.1
  if ha' : a < 0xE0 then
    suffices _ ∧ _ ∧ _ from two h₂ this.1 this.2.1 this.2.2
    match wf with
    | .zero hn => absurd h₁ hn
    | .one ha .. => absurd ha.2 ‹_›
    | .two ha hb h => ⟨ha, hb, h⟩
    | .three₂ ha .. | .three₄ ha .. | .four₂ ha .. => absurd_le ha' ha.1
    | .three₁ ha .. | .three₃ ha .. | .four₁ ha .. | .four₃ ha .. => absurd_eq ha' ha
  else
  have h₃ : seq.good s :=
    match wf with
    | .zero hn => absurd h₁ hn
    | .one ha .. | .two ha .. => absurd ha.2 ‹_›
    | .more _ (.more _ (.more h₃ _)) => h₃
  let C := seq.more s h₃; let s := C.2; let c := C.1
  have ha'' : 0xE0 ≤ a := Nat.le_of_not_lt ha'
  if ha' : a < 0xF0 then
    suffices _ ∧ _ from three h₂ h₃ this.1 this.2
    match wf with
    | .zero hn => absurd h₁ hn
    | .one ha .. | .two ha .. => absurd ha.2 ‹_›
    | .three₂ ha _ _ h | .three₄ ha _ _ h => ⟨⟨ha'', Nat.lt_of_lt_of_le ha.2 (by decide)⟩, h⟩
    | .three₁ ha _ _ h | .three₃ ha _ _ h => ⟨⟨ha'', ha ▸ by decide⟩, h⟩
    | .four₂ ha .. => absurd_le ha' ha.1
    | .four₁ ha .. | .four₃ ha .. => absurd_eq ha' ha
  else
  have ha' : a ≥ 0xF0 := Nat.le_of_not_lt ha'
  have h₄ : seq.good s :=
    match wf with
    | .zero hn => absurd h₁ hn
    | .one ha .. | .two ha .. | .three₂ ha .. | .three₄ ha .. => absurd_le ha.2 ha'
    | .three₁ ha .. | .three₃ ha .. => absurd_eq' ha ha'
    | .more _ (.more _ (.more _ (.more h₄ _))) => h₄
  let D := seq.more s h₄; let s := D.2; let d := D.1
    suffices _ ∧ _ from four h₂ h₃ h₄ this.1 this.2
    match wf with
    | .zero hn => absurd h₁ hn
    | .one ha .. | .two ha .. | .three₂ ha .. | .three₄ ha .. => absurd_le ha.2 ha'
    | .three₁ ha .. | .three₃ ha .. => absurd_eq' ha ha'
    | .four₂ ha _ _ _ h => ⟨⟨ha', Nat.lt_trans ha.2 Nat.le.refl⟩, h⟩
    | .four₁ ha _ _ _ h | .four₃ ha _ _ _ h => ⟨⟨ha', ha ▸ by decide⟩, h⟩
where
  absurd_le {α} {x a b : Utf8.CodeUnit} (ha : x < a) (hb : b ≤ x) (h : a ≤ b := by decide) : α :=
    nomatch Nat.lt_le_asymm ha (Nat.le_trans h hb)
  absurd_eq {α} {x a b : Utf8.CodeUnit} (ha : x < a) (hb : x = b) (h : a ≤ b := by decide) : α :=
    nomatch Nat.lt_le_asymm ha (hb ▸ h)
  absurd_eq' {α} {x a b : Utf8.CodeUnit} (ha : x = a) (hb : b ≤ x) (h : a < b := by decide) : α :=
    absurd_eq h ha.symm hb

open Unicode in
example {σ} [seq : Utf8.Seq σ] : Utf32.Seq (Utf8 σ) where
  good s := seq.good s
  more s (h₁ : seq.good s) := show Utf32.CodeUnit × Utf8 σ from
    s.moreRec h₁ (motive := fun _ _ => Utf32.CodeUnit × Utf8 σ)
      (fun _ h => show Utf32.CodeUnit × Utf8 σ from
        let A := seq.more s h₁; let s := A.2; let a := A.1
        -- 0xxxxxxx ← 0xxxxxxx
        ⟨a.toUInt32, s, h⟩)
      (fun h₂ _ _ h => show Utf32.CodeUnit × Utf8 σ from
        let A := seq.more s h₁; let s := A.2; let a := A.1
        let B := seq.more s h₂; let s := B.2; let b := B.1
        -- 00000yyy yyxxxxxx ← 110yyyyy 10xxxxxx
        let y := a.toBitVec.extractLsb' 0 5
        let x := b.toBitVec.extractLsb' 0 6
        ⟨toUInt32 (y ++ x), s, h⟩)
      (fun h₂ h₃ _ h => show Utf32.CodeUnit × Utf8 σ from
        let A := seq.more s h₁; let s := A.2; let a := A.1
        let B := seq.more s h₂; let s := B.2; let b := B.1
        let C := seq.more s h₃; let s := C.2; let c := C.1
        -- zzzzyyyy yyxxxxxx ← 1110zzzz 10yyyyyy 10xxxxxx
        let z := a.toBitVec.extractLsb' 0 4
        let y := b.toBitVec.extractLsb' 0 6
        let x := c.toBitVec.extractLsb' 0 6
        ⟨toUInt32 (z ++ y ++ x), s, h⟩)
      (fun h₂ h₃ h₄ _ h => show Utf32.CodeUnit × Utf8 σ from
        let A := seq.more s h₁; let s := A.2; let a := A.1
        let B := seq.more s h₂; let s := B.2; let b := B.1
        let C := seq.more s h₃; let s := C.2; let c := C.1
        let D := seq.more s h₄; let s := D.2; let d := D.1
        -- 000uuuuu zzzzyyyy yyxxxxxx ← 11110uuu 10uuzzzz 10yyyyyy 10xxxxxx
        let u := a.toBitVec.extractLsb' 0 3
        let z := b.toBitVec.extractLsb' 0 4
        let y := c.toBitVec.extractLsb' 0 6
        let x := d.toBitVec.extractLsb' 0 6
        ⟨toUInt32 (u ++ z ++ y ++ x), s, h⟩)
where
  toUInt32 {w} (x : BitVec w) (h : w ≤ 32 := by decide) : UInt32 :=
    .mk (x.setWidth' h)
