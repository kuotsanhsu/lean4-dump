/-! # Unicode

- https://www.unicode.org/glossary/#unicode_scalar_value

-/

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
class CodeUnitSeq (CodeUnit σ) extends EmptyCollection σ where
  nextCodeUnit (s : σ) : s ≠ ∅ → CodeUnit × σ

namespace Utf8

/-- Require `lowerBound < 255` so that `lowerBound + 1` won't overflow 8 bits. -/
abbrev ByteRange (lowerBound : UInt8) (upperBound : UInt8 := lowerBound + 1)
    (_ : lowerBound < 255 := by decide) :=
  {codePoint : UInt8 // lowerBound ≤ codePoint ∧ codePoint < upperBound}

/-- The range 80..BF -/
abbrev TrailingByteRange := ByteRange 0x80 0xC0

/-- [Well-formed UTF-8 code unit sequence](https://www.unicode.org/versions/Unicode16.0.0/core-spec/chapter-3/#G32854): A well-formed Unicode code unit sequence of UTF-8 code units.

[Table 3-7](https://www.unicode.org/versions/Unicode16.0.0/core-spec/chapter-3/#G27506). Well-Formed UTF-8 Byte Sequences

**TODO**: replace `List UInt8` with `CodeUnitSeq UInt8 σ`.
-/
inductive WellFormed : List UInt8 → Prop
  | zero : WellFormed []
  | one (a : ByteRange 0x00 0x80) tail : WellFormed tail → WellFormed %[a| tail]
  | two (a : ByteRange 0xC2 0xE0) (b : TrailingByteRange) tail :
    WellFormed tail → WellFormed %[a, b| tail]
  | three₁ (a : ByteRange 0xE0) (b : ByteRange 0xA0 0xC0) (c : TrailingByteRange) tail :
    WellFormed tail → WellFormed %[a, b, c| tail]
  | three₂ (a : ByteRange 0xE1 0xED) (b c : TrailingByteRange) tail :
    WellFormed tail → WellFormed %[a, b, c| tail]
  | three₃ (a : ByteRange 0xED) (b : ByteRange 0x80 0xA0) (c : TrailingByteRange) tail :
    WellFormed tail → WellFormed %[a, b, c| tail]
  | three₄ (a : ByteRange 0xEE 0xF0) (b c : TrailingByteRange) tail :
    WellFormed tail → WellFormed %[a, b, c| tail]
  | four₁ (a : ByteRange 0xF0) (b : ByteRange 0x90 0xC0) (c d : TrailingByteRange) tail :
    WellFormed tail → WellFormed %[a, b, c, d| tail]
  | four₂ (a : ByteRange 0xF1 0xF4) (b c d : TrailingByteRange) tail :
    WellFormed tail → WellFormed %[a, b, c, d| tail]
  | four₃ (a : ByteRange 0xF4) (b : ByteRange 0x80 0x90) (c d : TrailingByteRange) tail :
    WellFormed tail → WellFormed %[a, b, c, d| tail]

end Utf8

/-- **TODO**: remove this definition. -/
partial def CodeUnitSeq.toList {CodeUnit σ} [DecidableEq σ] [CodeUnitSeq CodeUnit σ] (s : σ) :
    List CodeUnit :=
  if h : s = ∅ then [] else
    let (a, τ) := CodeUnitSeq.nextCodeUnit s h
    a::toList τ

/-- [Unicode 8-bit string](https://www.unicode.org/versions/Unicode16.0.0/core-spec/chapter-3/#G32748): A Unicode string containing only UTF-8 code units.

**TODO**: remove `CodeUnitSeq.toList`.
-/
structure Utf8 (σ) [DecidableEq σ] extends CodeUnitSeq UInt8 σ where
  string : σ
  wellFormed : Utf8.WellFormed (CodeUnitSeq.toList string)

/--
[Table 3-6](https://www.unicode.org/versions/Unicode16.0.0/core-spec/chapter-3/#G27288). UTF-8 Bit Distribution

**TODO**: replace `List ScalarValue` with something monadic.
-/
def Utf8.nextScalarValue {σ} [DecidableEq σ] (self : Utf8 σ) : List ScalarValue :=
  match self.toList self.string with
  | [] => []
  | a::tail =>
    if ha : a < 0x80 then
      let tail := suffices WellFormed tail from nextScalarValue tail this
        match hs with
        | .one _ _ h => h
        | .two a ..
        | .three₁ a .. | .three₂ a .. | .three₃ a .. | .three₄ a ..
        | .four₁ a .. | .four₂ a .. | .four₃ a .. => nomatch aux ha a.property.left
      /- 0xxxxxxx	← 0xxxxxxx -/
      tail.cons ⟨a.toUInt32, .inl (Nat.lt_trans ha (by decide))⟩
    else
  match tail with
  | [] => nomatch show False from match hs with | .one a .. => ha a.property.right
  | b::tail =>
    if ha : a < 0xE0 then
      let tail := suffices WellFormed tail from nextScalarValue tail this
        match hs with
        | .two _ _ _ h => h
        | .three₁ a .. | .three₂ a .. | .three₃ a .. | .three₄ a ..
        | .four₁ a .. | .four₂ a .. | .four₃ a .. => nomatch aux ha a.property.left
      /- 00000yyy yyxxxxxx ← 110yyyyy 10xxxxxx -/
      let bits : BitVec 11 := a.toBitVec.extractLsb' 0 5 ++ b.toBitVec.extractLsb' 0 6
      tail.cons ⟨⟨bits.setWidth' (by decide)⟩, sorry⟩
    else
  match tail with
  | [] => nomatch show False from match hs with | .two a .. => ha a.property.right
  | c::tail =>
    if ha : a < 0xF0 then
      let tail := suffices WellFormed tail from nextScalarValue tail this
        match hs with
        | .three₁ _ _ _ _ h | .three₂ _ _ _ _ h | .three₃ _ _ _ _ h | .three₄ _ _ _ _ h => h
        | .four₁ a .. | .four₂ a .. | .four₃ a .. => nomatch aux ha a.property.left
      /- zzzzyyyy yyxxxxxx ← 1110zzzz 10yyyyyy 10xxxxxx -/
      let bits : BitVec 16 :=
        a.toBitVec.extractLsb' 0 4 ++ b.toBitVec.extractLsb' 0 6 ++ c.toBitVec.extractLsb' 0 6
      suffices _ from tail.cons ⟨⟨bits.setWidth' (by decide)⟩, this⟩
      if ha : a = 0xE0 then
        sorry
      else if ha : a < 0xED then
        sorry
      else if ha : a = 0xED then
        sorry
      else
        sorry
    else
  match tail with
  | [] => nomatch show False from match hs with
    | .three₁ a .. | .three₂ a .. | .three₃ a .. | .three₄ a .. =>
      aux a.property.right (Nat.le_of_not_gt ha)
  | d::tail =>
    let tail := suffices WellFormed tail from nextScalarValue tail this
      match hs with
      | .three₁ a .. | .three₂ a .. | .three₃ a .. | .three₄ a .. => sorry
      | .four₁ _ _ _ _ _ h | .four₂ _ _ _ _ _ h | .four₃ _ _ _ _ _ h => h
    /- 000uuuuu zzzzyyyy yyxxxxxx ← 11110uuu 10uuzzzz 10yyyyyy 10xxxxxx -/
    let bits : BitVec 21 :=
      a.toBitVec.extractLsb' 0 3 ++ b.toBitVec.extractLsb' 0 6 ++
      c.toBitVec.extractLsb' 0 6 ++ d.toBitVec.extractLsb' 0 6
    suffices _ from tail.cons ⟨⟨bits.setWidth' (by decide)⟩, this⟩
    if ha : a = 0xF0 then
      sorry
    else if ha : a < 0xF4 then
      sorry
    else if ha : a = 0xF4 then
      sorry
    else
      sorry
where
  aux {x a b : Nat} (ha : x < a) (hb : b ≤ x) (h : a ≤ b := by decide) : False :=
    Nat.lt_le_asymm ha (Nat.le_trans h hb)

section Extra

#check Std.Range
#check Char
#check String
#check String.Pos
#check ByteArray
#check String.iter
#check String.Iterator.curr
#check ByteArray.iter
#check ByteArray.Iterator.curr
#check ForInStep

end Extra

#check Decidable
#check Nat.decEq

/-- The forward iterator `ι` iterates over values of type `α`. -/
class ForwardIterator (α ι) where
  next? : ι → Option (α × ι)

example : ForwardIterator Char String.Iterator where
  next? it := if h : it.hasNext then (it.curr' h, it.next' h) else none

example : ForwardIterator UInt8 ByteArray.Iterator where
  next? it := if h : it.hasNext then (it.curr' h, it.next' h) else none

example α : ForwardIterator α (List α) where
  next? | a::as => (a, as) | [] => none

example α : ForwardIterator α (Array α × Nat) where
  next? | (as, i) => if _ : i < as.size then (as[i], as, i + 1) else none

class InputIterator (α ι) (sentinal : ι) where
  next (it : ι) : it ≠ sentinal → α × ι

example α : InputIterator α (List α) [] where
  next | a::as, _ => (a, as)

example {α ι sentinal} [∀ it, Decidable (it = sentinal)] (self : InputIterator α ι sentinal) :
    ForwardIterator α ι where
  next? it := if h : it = sentinal then none else self.next it h

class Iterator (α ι) where
  good : ι → Prop
  value it : good it → α
  next it : good it → ι

example : Iterator UInt8 ByteArray.Iterator where
  good it := it.hasNext
  value it := it.curr'
  next it := it.next'

example : Iterator Char String.Iterator where
  good it := it.hasNext
  value it := it.curr'
  next it := it.next'

example α : Iterator α (List α) where
  good it := it ≠ []
  value | a::_, _ => a
  next | _::as, _ => as

class Iterator' (α ι) extends Iterator α ι where
  [decGood : ∀ it, Decidable (good it)]
  value? : ι → Option α
  next? : ι → Option ι

def Iterator'.isGood {α ι} [self : Iterator' α ι] (it : ι) : Bool :=
  @decide (self.good it) (self.decGood it)

namespace Utf8

abbrev CodeUnit := UInt8

namespace CodeUnit

def InRange (x lowerBound upperBound : CodeUnit) (_ : lowerBound < 255 := by decide) :=
  lowerBound ≤ x ∧ x < upperBound

abbrev IsTrailing (x : CodeUnit) := InRange x 0x80 0xC0

/-- [Minimal well-formed code unit subsequence](https://www.unicode.org/versions/Unicode16.0.0/core-spec/chapter-3/#G47292): A well-formed Unicode code unit sequence that maps to a single Unicode scalar value.
-/
inductive MinSeq : Prop
  | one a : InRange a 0x00 0x80 → MinSeq
  | two a b : InRange a 0xC2 0xE0 → IsTrailing b → MinSeq
  | three₁ a b c : a = 0xE0 → InRange b 0xA0 0xC0 → IsTrailing c → MinSeq
  | three₂ a b c : InRange a 0xE1 0xED → IsTrailing b → IsTrailing c → MinSeq
  | three₃ a b c : a = 0xED → InRange b 0x80 0xA0 → IsTrailing c → MinSeq
  | three₄ a b c : InRange a 0xEE 0xF0 → IsTrailing b → IsTrailing c → MinSeq
  | four₁ a b c d : a = 0xF0 → InRange b 0x90 0xC0 → IsTrailing c → IsTrailing d → MinSeq
  | four₂ a b c d : InRange a 0xF1 0xF4 → IsTrailing b → IsTrailing c → IsTrailing d → MinSeq
  | four₃ a b c d : a = 0xF4 → InRange b 0x80 0x90 → IsTrailing c → IsTrailing d → MinSeq

mutual
variable {ι} [self : Iterator CodeUnit ι]

inductive Take : ι → Prop
  | zero it : ¬self.good it → Take it
  | more it h : Take1 (self.value it h) (self.next it h) → Take it

inductive Take1 : CodeUnit → ι → Prop
  | one a it : InRange a 0x00 0x80 → Take it → Take1 a it
  | more {a} it h : Take2 a (self.value it h) (self.next it h) → Take1 a it

inductive Take2 : CodeUnit → CodeUnit → ι → Prop
  | two a b it : InRange a 0xC2 0xE0 → IsTrailing b → Take it → Take2 a b it
  | more {a b} it h : Take3 a b (self.value it h) (self.next it h) → Take2 a b it

inductive Take3 : CodeUnit → CodeUnit → CodeUnit → ι → Prop
  | three₁ a b c it : a = 0xE0 → InRange b 0xA0 0xC0 → IsTrailing c → Take it → Take3 a b c it
  | three₂ a b c it : InRange a 0xE1 0xED → IsTrailing b → IsTrailing c → Take it → Take3 a b c it
  | three₃ a b c it : a = 0xED → InRange b 0x80 0xA0 → IsTrailing c → Take it → Take3 a b c it
  | three₄ a b c it : InRange a 0xEE 0xF0 → IsTrailing b → IsTrailing c → Take it → Take3 a b c it
  | more {a b c} it h : Take4 a b c (self.value it h) (self.next it h) → Take3 a b c it

inductive Take4 : CodeUnit → CodeUnit → CodeUnit → CodeUnit → ι → Prop
  | four₁ a b c d it : a = 0xF0 → InRange b 0x90 0xC0 → IsTrailing c → IsTrailing d →
    Take it → Take4 a b c d it
  | four₂ a b c d it : InRange a 0xF1 0xF4 → IsTrailing b → IsTrailing c → IsTrailing d →
    Take it → Take4 a b c d it
  | four₃ a b c d it : a = 0xF4 → InRange b 0x80 0x90 → IsTrailing c → IsTrailing d →
    Take it → Take4 a b c d it

-- inductive Trailing : CodeUnit → ι → Prop
--   | mk x it : InRange x 0x80 0xC0 → Take it → Trailing x it

end

end CodeUnit

example σ [self : ForwardIterator UInt8 σ] : ForwardIterator UInt32 σ :=
  sorry

end Utf8
