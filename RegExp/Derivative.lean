import RegExp.Basic

namespace RegExp
universe u
variable {α : Type u}

section
variable {a b : α} {s : List α} {r r₁ r₂ : RegExp α}

theorem accept_nothing : ¬ s =~ ∅ := nofun

theorem accept_empty : s =~ ε → s = []
  | empty => rfl

theorem accept_single : s =~ a → [a] = s
  | single => rfl

example : a::s =~ b → a = b
  | h => match accept_single h with | rfl => rfl

example : a::s =~ b → s = []
  | h => match accept_single h with | rfl => rfl

example : s =~ ∅* → s = []
  | starEmpty => rfl

example : s =~ r → s =~ r*
  | h => s.append_nil ▸ (starAppend h starEmpty)

theorem app_exists : s =~ r₁ ++ r₂ → ∃ s₁ s₂, s₁ ++ s₂ = s ∧ s₁ =~ r₁ ∧ s₂ =~ r₂
  | append h₁ h₂ => ⟨_, _, rfl, h₁, h₂⟩

theorem union_disj : s =~ r₁ ∪ r₂ → s =~ r₁ ∨ s =~ r₂
  | unionL h => .inl h
  | unionR h => .inr h

theorem cons_accept_append : a::s =~ r₁ ++ r₂ →
    (∃ s₁ s₂, s = s₁ ++ s₂ ∧ a::s₁ =~ r₁ ∧ s₂ =~ r₂) ∨ ([] =~ r₁ ∧ a::s =~ r₂) := by
  generalize et : a::s = t
  intro
  | append (s₁ := []) h₁ h₂ => exact .inr ⟨h₁, h₂⟩
  | append (s₁ := b::s₁) h₁ h₂ => cases et; exact .inl ⟨_, _, rfl, h₁, h₂⟩

instance decAcceptEmpty : (r : RegExp α) → Decidable ([] =~ r)
  | .nothing => isFalse accept_nothing
  | ε => isTrue empty
  | (a : α) => isFalse (nomatch accept_single ·)
  | .append r₁ r₂ =>
    match r₁.decAcceptEmpty, r₂.decAcceptEmpty with
    | isTrue h₁, isTrue h₂ => isTrue (append h₁ h₂)
    | isFalse (hn : ¬[] =~ r₁), _
    | _, isFalse (hn : ¬[] =~ r₂) => isFalse fun h =>
      match app_exists h with
      | ⟨[], [], rfl, (h₁ : [] =~ r₁), (h₂ : [] =~ r₂)⟩ => hn ‹_›
  | .union r₁ r₂ =>
    match r₁.decAcceptEmpty, r₂.decAcceptEmpty with
    | isFalse hn₁, isFalse hn₂ => isFalse fun h => (union_disj h).elim hn₁ hn₂
    | isTrue h, _ => isTrue (unionL h)
    | _, isTrue h => isTrue (unionR h)
  | _* => isTrue starEmpty

theorem starRec {motive : ∀ {s}, s =~ r* → Prop}
    (base : motive starEmpty)
    (ind : ∀ {s s'}, (h : s =~ r) → (h' : s' =~ r*) → motive h' → motive (starAppend h h'))
    {s} (hh : s =~ r*) : motive hh := by
  generalize er : r* = r; rw [er] at hh
  induction hh
  case empty | single | append | unionL | unionR => nomatch er
  case starEmpty => exact base
  case starAppend s s' _ h h' _ ih =>
    cases er; cases s
    case nil => exact ih hh rfl
    case cons => exact ind h h' (ih h' rfl)

theorem cons_accept_star : a::s =~ r* → ∃ s₁ s₂, s = s₁ ++ s₂ ∧ a::s₁ =~ r ∧ s₂ =~ r* := by
  generalize et : a::s = t
  intros h
  induction h using starRec
  case base => nomatch et
  case ind s₁ s₂ h₁ h₂ ih =>
    cases s₁
    case nil => exact ih et
    case cons => cases et; exact ⟨_, _, rfl, h₁, h₂⟩

end

variable [DecidableEq α] (a : α)

/--
- [Brzozowski derivative](https://en.wikipedia.org/wiki/Brzozowski_derivative)
- [Myhill–Nerode theorem](https://en.wikipedia.org/wiki/Myhill%E2%80%93Nerode_theorem)
-/
def derive : RegExp α → RegExp α
  | .nothing | ε => ∅
  | (b : α) => if a = b then ε else ∅
  | .append r₁ r₂ => if [] =~ r₁ then (r₁.derive ++ r₂) ∪ r₂.derive else r₁.derive ++ r₂
  | .union r₁ r₂ => r₁.derive ∪ r₂.derive
  | r* => r.derive ++ r*

theorem derives (r : RegExp α) (s : List α) : a::s =~ r ↔ s =~ derive a r :=
  ⟨mp, mpr⟩
where
  mp {s : List α} : {r : RegExp α} → a::s =~ r → s =~ r.derive a
    | .nothing, h => absurd h accept_nothing
    | ε, h => nomatch accept_empty h
    | (b : α), h => match accept_single h with | rfl => trans empty (if_pos rfl).symm
    | .append r₁ r₂, h =>
      match cons_accept_append h with
      | .inl ⟨_, _, h, h₁, h₂⟩ =>
        have : s =~ r₁.derive a ++ r₂ := h.symm ▸ append (mp h₁) h₂
        if e : [] =~ r₁ then trans (unionL this) (if_pos e).symm else trans this (if_neg e).symm
      | .inr ⟨e, h₂⟩ => trans (unionR (mp h₂)) (if_pos e).symm
    | .union _ _, h => (union_disj h).elim (unionL ∘ mp) (unionR ∘ mp)
    | _*, h => match cons_accept_star h with | ⟨_, _, h, h₁, h₂⟩ => h ▸ append (mp h₁) h₂
  mpr {s : List α} : {r : RegExp α} → s =~ r.derive a → a::s =~ r
    | (b : α), h =>
      if e : a = b then
        match trans h (if_pos e) with | empty => e ▸ single
      else
        nomatch trans h (if_neg e)
    | .append r _, h =>
      if e : [] =~ r then
        match trans h (if_pos e) with
        | unionL (append h₁ h₂) => append (mpr h₁) h₂
        | unionR h₂ => append e (mpr h₂)
      else
        match trans h (if_neg e) with
        | append h₁ h₂ => append (mpr h₁) h₂
    | .union _ _, unionL h => unionL (mpr h)
    | .union _ _, unionR h => unionR (mpr h)
    | _*, append h₁ h₂ => starAppend (mpr h₁) h₂

instance decAccept (r : RegExp α) : (s : List α) → Decidable (s =~ r)
  | [] => decAcceptEmpty r
  | a::s =>
    match (r.derive a).decAccept s with
    | isTrue h => isTrue (derives.mpr a h)
    | isFalse hn => isFalse (hn ∘ derives.mp a)

end RegExp
