import RegExp.Basic

namespace RegExp
variable {α}

def size (r : RegExp α) : Nat :=
  suffices Nat from this.succ
  match r with
  | .nothing | ε | .single _ => 0
  | .star r => r.size
  | .append r₁ r₂ | .union r₁ r₂ => r₁.size + r₂.size

example : @size α .nothing = 1 := rfl
example : @size α ε = 1 := rfl
example (a : α) : size (.single a) = 1 := rfl
example {n} (r : RegExp α) : r.size = n → size r* = n + 1
  | rfl => rfl
example {n₁ n₂} (r₁ r₂ : RegExp α) : r₁.size = n₁ → r₂.size = n₂ → size (r₁ ++ r₂) = n₁ + n₂ + 1
  | rfl, rfl => rfl
example {n₁ n₂} (r₁ r₂ : RegExp α) : r₁.size = n₁ → r₂.size = n₂ → size (r₁ ∪ r₂) = n₁ + n₂ + 1
  | rfl, rfl => rfl

abbrev L (r : RegExp α) := {s : List α // s =~ r}

instance setoid : Setoid (RegExp α) where
  r r₁ r₂ := ∀ s, s =~ r₁ ↔ s =~ r₂
  iseqv.refl _ _ := .rfl
  iseqv.symm h s := (h s).symm
  iseqv.trans h₁ h₂ s := (h₁ s).trans (h₂ s)

variable {s : List α}

theorem accept_nothing : ¬s =~ ∅ := nofun
instance : Subsingleton (@L α ∅) where
  allEq | _, ⟨_, h⟩ => absurd h accept_nothing

instance : Inhabited (@L α ε) where
  default := ⟨[], empty⟩
instance : Subsingleton (@L α ε) where
  allEq | ⟨_, empty⟩, ⟨_, empty⟩ => rfl
theorem accept_empty : s =~ ε ↔ [] = s := ⟨fun | empty => rfl, fun | rfl => empty⟩

variable {a b : α}

instance : Inhabited (L (.single a)) where
  default := ⟨[a], single⟩
instance : Subsingleton (L (.single a)) where
  allEq | ⟨_, single⟩, ⟨_, single⟩ => rfl
theorem accept_single : s =~ a ↔ [a] = s := ⟨fun | single => rfl, fun | rfl => single⟩
theorem accept_single_unique : [a] =~ b ↔ a = b :=
  ⟨fun h => match accept_single.mp h with | rfl => rfl, fun | rfl => single⟩
theorem accept_single_head (h : a::s =~ b) : a = b := match accept_single.mp h with | rfl => rfl
theorem accept_single_tail (h : a::s =~ b) : [] = s := match accept_single.mp h with | rfl => rfl

theorem accept_starEmpty : s =~ ∅* ↔ [] = s := ⟨fun | starEmpty => rfl, fun | rfl => starEmpty⟩
example : (∅* : RegExp α) ≈ ε
  | _ => ⟨fun | starEmpty => empty, fun | empty => starEmpty⟩

variable {r : RegExp α}

theorem accept_star (h : s =~ r) : s =~ r* := s.append_nil ▸ h.starAppend starEmpty
example : r** ≈ r*
  | s => ⟨_, accept_star⟩
