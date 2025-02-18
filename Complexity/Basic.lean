import Mathlib.Tactic.Ring

/-- f is O(g) -/
def bigO (f g : Nat → Nat) : Prop :=
  ∃ N C : Nat, ∀ n : Nat, n ≥ N → f n ≤ C * g n

/-- f ∈ O(g) -/
def BigO (g : Nat → Nat) := {f : Nat → Nat // bigO f g}

theorem simple : bigO (fun n => n) (fun n => n * n) :=
  suffices ∀ n, n ≤ 1 * (n * n) from ⟨0, 1, fun n _ => this n⟩
  by
    intro n
    simp
    induction n with
    | zero => trivial
    | succ n hi =>
      calc n + 1
        _ ≤ (n * n + n) + (n + 1) := Nat.le_add_left ..
        _ = (n * n + n) + n + 1 := (Nat.add_assoc ..).symm
        _ = (n + 1) * (n + 1) := by rw [
          Nat.add_mul,
          Nat.one_mul,
          Nat.mul_add,
          Nat.mul_one,
          ←Nat.add_assoc (n * n + n),
        ]
        _ ≤ (n + 1) * (n + 1) := Nat.le.refl

example : ∀ n : Nat, n ≤ 1 * (n * n)
  | 0 => by trivial
  | n + 1 =>
    calc n + 1
      _ ≤ (n * n + n) + (n + 1) := Nat.le_add_left ..
      _ = 1 * ((n + 1) * (n + 1)) := by ring

def linear (n : Nat) := n
def quadratic (n : Nat) := n * n

example : bigO linear quadratic := simple
example : BigO quadratic := ⟨linear, simple⟩
#check (⟨linear, simple⟩ : BigO quadratic)
example : bigO quadratic quadratic :=
  ⟨0, 1, fun n _ => show n * n ≤ 1 * (n * n) by simp⟩
example : ¬bigO quadratic linear
  | ⟨N, C, h⟩ =>
    have : (N + C + 1) * (N + C + 1) ≤ C * (N + C + 1) :=
      suffices N + C + 1 ≥ N from h (N + C + 1) this
      calc N
        _ ≤ N + C := N.le_add_right C
        _ ≤ N + C + 1 := (N + C).le_succ
    have : N + C + 1 ≤ C := Nat.le_of_mul_le_mul_right this (N + C).succ_pos
    have : N + 1 ≤ 0 := Nat.le_of_add_le_add_left <|
      calc C + (N + 1)
        _ = N + C + 1 := by ring
        _ ≤ C := this
    absurd this N.not_succ_le_zero

example (f₁ f₂ g : Nat → Nat) : bigO f₁ g → bigO f₂ g →
  bigO (fun n => f₁ n + f₂ n) g := sorry

instance : Add (Nat → Nat) where
  add f₁ f₂ n := f₁ n + f₂ n

theorem bigO.add (f₁ f₂ g : Nat → Nat) : bigO f₁ g → bigO f₂ g → bigO (f₁ + f₂) g
  | ⟨N₁, C₁, (h₁ : ∀ n : Nat, n ≥ N₁ → f₁ n ≤ C₁ * g n)⟩,
    ⟨N₂, C₂, (h₂ : ∀ n : Nat, n ≥ N₂ → f₂ n ≤ C₂ * g n)⟩ =>
    ⟨N₁ + N₂, C₁ + C₂, fun n (hn : n ≥ N₁ + N₂) =>
      show f₁ n + f₂ n ≤ (C₁ + C₂) * g n from
      have h₁ : f₁ n ≤ C₁ * g n := h₁ n <|
        calc n
          _ ≥ N₁ + N₂ := hn
          _ ≥ N₁ := Nat.le_add_right ..
      have h₂ : f₂ n ≤ C₂ * g n := h₂ n <|
        calc n
          _ ≥ N₁ + N₂ := hn
          _ ≥ N₂ := Nat.le_add_left ..
      calc f₁ n + f₂ n
        _ ≤ C₁ * g n + C₂ * g n := Nat.add_le_add h₁ h₂
        _ = (C₁ + C₂) * g n := Nat.add_mul C₁ C₂ (g n) |>.symm
    ⟩

example (f₁ f₂ g : Nat → Nat) : bigO f₁ g → bigO f₂ g → bigO (f₁ + f₂) g
  | ⟨N₁, C₁, (h₁ : ∀ n : Nat, n ≥ N₁ → f₁ n ≤ C₁ * g n)⟩,
    ⟨N₂, C₂, (h₂ : ∀ n : Nat, n ≥ N₂ → f₂ n ≤ C₂ * g n)⟩ =>
    ⟨max N₁ N₂, C₁ + C₂, fun n (hn : n ≥ max N₁ N₂) =>
      show f₁ n + f₂ n ≤ (C₁ + C₂) * g n from
      have h₁ : f₁ n ≤ C₁ * g n := h₁ n <|
        calc n
          _ ≥ max N₁ N₂ := hn
          _ ≥ N₁ := le_max_left ..
      have h₂ : f₂ n ≤ C₂ * g n := h₂ n <|
        calc n
          _ ≥ max N₁ N₂ := hn
          _ ≥ N₂ := le_max_right ..
      calc f₁ n + f₂ n
        _ ≤ C₁ * g n + C₂ * g n := Nat.add_le_add h₁ h₂
        _ = (C₁ + C₂) * g n := Nat.add_mul C₁ C₂ (g n) |>.symm
    ⟩

instance (g : Nat → Nat) : Add (BigO g) where
  add | ⟨f₁, (h₁ : bigO f₁ g)⟩, ⟨f₂, (h₂ : bigO f₂ g)⟩ => ⟨f₁ + f₂, bigO.add f₁ f₂ g h₁ h₂⟩

theorem bigO.trans (f g h : Nat → Nat) : bigO f g → bigO g h → bigO f h
  | ⟨M, C, p⟩, ⟨N, D, q⟩ => ⟨max M N, C * D, fun n r =>
    calc f n
      _ ≤ C * g n := p n <|
        calc n
        _ ≥ max M N := r
        _ ≥ M := le_max_left ..
      _ ≤ C * (D * h n) := Nat.mul_le_mul_left C <| q n <|
        calc n
        _ ≥ max M N := r
        _ ≥ N := le_max_right ..
      _ = C * D * h n := Nat.mul_assoc .. |>.symm
    ⟩

theorem bigO.refl (f : Nat → Nat) : bigO f f :=
  ⟨0, 1, fun n _ => show f n ≤ 1 * f n by simp⟩

/-- f is Θ(g) -/
def Theta (f g : Nat → Nat) : Prop :=
  ∃ a b N : Nat, ∀ n : Nat, n ≥ N → a * f n ≥ g n ∧ f n ≤ b * g n

theorem Theta.refl (f : Nat → Nat) : Theta f f :=
  ⟨1, 1, 0, fun n _ => ⟨by simp, by simp⟩⟩

theorem Theta.symm {f g : Nat → Nat} : Theta f g → Theta g f
  | ⟨a, b, N, h⟩ => ⟨b, a, N, fun n hn => (h n hn).symm⟩

theorem Theta.trans {f g h : Nat → Nat} : Theta f g → Theta g h → Theta f h
  | ⟨a, b, M, p⟩, ⟨c, d, N, q⟩ => ⟨c * a, b * d, max M N, fun n r =>
    have k₁ : h n ≤ c * a * f n :=
      calc h n
        _ ≤ c * g n := And.left ∘ q n <|
          calc n
          _ ≥ max M N := r
          _ ≥ N := le_max_right ..
        _ ≤ c * (a * f n) := Nat.mul_le_mul_left c <| And.left ∘ p n <|
          calc n
          _ ≥ max M N := r
          _ ≥ M := le_max_left ..
        _ = c * a * f n := Nat.mul_assoc .. |>.symm
    have k₂ : f n ≤ b * d * h n :=
      calc f n
        _ ≤ b * g n := And.right ∘ p n <|
          calc n
          _ ≥ max M N := r
          _ ≥ M := le_max_left ..
        _ ≤ b * (d * h n) := Nat.mul_le_mul_left b <| And.right ∘ q n <|
          calc n
          _ ≥ max M N := r
          _ ≥ N := le_max_right ..
        _ = b * d * h n := Nat.mul_assoc .. |>.symm
    ⟨k₁, k₂⟩
  ⟩

instance Theta.setoid : Setoid (Nat → Nat) where
  r := Theta
  iseqv.refl := Theta.refl
  iseqv.symm := Theta.symm
  iseqv.trans := Theta.trans

def Complexity := Quotient Theta.setoid
