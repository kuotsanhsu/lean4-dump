/-
We define a function recursively for all positive integers $n$ by $f(1)=1$, $f(2)=5$, and for $n>2, f(n+1)=f(n)+2 f(n-1)$. Show that $f(n)=$ $2^{n}+(-1)^{n}$, using the second principle of mathematical induction.
-/

/-
leanprover/lean4:v4.16.0
require "leanprover-community" / "mathlib" @ git "v4.16.0"
-/
import Mathlib.Tactic.Ring

def f : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => f (n + 1) + 2 * f n

example : f 1 = 1 := rfl
example : f 2 = 5 := rfl
example : ∀ n > 2, f (n + 1) = f n + 2 * f (n - 1) | _ + 1, _ => rfl

theorem F : ∀ n, (f n : ℤ) = 2 ^ n + (-1) ^ n
  | 0 | 1 => rfl
  | n + 2 =>
    calc (f (n + 1) + 2 * f n : ℤ)
      _ = 2 ^ (n + 1) + (-1) ^ (n + 1) + 2 * (2 ^ n + (-1) ^ n) := by rw [F (n + 1), F n]
      _ = 2 ^ (n + 2) + (-1) ^ (n + 2) := by ring
