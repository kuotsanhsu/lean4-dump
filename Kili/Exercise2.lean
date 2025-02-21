/-
Let $n$ and $k$ be nonnegative integers with $k \leqslant n$. Then
(i ) $\binom{n}{0}=\binom{n}{n}=1$
(ii) $\binom{n}{k}=\binom{n}{n-k}$.
-/

/-
leanprover/lean4:v4.16.0
require "leanprover-community" / "mathlib" @ git "v4.16.0"
-/
import Mathlib.Data.Nat.Choose.Basic

variable (n k : ℕ) (h : k ≤ n)
example : n.choose 0 = 1 := n.choose_zero_right
example : n.choose n = 1 := n.choose_self
example : n.choose k = n.choose (n - k) := (n.choose_symm h).symm
