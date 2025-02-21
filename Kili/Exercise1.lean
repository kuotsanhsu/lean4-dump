/-
If $a$ and $r$ are real numbers and $r \neq 1$, then
(1.1)
$$
\sum_{j=0}^{n} a r^{j}=a+a r+a r^{2}+\cdots+a r^{n}=\frac{a r^{n+1}-a}{r-1} .
$$
-/

/-
leanprover/lean4:v4.16.0
require "leanprover-community" / "mathlib" @ git "v4.16.0"
-/
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

open Finset

example {a r : ℝ} (n : ℕ) (h : r ≠ 1) : ∑ i ∈ range (n+1), a * r^i = (a * r^(n+1) - a) / (r-1) := by
  induction n with
  | zero =>
    simp
    rw [←mul_sub_one a r, mul_div_cancel_right₀ a hr]
  | succ n ih =>
    rw [sum_range_succ, ih]
    apply (mul_left_inj' hr).mp
    rw [add_mul, div_mul_cancel₀ _ hr, div_mul_cancel₀ _ hr]
    ring
where
  hr : r - 1 ≠ 0 := by
    intro (h' : r - 1 = 0)
    suffices r = 1 from h this
    apply congrArg (· + 1) at h'
    simpa using h'
