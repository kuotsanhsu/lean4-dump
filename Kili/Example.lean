import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

example (n : ℕ) : ∑ i ∈ .range (n + 1), i = n * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    apply (Nat.mul_right_inj two_ne_zero).1
    rw [← Nat.mul_div_assoc _ (even_iff_two_dvd.1 (Nat.even_mul_succ_self (n+1)))]
    rw [mul_add]
    rw [← Nat.mul_div_assoc _ (even_iff_two_dvd.1 (Nat.even_mul_succ_self (n)))]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀]
    ring
