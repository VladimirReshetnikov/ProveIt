import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import OAI.Combinatorics.Progressions.Estimates.FiniteReciprocalTenthTail

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem sum_positiveOrders_eq_Ioc (f : ℕ → ℝ) (B R : ℕ) :
    (∑ a : Fin R, if B < a.val + 1 then f (a.val + 1) else 0) =
      ∑ a ∈ Finset.Ioc B R, f a := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih]
    by_cases hBR : B ≤ R
    · rw [Finset.sum_Ioc_succ_top hBR]
      simp only [show B < R + 1 by omega, ite_true]
    · have hRB : R + 1 ≤ B := by omega
      simp [Finset.Ioc_eq_empty_of_le hRB, Finset.Ioc_eq_empty_of_le (by omega : R ≤ B),
        show ¬ B < R + 1 by omega]

theorem finite_positiveOrder_reciprocal_tail (B R : ℕ) (hB : 0 < B) :
    (∑ a : Fin R, if B < a.val + 1 then 1 / ((a.val + 1 : ℕ) : ℝ) ^ 2 else 0) ≤
      1 / (B : ℝ) := by
  rw [sum_positiveOrders_eq_Ioc (fun a => 1 / (a : ℝ) ^ 2) B R]
  exact finite_reciprocal_square_tail (Finset.Ioc B R) hB
    (fun _ h => (Finset.mem_Ioc.mp h).1)

theorem character_root_power_cancel (a C : ℝ) (ha : 0 < a) (n : ℕ) (hn : 0 < n) :
    a ^ n * (C / a ^ (1 / (n : ℝ))) ^ (n * (n + 2)) =
      C ^ (n * (n + 2)) / a ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hroot : (a ^ (1 / (n : ℝ))) ^ n = a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    rw [one_div_mul_cancel hn', Real.rpow_one]
  have hpow : (a ^ (1 / (n : ℝ))) ^ (n * (n + 2)) = a ^ (n + 2) := by
    rw [pow_mul, hroot]
  rw [div_pow, hpow, pow_add]
  field_simp

theorem finite_character_reciprocal_tail (B R n : ℕ) (hB : 0 < B) (hn : 0 < n)
    (C : ℝ) (hC : 0 ≤ C) :
    (∑ a : Fin R, if B < a.val + 1 then
      ((a.val + 1 : ℕ) : ℝ) ^ n *
        (C / ((a.val + 1 : ℕ) : ℝ) ^ (1 / (n : ℝ))) ^ (n * (n + 2)) else 0) ≤
      C ^ (n * (n + 2)) / (B : ℝ) := by
  have heq : (∑ a : Fin R, if B < a.val + 1 then
      ((a.val + 1 : ℕ) : ℝ) ^ n *
        (C / ((a.val + 1 : ℕ) : ℝ) ^ (1 / (n : ℝ))) ^ (n * (n + 2)) else 0) =
      C ^ (n * (n + 2)) *
        ∑ a : Fin R, if B < a.val + 1 then 1 / ((a.val + 1 : ℕ) : ℝ) ^ 2 else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : B < a.val + 1
    · simp only [h, ite_true]
      rw [character_root_power_cancel _ C (by positivity) n hn]
      ring
    · simp only [h, ite_false, mul_zero]
  rw [heq, div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left (finite_positiveOrder_reciprocal_tail B R hB) (pow_nonneg hC _)

end Erdos3

end

end OAI
