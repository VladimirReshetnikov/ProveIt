import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A uniform lower bound for finite squarefree Euler factors

The product over every integer from two to a cutoff telescopes. Omitting
factors increases the product, giving a positive lower bound uniform in
the finite set of primes used to approximate Rankin's density.
-/

namespace GRHArticle.ProgressionFree

private theorem prod_one_sub_inv_sq_interval (Y n : ℕ) (hY : 0 < Y) :
    ∏ k ∈ Finset.Icc (Y + 1) (Y + n), (1 - 1 / (k : ℝ) ^ 2) =
      (Y : ℝ) / (Y + 1) * ((Y + n + 1 : ℝ) / (Y + n)) := by
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hY
  induction n with
  | zero => simp; field_simp
  | succ n ih =>
    rw [show Y + n.succ = (Y + n) + 1 by omega, Finset.prod_Icc_succ_top (by omega), ih]
    push_cast
    field_simp
    ring

/-- The contribution from any finite set of integers above the cutoff is
at least the telescoping product over the full tail. -/
theorem le_prod_one_sub_inv_sq_of_lt (Y : ℕ) (hY : 0 < Y) (T : Finset ℕ)
    (hT : ∀ p ∈ T, Y < p) :
    (Y : ℝ) / (Y + 1) ≤ ∏ p ∈ T, (1 - 1 / (p : ℝ) ^ 2) := by
  let M := T.sup id
  have hsub : T ⊆ Finset.Icc (Y + 1) (Y + M) := fun p hp =>
    Finset.mem_Icc.mpr ⟨hT p hp, (Finset.le_sup (f := id) hp).trans (Nat.le_add_left M Y)⟩
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hY
  calc
    (Y : ℝ) / (Y + 1) ≤ (Y : ℝ) / (Y + 1) * ((Y + M + 1 : ℝ) / (Y + M)) := by
      apply le_mul_of_one_le_right (by positivity)
      rw [one_le_div (by positivity)]
      linarith
    _ = _ := (prod_one_sub_inv_sq_interval Y M hY).symm
    _ ≤ _ := by
      apply Finset.prod_le_prod_of_subset_of_le_one hsub
      · intro p hp
        have h : 2 ≤ p := by have := (Finset.mem_Icc.mp hp).1; omega
        have hr : (2 : ℝ) ≤ p := by exact_mod_cast h
        apply sub_nonneg.mpr
        rw [div_le_one (by positivity)]
        nlinarith
      · intro p _ _
        exact sub_le_self _ (by positivity)

/-- The density contributed by the choices of exponents zero and one stays
at least one half under arbitrarily many prime restrictions. -/
theorem one_half_le_prod_one_sub_inv_sq (T : Finset ℕ) (hT : ∀ p ∈ T, 2 ≤ p) :
    (1 / 2 : ℝ) ≤ ∏ p ∈ T, (1 - 1 / (p : ℝ) ^ 2) := by
  convert le_prod_one_sub_inv_sq_of_lt 1 (by decide) T hT using 1
  norm_num

end GRHArticle.ProgressionFree
