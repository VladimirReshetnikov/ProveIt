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

private theorem prod_one_sub_inv_sq_interval (n : ℕ) :
    ∏ k ∈ Finset.Icc 2 (n + 1), (1 - 1 / (k : ℝ) ^ 2) =
      (n + 2 : ℝ) / (2 * (n + 1)) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih]
    push_cast
    field_simp
    ring

/-- The density contributed by the choices of exponents zero and one stays
at least one half under arbitrarily many prime restrictions. -/
theorem one_half_le_prod_one_sub_inv_sq (T : Finset ℕ) (hT : ∀ p ∈ T, 2 ≤ p) :
    (1 / 2 : ℝ) ≤ ∏ p ∈ T, (1 - 1 / (p : ℝ) ^ 2) := by
  let M := T.sup id
  have hsub : T ⊆ Finset.Icc 2 (M + 1) := fun p hp =>
    Finset.mem_Icc.mpr ⟨hT p hp, (Finset.le_sup (f := id) hp).trans (Nat.le_succ M)⟩
  calc
    (1 / 2 : ℝ) ≤ (M + 2 : ℝ) / (2 * (M + 1)) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    _ = _ := (prod_one_sub_inv_sq_interval M).symm
    _ ≤ _ := by
      apply Finset.prod_le_prod_of_subset_of_le_one hsub
      · intro p hp
        have h : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_Icc.mp hp).1
        apply sub_nonneg.mpr
        rw [div_le_one (by positivity)]
        nlinarith
      · intro p _ _
        exact sub_le_self _ (by positivity)

end GRHArticle.ProgressionFree
