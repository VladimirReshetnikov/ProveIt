import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Exponential bounds and growth constants

This module isolates the elementary final step in a growth-constant proof.
For a nonnegative integer sequence `A`, its `growthSup` is the supremum of
all positive-index real nth roots.  When supermultiplicativity supplies the
usual Fekete limit, this is exactly the conventional growth constant.  The
result below needs only a pointwise exponential majorant.
-/

namespace LeanProofs.KlarnerConstant

/-- The set of positive-index nth roots of an integer-valued sequence. -/
def rootSet (A : ℕ → ℕ) : Set ℝ :=
  {x | ∃ n : ℕ, n ≠ 0 ∧ x = (A n : ℝ) ^ (n⁻¹ : ℝ)}

/-- The supremum formulation of an exponential growth constant. -/
noncomputable def growthSup (A : ℕ → ℕ) : ℝ :=
  sSup (rootSet A)

theorem rootSet_nonempty (A : ℕ → ℕ) : (rootSet A).Nonempty := by
  refine ⟨(A 1 : ℝ), 1, one_ne_zero, ?_⟩
  simp

/-- A pointwise bound `A n ≤ μⁿ` bounds every positive-index nth root. -/
theorem root_le_of_le_pow {A : ℕ → ℕ} {μ : ℝ} (hμ : 0 ≤ μ)
    (hA : ∀ n : ℕ, (A n : ℝ) ≤ μ ^ n) {n : ℕ} (hn : n ≠ 0) :
    (A n : ℝ) ^ (n⁻¹ : ℝ) ≤ μ := by
  calc
    (A n : ℝ) ^ (n⁻¹ : ℝ) ≤ (μ ^ n) ^ (n⁻¹ : ℝ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (hA n) (by positivity)
    _ = μ := Real.pow_rpow_inv_natCast hμ hn

/-- A pointwise exponential majorant bounds the supremal growth rate. -/
theorem growthSup_le_of_le_pow {A : ℕ → ℕ} {μ : ℝ} (hμ : 0 ≤ μ)
    (hA : ∀ n : ℕ, (A n : ℝ) ≤ μ ^ n) :
    growthSup A ≤ μ := by
  apply csSup_le (rootSet_nonempty A)
  rintro x ⟨n, hn, rfl⟩
  exact root_le_of_le_pow hμ hA hn

/-- The exact rational value of the improved decimal coefficient. -/
theorem improvedBase_eq : (9047 / 2000 : ℝ) = 4.5235 := by
  norm_num

end LeanProofs.KlarnerConstant
