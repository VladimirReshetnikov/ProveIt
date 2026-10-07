import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem clm_norm_le_card_mul_of_basis {I E : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (A : (I → ℝ) →L[ℝ] E)
    {M : ℝ} (hM : 0 ≤ M) (hA : ∀ i, ‖A (Pi.single i 1)‖ ≤ M) :
    ‖A‖ ≤ Fintype.card I * M := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  have hsum : A x = ∑ i, (x i) • A (Pi.single i 1) := by
    calc
      A x = A (∑ i, Pi.single i (x i)) :=
        congrArg A (LinearMap.sum_single_apply (fun _ : I => ℝ) x).symm
      _ = ∑ i, A (Pi.single i (x i)) := map_sum A _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        have hs : Pi.single i (x i) = (x i) • (Pi.single i (1 : ℝ) : I → ℝ) := by
          rw [← Pi.single_smul]
          simp
        rw [hs, map_smul]
  rw [hsum]
  calc
    _ ≤ ∑ i, ‖(x i) • A (Pi.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : I, ‖x‖ * M := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul (norm_le_pi_norm x i) (hA i) (norm_nonneg _) (norm_nonneg x)
    _ = _ := by simp [mul_comm, mul_left_comm, mul_assoc]

theorem clm_norm_le_card_mul_of_entries {I O : Type*}
    [Fintype I] [DecidableEq I] [Fintype O]
    (A : (I → ℝ) →L[ℝ] (O → ℝ)) {M : ℝ} (hM : 0 ≤ M)
    (hA : ∀ i o, |A (Pi.single i 1) o| ≤ M) : ‖A‖ ≤ Fintype.card I * M := by
  apply clm_norm_le_card_mul_of_basis A hM
  intro i
  apply (pi_norm_le_iff_of_nonneg hM).mpr
  intro o
  simpa only [Real.norm_eq_abs] using hA i o

end Erdos3

end

end OAI
