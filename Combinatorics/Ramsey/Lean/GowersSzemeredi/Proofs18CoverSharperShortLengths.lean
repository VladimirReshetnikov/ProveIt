import GowersSzemeredi.Proofs18RothThresholdBounds
import GowersSzemeredi.Proofs18ShortLengthsFromCubic
import GowersSzemeredi.Proofs18SzemerediSmallLengths
import GowersSzemeredi.Proofs05HighCorrelationAssembly
import GowersSzemeredi.Proofs05HighCorrelationScale
import GowersSzemeredi.Proofs05ThresholdFreeScale

/-! Legacy scalar threshold comparisons for short lengths.

The canonical offset-three short-length theorem is imported from
`Proofs18ShortLengthsFromCubic`. This module retains the Roth, quadratic
and dedicated five-term threshold comparisons and their offset-six
specializations for existing clients. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem roth_threshold_le_szemerediThresholdAt_three (k : Nat) {delta : Real}
    (hδ : 0 < delta) (hδ2 : delta ≤ 1 / 2) :
    Real.exp (Real.exp (1000000000000 * delta⁻¹)) ≤ szemerediThresholdAt 3 delta k := by
  unfold szemerediThresholdAt
  apply roth_exp_exp_le_two_tower (n := k + 3) ?_ (by omega)
  rw [← one_div, le_div_iff₀ hδ]
  linarith only [hδ2]

theorem quadraticIntervalClosedThreshold_le_at_three {delta : Real}
    (hδ : 0 < delta) (hδhalf : delta ≤ 1 / 2) :
    quadraticIntervalClosedThreshold delta ≤ szemerediThresholdAt 3 delta 4 := by
  apply (quadraticIntervalClosedThreshold_le_explicit_tower hδ hδhalf).trans
  have hu : 1 ≤ delta⁻¹ := (one_le_inv₀ hδ).mpr (by linarith)
  have hsource : (2 : Real) ^ ((2 : Real) ^ (delta⁻¹ ^ ((2 : Nat) ^ 128))) =
      szemerediThresholdAt 3 delta 4 := by
    unfold szemerediThresholdAt
    rw [show (2 : Real) ^ (4 + 3 : Nat) = 128 by norm_num]
    simp only [← Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
  rw [← hsource]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact pow_le_pow_right₀ hu (Nat.pow_le_pow_right (by norm_num) (by norm_num : 21 ≤ 128))

theorem fejerFiveTermThreshold_le_at_three {delta : Real}
    (hδ : 0 < delta) (hδhalf : delta ≤ 1 / 2) :
    fejerFiveTermThreshold delta ≤ szemerediThresholdAt 3 delta 5 := by
  apply (fejerFiveTermThreshold_le_explicit_tower hδ hδhalf).trans
  have hu : 1 ≤ delta⁻¹ := (one_le_inv₀ hδ).mpr (by linarith)
  have hsource : (2 : Real) ^ ((2 : Real) ^ (delta⁻¹ ^ ((2 : Nat) ^ 256))) =
      szemerediThresholdAt 3 delta 5 := by
    unfold szemerediThresholdAt
    rw [show (2 : Real) ^ (5 + 3 : Nat) = 256 by norm_num]
    simp only [← Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
  rw [← hsource]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact pow_le_pow_right₀ hu (Nat.pow_le_pow_right (by norm_num) (by norm_num : 73 ≤ 256))

/-- Roth's explicit threshold lies below the threshold with `k + 6` on top. -/
theorem roth_threshold_le_szemerediThresholdAt_six (k : Nat) {delta : Real}
    (hδ : 0 < delta) (hδ2 : delta ≤ 1 / 2) :
    Real.exp (Real.exp (1000000000000 * delta⁻¹)) ≤ szemerediThresholdAt 6 delta k := by
  exact (roth_threshold_le_szemerediThresholdAt_three k hδ hδ2).trans
    (szemerediThresholdAt_mono (by norm_num) hδ (by linarith))

theorem quadraticIntervalClosedThreshold_le_at_six {delta : Real}
    (hδ : 0 < delta) (hδhalf : delta ≤ 1 / 2) :
    quadraticIntervalClosedThreshold delta ≤ szemerediThresholdAt 6 delta 4 := by
  exact (quadraticIntervalClosedThreshold_le_at_three hδ hδhalf).trans
    (szemerediThresholdAt_mono (by norm_num) hδ (by linarith))

theorem fejerFiveTermThreshold_le_at_six {delta : Real}
    (hδ : 0 < delta) (hδhalf : delta ≤ 1 / 2) :
    fejerFiveTermThreshold delta ≤ szemerediThresholdAt 6 delta 5 := by
  exact (fejerFiveTermThreshold_le_at_three hδ hδhalf).trans
    (szemerediThresholdAt_mono (by norm_num) hδ (by linarith))

/-- **Theorem 18.2 with `L + 6` at every length `L ≤ 5`.** -/
theorem theorem_18_2_L6_le_five {k : Nat} (hk : k ≤ 5) : Theorem182AtSharp 6 k := by
  exact (theorem_18_2_L3_le_five hk).mono (by norm_num)

/-- **Corollary 18.7 with `L + 6` at every length `L ≤ 5`.** -/
theorem corollary_18_7_L6_le_five {k : Nat} (hk : k ≤ 5) : Corollary187AtSharp 6 k :=
  (theorem_18_2_L6_le_five hk).corollary_18_7

end LeanProofs.GowersSzemeredi
