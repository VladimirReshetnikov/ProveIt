import GowersSzemeredi.Proofs18CoverThresholdsSharp

/-! **Theorem 18.2 and Corollary 18.7 with `L + 4` at lengths `L ≤ 5`**
(Notes L.16d).

The short-length block of `Proofs18CoverThresholdsSharp` with `5` replaced
by `4` (generated). The corpus's explicit thresholds (Roth's
`exp(exp(10¹²·δ⁻¹))` for `L ≤ 3`; towers with `2^21` and `2^73` on top for
`L = 4, 5`) stay below the threshold with `L + 4` on top:
`2^(4+4) = 256 ≥ 21` and `2^(5+4) = 512 ≥ 73`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem roth_threshold_le_szemerediThresholdAt_four (k : Nat) {delta : Real}
    (hδ : 0 < delta) (hδ2 : delta ≤ 1 / 2) :
    Real.exp (Real.exp (1000000000000 * delta⁻¹)) ≤ szemerediThresholdAt 4 delta k := by
  exact (roth_threshold_le_szemerediThresholdAt_three k hδ hδ2).trans
    (szemerediThresholdAt_mono (by norm_num) hδ (by linarith))

theorem quadraticIntervalClosedThreshold_le_at_four {delta : Real}
    (hδ : 0 < delta) (hδhalf : delta ≤ 1 / 2) :
    quadraticIntervalClosedThreshold delta ≤ szemerediThresholdAt 4 delta 4 := by
  exact (quadraticIntervalClosedThreshold_le_at_three hδ hδhalf).trans
    (szemerediThresholdAt_mono (by norm_num) hδ (by linarith))

theorem fejerFiveTermThreshold_le_at_four {delta : Real}
    (hδ : 0 < delta) (hδhalf : delta ≤ 1 / 2) :
    fejerFiveTermThreshold delta ≤ szemerediThresholdAt 4 delta 5 := by
  exact (fejerFiveTermThreshold_le_at_three hδ hδhalf).trans
    (szemerediThresholdAt_mono (by norm_num) hδ (by linarith))

/-- **Theorem 18.2 with `L + 4` at every length `L ≤ 5`.** -/
theorem theorem_18_2_L4_le_five {k : Nat} (hk : k ≤ 5) : Theorem182AtSharp 4 k := by
  exact (theorem_18_2_L3_le_five hk).mono (by norm_num)

/-- **Corollary 18.7 with `L + 4` at every length `L ≤ 5`.** -/
theorem corollary_18_7_L4_le_five {k : Nat} (hk : k ≤ 5) : Corollary187AtSharp 4 k :=
  (theorem_18_2_L4_le_five hk).corollary_18_7

end LeanProofs.GowersSzemeredi
