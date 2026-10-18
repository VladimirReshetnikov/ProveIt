import GowersSzemeredi.Proofs18EnvelopeBounds
import GowersSzemeredi.Proofs18FejerCubicDiscrepancySide
import GowersSzemeredi.Proofs18StructuralInverseParameters
import GowersSzemeredi.Proofs18FejerIterationParametersSide
import GowersSzemeredi.Proofs18WidthPowerBoundsSide

/-! Declarations of `Proofs18EnvelopeBounds` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- The partition constant, including the factor 32 in the inverse exponent. -/
theorem polyPartConst_mul32_le_pw {X : Real} (hX : 2 ≤ X) (k : Nat) :
    32 * (polynomialPartitionConstant (k + 1 + 1) : Real) ≤
      X ^ (2 ^ (4 * (k + 3) ^ 2 + 4)) :=
  mul32_nat_le_pw hX
    (by simpa only [show k + 1 + 1 + 1 = k + 3 by omega]
      using polyPartConst_le (k + 1 + 1))
    (Nat.lt_two_pow_self (n := 4 * (k + 3) ^ 2 + 4))

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

/-- **Degree three**, from the Fejér cubic bound. -/
theorem envBound_three : EnvBound 3 62 := by
  intro alpha ha ha2
  have ha1 : alpha ≤ 1 := by linarith
  have hX := two_div_ge_two ha ha2
  have hb0 := fejerCubicDiscrepancyParameter_pos ha
  have hb1 := fejerCubicDiscrepancyParameter_le_one ha ha1
  have hs0 := fejerCubicDiscrepancyExponent_pos ha ha1
  refine ⟨fejerCubicDiscrepancyParameter alpha, min (fejerCubicDiscrepancyExponent alpha) 16,
    fejerCubicInverseThreshold alpha,
    (fejer_cubic_function_discrepancy_bound ha ha1).mono le_rfl le_rfl (min_le_left _ _) le_rfl,
    hb0, hb1, lt_min hs0 (by norm_num), min_le_right _ _, ?_, ?_, ?_⟩
  · have h8 : (fejerCubicDiscrepancyParameter alpha)⁻¹ ≤ (fejerCubicDiscrepancyParameter alpha / 8)⁻¹ :=
      inv_anti₀ (by positivity) (by linarith only [hb0])
    have hg := fejer_cubic_gain_inv_le_power ha ha1
    exact (h8.trans hg).trans (pw_natpow hX (Nat.pow_le_pow_right (by norm_num) (by norm_num)))
  · have hs := fejerCubicDiscrepancyExponent_inv_le_exp ha ha1
    rcases min_choice (fejerCubicDiscrepancyExponent alpha) 16 with h | h
    · rw [h]; exact ex_mono hX hs (by norm_num)
    · rw [h]
      exact (show ((16 : Real))⁻¹ ≤ 1 by norm_num).trans (Real.one_le_exp (by positivity))
  · exact (fejerCubicInverseThreshold_le_double_exp ha ha1).trans (le_of_eq rfl)

end LeanProofs.GowersSzemeredi
