import GowersSzemeredi.Proofs05Downstream

/-! Polynomial dependence of the phase-refinement constant on inverse error. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- An upper bound T on inverse error costs at most T^K in the local
refinement constant, where K is the polynomial partition exponent constant. -/
theorem section5LocalRefinementConstant_le_scaled (k : Nat) (eta T : Real)
    (hη : 0 < eta) (hT : 1 ≤ T) (heta : eta⁻¹ ≤ T) :
    section5LocalRefinementConstant k eta ≤
      section5LocalRefinementConstant k 1 * T ^ polynomialPartitionConstant k := by
  let K := polynomialPartitionConstant k
  let W : Real := polynomialPartitionThreshold k
  let B : Real := max (max W ((4 * Real.pi) ^ K)) ((4 : Real) ^ K)
  have hpow : 1 ≤ T ^ K := one_le_pow₀ hT
  have hB0 : 0 ≤ B := le_trans (by positivity : (0 : Real) ≤ (4 : Real) ^ K) (le_max_right _ _)
  have hB : B ≤ B * T ^ K := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hB0
  have hW : W ≤ B := (le_max_left _ _).trans (le_max_left _ _)
  have hpi : (4 * Real.pi) ^ K ≤ B := (le_max_right _ _).trans (le_max_left _ _)
  have hfour : (4 : Real) ^ K ≤ B := le_max_right _ _
  have hphase : (4 * Real.pi / eta) ^ K ≤ B * T ^ K := by
    calc
      _ ≤ (4 * Real.pi * T) ^ K := by
        apply pow_le_pow_left₀
        · exact div_nonneg (by positivity) hη.le
        · rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left heta (by positivity)
      _ = (4 * Real.pi) ^ K * T ^ K := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hpi (pow_nonneg (zero_le_one.trans hT) _)
  have hmax : max (max W ((4 * Real.pi / eta) ^ K)) ((4 : Real) ^ K) ≤ B * T ^ K :=
    max_le (max_le (hW.trans hB) hphase) (hfour.trans hB)
  have hfourScale : (4 : Real) ≤ 4 * T ^ K := by linarith only [hpow]
  change max (max W ((4 * Real.pi / eta) ^ K)) ((4 : Real) ^ K) + 4 ≤ _
  calc
    _ ≤ B * T ^ K + 4 * T ^ K := add_le_add hmax hfourScale
    _ = section5LocalRefinementConstant k 1 * T ^ K := by
      simp only [section5LocalRefinementConstant, div_one]
      dsimp only [B, W, K]
      ring

end LeanProofs.GowersSzemeredi
