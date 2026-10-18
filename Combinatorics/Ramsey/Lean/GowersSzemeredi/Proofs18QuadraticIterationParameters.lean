import GowersSzemeredi.Proofs18QuadraticIterationStep
import Mathlib.Analysis.Real.Pi.Bounds

/-! Fixed-power bounds on the inverse density gain, length exponent, and
length prefactor needed to compare the closed iteration threshold.

`intervalQuadraticUniformityParameter_inv_upper` is in
`Proofs18QuadraticIterationParametersSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem quadratic_interval_parameters_inv_upper {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    (quadraticDiscrepancyParameter alpha)⁻¹ ≤ (2 / alpha) ^ (12381 : Nat) ∧
    (quadraticDiscrepancyParameter alpha / 8)⁻¹ ≤ (2 / alpha) ^ (12384 : Nat) ∧
    (quadraticDiscrepancyExponent alpha / 16)⁻¹ ≤ (2 / alpha) ^ (24748 : Nat) ∧
    (quadraticDiscrepancyParameter alpha /
      (8 * boundaryRefinementConstant (quadraticDiscrepancyParameter alpha / 64)))⁻¹ ≤
        (8 * section5LocalRefinementConstant 1 1) * (2 / alpha) ^ (210541 : Nat) := by
  have hu : 2 ≤ 2 / alpha := (le_div_iff₀ hα).mpr (by linarith)
  have hτ : 0 < quadraticDiscrepancyParameter alpha := by
    unfold quadraticDiscrepancyParameter; positivity
  have hτinv : (quadraticDiscrepancyParameter alpha)⁻¹ ≤ (2 / alpha) ^ (12381 : Nat) := by
    have hτeq : quadraticDiscrepancyParameter alpha =
        (2 : Real) ^ (-(19 : Int)) * alpha ^ 2 * (alpha / 2) ^ (12359 : Nat) / 2 := by
      unfold quadraticDiscrepancyParameter
      generalize (alpha / 2) ^ (12359 : Nat) = t
      norm_num
      ring
    rw [hτeq, inv_div, div_eq_mul_inv, pow_succ' (2 / alpha) 12380]
    exact mul_le_mul hu (quadratic_parameters_inv_upper hα hαone).1 (by positivity) (by positivity)
  have hσ : 0 < quadraticDiscrepancyExponent alpha :=
    div_pos (quadratic_frequency_exponent_bounds hα hαone).1 (by norm_num)
  refine ⟨hτinv, ?_, ?_, interval_length_factor_inv_le_scaled (n := 12381) hu hτ hτinv⟩
  · rw [inv_div, div_eq_mul_inv, show (12384 : Nat) = 3 + 12381 from rfl, pow_add]
    exact mul_le_mul (le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hu 3)) hτinv
      (inv_nonneg.mpr hτ.le) (by positivity)
  · rw [inv_div, div_eq_mul_inv, show (24748 : Nat) = 4 + 24744 from rfl, pow_add]
    exact mul_le_mul (le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hu 4))
      (quadratic_parameters_inv_upper hα hαone).2 (inv_nonneg.mpr hσ.le) (by positivity)

theorem quadratic_interval_length_factor_le_one {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    quadraticDiscrepancyParameter alpha /
      (8 * boundaryRefinementConstant (quadraticDiscrepancyParameter alpha / 64)) ≤ 1 := by
  have hτone : quadraticDiscrepancyParameter alpha ≤ 1 := by
    have h2 : alpha ^ 2 ≤ 1 := pow_le_one₀ hα.le hαone
    have hp : (alpha / 2) ^ (12359 : Nat) ≤ 1 :=
      pow_le_one₀ (by positivity) (by linarith)
    have hc : (2 : Real) ^ (-(20 : Int)) ≤ 1 := by norm_num
    unfold quadraticDiscrepancyParameter
    calc
      _ ≤ 1 * 1 * 1 := mul_le_mul
        (mul_le_mul hc h2 (by positivity) (by norm_num)) hp (by positivity) (by norm_num)
      _ = _ := by norm_num
  have hC := section5LocalRefinementConstant_ge_four 1
    (4 * Real.pi * (quadraticDiscrepancyParameter alpha / 64))
  change quadraticDiscrepancyParameter alpha / (8 * section5LocalRefinementConstant 1 _) ≤ 1
  apply (div_le_one (by positivity : (0 : Real) < 8 * section5LocalRefinementConstant 1 _)).mpr
  linarith

/-- The finite-interval uniformity parameter is at most the fourth power of
the initial density, including the zero-density endpoint. -/
theorem intervalQuadraticUniformityParameter_le_pow_four {delta : Real}
    (hδ : 0 ≤ delta) (hδone : delta ≤ 1) : intervalQuadraticUniformityParameter delta ≤ delta ^ 4 := by
  let a := delta ^ 4 / 32768
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have haδ : a ≤ delta ^ 4 := div_le_self (pow_nonneg hδ _) (by norm_num)
  have haone : a ≤ 1 := haδ.trans (pow_le_one₀ hδ hδone)
  change a ^ 8 ≤ _
  calc
    _ = a ^ 7 * a := pow_succ a 7
    _ ≤ 1 * a := mul_le_mul_of_nonneg_right (pow_le_one₀ ha haone) ha
    _ = a := one_mul _
    _ ≤ _ := haδ

end LeanProofs.GowersSzemeredi
