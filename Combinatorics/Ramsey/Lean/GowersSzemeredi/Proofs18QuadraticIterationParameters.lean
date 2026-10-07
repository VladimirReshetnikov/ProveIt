import GowersSzemeredi.Proofs18QuadraticIterationStep
import Mathlib.Analysis.Real.Pi.Bounds

/-! Fixed-power bounds on the inverse density gain, length exponent, and
length prefactor needed to compare the closed iteration threshold. -/
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
  let u := 2 / alpha
  let tau := quadraticDiscrepancyParameter alpha
  let beta := (2 : Real) ^ (-(19 : Int)) * alpha ^ 2 * (alpha / 2) ^ (12359 : Nat)
  have hu : 2 ≤ u := (le_div_iff₀ hα).mpr (by linarith)
  have huone : 1 ≤ u := by linarith
  have hτ : 0 < tau := by dsimp [tau, quadraticDiscrepancyParameter]; positivity
  have hβ : 0 < beta := by dsimp [beta]; positivity
  have hCpos := section5LocalRefinementConstant_pos 1 1
  have hτeq : tau = beta / 2 := by
    dsimp [tau, beta, quadraticDiscrepancyParameter]
    generalize (alpha / 2) ^ (12359 : Nat) = t
    norm_num
    ring
  have hτinv : tau⁻¹ ≤ u ^ (12381 : Nat) := by
    calc
      _ = 2 * beta⁻¹ := by rw [hτeq, inv_div, div_eq_mul_inv]
      _ ≤ 2 * u ^ (12380 : Nat) := mul_le_mul_of_nonneg_left
        (quadratic_parameters_inv_upper hα hαone).1 (by norm_num)
      _ ≤ u * u ^ (12380 : Nat) := mul_le_mul_of_nonneg_right hu (by positivity)
      _ = _ := (pow_succ' u 12380).symm
  have h8 : (8 : Real) ≤ u ^ (3 : Nat) := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 2) hu 3
    norm_num at hp
    exact hp
  have h16 : (16 : Real) ≤ u ^ (4 : Nat) := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 2) hu 4
    norm_num at hp
    exact hp
  have hσ : 0 < quadraticDiscrepancyExponent alpha :=
    div_pos (quadratic_frequency_exponent_bounds hα hαone).1 (by norm_num)
  refine ⟨hτinv, ?_, ?_, ?_⟩
  · calc
      _ = 8 * tau⁻¹ := by rw [inv_div, div_eq_mul_inv]
      _ ≤ u ^ (3 : Nat) * u ^ (12381 : Nat) :=
        mul_le_mul h8 hτinv (inv_nonneg.mpr hτ.le) (by positivity)
      _ = _ := by rw [← pow_add]
  · calc
      _ = 16 * (quadraticDiscrepancyExponent alpha)⁻¹ := by rw [inv_div, div_eq_mul_inv]
      _ ≤ u ^ (4 : Nat) * u ^ (24744 : Nat) :=
        mul_le_mul h16 (quadratic_parameters_inv_upper hα hαone).2
          (inv_nonneg.mpr hσ.le) (by positivity)
      _ = _ := by rw [← pow_add]
  · let eta := 4 * Real.pi * (tau / 64)
    have hη : 0 < eta := by dsimp [eta]; positivity
    have hηlower : tau / 16 ≤ eta := by
      have hm := mul_le_mul_of_nonneg_right (show 1 ≤ Real.pi by linarith [Real.pi_gt_three]) hτ.le
      dsimp [eta]
      nlinarith
    have hηinv : eta⁻¹ ≤ u ^ (12385 : Nat) := by
      calc
        _ ≤ (tau / 16)⁻¹ := (inv_le_inv₀ hη (by positivity)).mpr hηlower
        _ = 16 * tau⁻¹ := by rw [inv_div, div_eq_mul_inv]
        _ ≤ u ^ (4 : Nat) * u ^ (12381 : Nat) :=
          mul_le_mul h16 hτinv (inv_nonneg.mpr hτ.le) (by positivity)
        _ = _ := by rw [← pow_add]
    have hC := section5LocalRefinementConstant_le_scaled 1 eta (u ^ (12385 : Nat))
      hη (one_le_pow₀ huone) hηinv
    have hK : polynomialPartitionConstant 1 = 16 := by norm_num [polynomialPartitionConstant, Nat.factorial]
    rw [hK, ← pow_mul] at hC
    change (tau / (8 * section5LocalRefinementConstant 1 eta))⁻¹ ≤ _
    calc
      _ = (8 * section5LocalRefinementConstant 1 eta) * tau⁻¹ := by rw [inv_div, div_eq_mul_inv]
      _ ≤ (8 * (section5LocalRefinementConstant 1 1 * u ^ (12385 * 16 : Nat))) * u ^ (12381 : Nat) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hC (by norm_num)) hτinv
          (inv_nonneg.mpr hτ.le) (by positivity)
      _ = _ := by
        rw [mul_assoc 8, mul_assoc, ← pow_add, ← mul_assoc]

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

/-- All density dependence of the fixed uniformity parameter is polynomial. -/
theorem intervalQuadraticUniformityParameter_inv_upper {delta : Real}
    (hδ : 0 < delta) (hδone : delta ≤ 1) :
    (intervalQuadraticUniformityParameter delta)⁻¹ ≤ (2 / delta) ^ (120 : Nat) ∧
      2 / intervalQuadraticUniformityParameter delta ≤ (2 / delta) ^ (121 : Nat) := by
  have hα := intervalQuadraticUniformityParameter_pos hδ
  have hd : 1 ≤ delta⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ hδ).mpr (by simpa using hδone)
  have hbase : (delta ^ 4 / 32768)⁻¹ ≤ (2 / delta) ^ (15 : Nat) := by
    calc
      _ = 32768 * (delta⁻¹) ^ (4 : Nat) := by rw [inv_div, div_eq_mul_inv, inv_pow]
      _ ≤ 32768 * (delta⁻¹) ^ (15 : Nat) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hd (by norm_num : 4 ≤ 15)) (by norm_num)
      _ = _ := by rw [div_pow, div_eq_mul_inv, inv_pow]; norm_num
  have hinv : (intervalQuadraticUniformityParameter delta)⁻¹ ≤ (2 / delta) ^ (120 : Nat) := by
    unfold intervalQuadraticUniformityParameter
    rw [← inv_pow]
    calc
      _ ≤ ((2 / delta) ^ (15 : Nat)) ^ (8 : Nat) := pow_le_pow_left₀ (by positivity) hbase _
      _ = _ := by rw [← pow_mul]
  refine ⟨hinv, ?_⟩
  have hu : 2 ≤ 2 / delta := (le_div_iff₀ hδ).mpr (by linarith)
  calc
    _ = 2 * (intervalQuadraticUniformityParameter delta)⁻¹ := div_eq_mul_inv _ _
    _ ≤ (2 / delta) * (2 / delta) ^ (120 : Nat) :=
      mul_le_mul hu hinv (by positivity) (by positivity)
    _ = _ := (pow_succ' _ 120).symm

end LeanProofs.GowersSzemeredi
