import GowersSzemeredi.Proofs18FejerReciprocalBudgets
import GowersSzemeredi.Proofs18FejerCubicTwistedDiscrepancy
import GowersSzemeredi.Proofs18QuadraticNumericalConstant

/-! Conventional double-exponential modulus bounds for every local prime
model and the assembled cubic twisted discrepancy partition. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

set_option exponentiation.threshold 512 in
/-- The actual local quadratic inverse threshold is single exponential in
an explicit fixed power of the original cubic uniformity parameter. -/
theorem quadraticExponentialThreshold_fejer_le_exp {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    quadraticExponentialThreshold (fejerCubicLocalQuadraticParameter alpha) ≤
      Real.exp ((2 / alpha) ^ ((2 : Nat) ^ 323)) := by
  let x := 2 / alpha
  have hx : 2 ≤ x := (le_div_iff₀ hα).mpr (by linarith only [hαone])
  have hx1 : 1 ≤ x := by linarith only [hx]
  have h1 := section5LocalRefinementConstant_pos 1 1
  have hC : 4 + 6 * section5LocalRefinementConstant 2 1 ≤ x ^ ((2 : Nat) ^ 322) := by
    have hc : 4 + 6 * section5LocalRefinementConstant 2 1 ≤ quadraticIterationLogBudgetConstant + 1 := by
      unfold quadraticIterationLogBudgetConstant
      linarith only [h1]
    exact (hc.trans quadraticIterationLogBudgetConstant_upper).trans
      (pow_le_pow_left₀ (by norm_num) hx _)
  have ha := fejerCubicLocalQuadraticParameter_pos hα
  have hbase := two_div_fejerCubicLocalQuadraticParameter_le_power hα hαone
  have hP := pow_le_pow_left₀ (by positivity : 0 ≤ 2 / fejerCubicLocalQuadraticParameter alpha)
    hbase (12380 * 2048 + 24744)
  rw [← pow_mul] at hP
  unfold quadraticExponentialThreshold
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ x ^ ((2 : Nat) ^ 322) * x ^ (((2 : Nat) ^ 43 + 1) * (12380 * 2048 + 24744)) :=
      mul_le_mul hC hP (by positivity) (by positivity)
    _ = x ^ ((2 : Nat) ^ 322 + ((2 : Nat) ^ 43 + 1) * (12380 * 2048 + 24744)) := (pow_add _ _ _).symm
    _ ≤ _ := pow_le_pow_right₀ hx1 (by norm_num)

/-- A single-exponential local modulus budget keeps the prime-model
construction double exponential, including its full Fourier input. -/
theorem fejerCubicPrimeModelThreshold_le_double_exp {alpha T A : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) (hA : 256 ≤ A)
    (hF : (2 / alpha) ^ ((2 : Nat) ^ 54) ≤ A) (hT : T ≤ Real.exp A) :
    fejerCubicPrimeModelThreshold alpha T ≤ Real.exp (Real.exp (4 * A)) := by
  let e := (1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 53))
  have hA0 : 0 ≤ A := by linarith only [hA]
  have hAe : A ≤ Real.exp A := by have h := Real.add_one_le_exp A; linarith only [h]
  have h12 : (12 : Real) ≤ Real.exp A := by linarith only [hA, hAe]
  have h2 : (2 : Real) ≤ Real.exp A := by linarith only [h12]
  have hmax : max 2 T ≤ Real.exp A := max_le h2 hT
  have hC : 12 * max 2 T ≤ Real.exp (2 * A) := by
    have h := mul_le_mul h12 hmax (le_trans (by norm_num : (0 : Real) ≤ 2) (le_max_left _ _)) (Real.exp_pos _).le
    simpa only [← Real.exp_add, show A + A = 2 * A by ring] using h
  have he : 0 < e := Real.rpow_pos_of_pos (by norm_num) _
  have hx : 1 ≤ 2 / alpha := (le_div_iff₀ hα).mpr (by linarith only [hαone])
  have hsmall : (2 / alpha) ^ ((2 : Nat) ^ 53) ≤ A :=
    (pow_le_pow_right₀ hx (by norm_num : (2 : Nat) ^ 53 ≤ (2 : Nat) ^ 54)).trans hF
  have heI : e⁻¹ ≤ Real.exp (1 * A) := by
    rw [one_mul]
    exact (fejerCubicLocalizationExponent_inv_le_exp hα).trans (Real.exp_le_exp.mpr hsmall)
  have h1 : (1 : Real)⁻¹ ≤ Real.exp (1 * A) := by
    simpa only [inv_one, one_mul] using Real.one_le_exp_iff.mpr hA0
  have hp := positivePowerThreshold_le_double_exp (C := 12 * max 2 T) zero_lt_one he.le hA0
    (by norm_num : (0 : Real) ≤ 2) (by norm_num : (0 : Real) ≤ 1) hC h1 heI
  norm_num only [show (2 + 1 + 1 : Real) = 4 by norm_num] at hp
  have h4 : A ≤ 4 * A := by linarith only [hA0]
  have hlarge : (256 : Real) ≤ Real.exp (Real.exp (4 * A)) :=
    hA.trans (h4.trans (real_le_double_exp _))
  unfold fejerCubicPrimeModelThreshold
  refine max_le hlarge (max_le ?_ hp)
  exact (section13FejerOddSquareThreshold_le_double_exp hα hαone).trans
    (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (hF.trans h4)))

set_option exponentiation.threshold 512 in
/-- The entire cubic twisted discrepancy construction works above a
conventional double exponential in the original uniformity parameter. -/
theorem fejerCubicTwistedThreshold_le_double_exp {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    fejerCubicTwistedThreshold alpha ≤ Real.exp (Real.exp ((2 / alpha) ^ ((2 : Nat) ^ 324))) := by
  let x := 2 / alpha
  let A := x ^ ((2 : Nat) ^ 323)
  have hx : 2 ≤ x := (le_div_iff₀ hα).mpr (by linarith only [hαone])
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hA : 256 ≤ A := by
    calc
      _ = (2 : Real) ^ (8 : Nat) := by norm_num
      _ ≤ x ^ (8 : Nat) := pow_le_pow_left₀ (by norm_num) hx _
      _ ≤ _ := pow_le_pow_right₀ hx1 (by norm_num : (8 : Nat) ≤ (2 : Nat) ^ 323)
  have hF : x ^ ((2 : Nat) ^ 54) ≤ A := pow_le_pow_right₀ hx1 (by norm_num : (2 : Nat) ^ 54 ≤ (2 : Nat) ^ 323)
  have h4 : (4 : Real) ≤ Real.exp A := by
    have hh := Real.add_one_le_exp A
    linarith only [hh, hA]
  have hT := max_le h4 (quadraticExponentialThreshold_fejer_le_exp hα hαone)
  have h := fejerCubicPrimeModelThreshold_le_double_exp hα hαone hA hF hT
  apply h.trans
  apply Real.exp_le_exp.mpr (Real.exp_le_exp.mpr _)
  have hx2 : (4 : Real) ≤ x ^ (2 : Nat) := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 2) hx 2
    norm_num at hh
    exact hh
  calc
    _ ≤ x ^ (2 : Nat) * x ^ ((2 : Nat) ^ 323) := mul_le_mul_of_nonneg_right hx2 (by positivity)
    _ = x ^ (2 + (2 : Nat) ^ 323) := (pow_add _ _ _).symm
    _ ≤ _ := pow_le_pow_right₀ hx1 (by norm_num : 2 + (2 : Nat) ^ 323 ≤ (2 : Nat) ^ 324)

end LeanProofs.GowersSzemeredi
