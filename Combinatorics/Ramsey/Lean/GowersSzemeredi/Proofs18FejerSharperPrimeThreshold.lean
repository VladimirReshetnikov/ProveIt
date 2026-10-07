import GowersSzemeredi.Proofs18LogarithmicPowerEnvelope
import GowersSzemeredi.Proofs18FejerPrimeThresholdEnvelope

/-! Sharper bounds for the unchanged cubic prime-model threshold. The fixed
quadratic partition constant is absorbed at the correct logarithmic level. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem fejerCubicPrimeModelThreshold_le_double_exp_of_double
    {alpha T A : Real} (hα : 0 < alpha) (hαone : alpha ≤ 1) (hA : 256 ≤ A)
    (hF : (2 / alpha) ^ ((2 : Nat) ^ 54) ≤ A)
    (hT : T ≤ Real.exp (Real.exp A)) :
    fejerCubicPrimeModelThreshold alpha T ≤ Real.exp (Real.exp (3 * A)) := by
  have hA0 : 0 ≤ A := by linarith only [hA]
  have hAe : A ≤ Real.exp A := by have h := Real.add_one_le_exp A; linarith only [h]
  have h2 : (2 : Real) ≤ Real.exp A := by linarith only [hA, hAe]
  have h12 : (12 : Real) ≤ Real.exp (Real.exp A) :=
    (by linarith only [hA] : (12 : Real) ≤ A).trans (real_le_double_exp A)
  have hmax : max 2 T ≤ Real.exp (Real.exp A) := max_le (by linarith only [h12]) hT
  have hC : 12 * max 2 T ≤ Real.exp (Real.exp (2 * A)) := by
    calc
      _ ≤ Real.exp (Real.exp A) * Real.exp (Real.exp A) :=
        mul_le_mul h12 hmax (le_trans (by norm_num : (0 : Real) ≤ 2) (le_max_left _ _)) (by positivity)
      _ = Real.exp (2 * Real.exp A) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by
        calc
          _ ≤ Real.exp A * Real.exp A := mul_le_mul_of_nonneg_right h2 (by positivity)
          _ = _ := by rw [← Real.exp_add]; congr 1; ring)
  have hx : 1 ≤ 2 / alpha := (le_div_iff₀ hα).mpr (by linarith only [hαone])
  have he : 0 < fejerCubicLocalizationExponent alpha := by
    unfold fejerCubicLocalizationExponent; positivity
  have heI : (fejerCubicLocalizationExponent alpha)⁻¹ ≤ Real.exp A :=
    (fejerCubicLocalizationExponent_inv_le_exp hα).trans (Real.exp_le_exp.mpr
      ((pow_le_pow_right₀ hx (by norm_num : (2 : Nat) ^ 53 ≤ (2 : Nat) ^ 54)).trans hF))
  have hp := positivePowerThreshold_one_le_double_exp he.le hC heI
  rw [show 2 * A + A = 3 * A by ring] at hp
  have hA3 : A ≤ 3 * A := by linarith only [hA0]
  unfold fejerCubicPrimeModelThreshold
  refine max_le (hA.trans (hA3.trans (real_le_double_exp _))) (max_le ?_ hp)
  exact (section13FejerOddSquareThreshold_le_double_exp hα hαone).trans
    (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (hF.trans hA3)))

/-- The full twisted threshold has inner reciprocal-power exponent 2^55;
the older 2^324 estimate remains valid but is no longer needed downstream. -/
theorem fejerCubicTwistedThreshold_le_double_exp_sharp {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    fejerCubicTwistedThreshold alpha ≤
      Real.exp (Real.exp ((2 / alpha) ^ ((2 : Nat) ^ 55))) := by
  let x := 2 / alpha
  let A := x ^ ((2 : Nat) ^ 54)
  have hx : 2 ≤ x := (le_div_iff₀ hα).mpr (by linarith only [hαone])
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hA : 256 ≤ A := by
    calc
      _ = (2 : Real) ^ (8 : Nat) := by norm_num
      _ ≤ x ^ (8 : Nat) := pow_le_pow_left₀ (by norm_num) hx _
      _ ≤ _ := pow_le_pow_right₀ hx1 (by norm_num : (8 : Nat) ≤ (2 : Nat) ^ 54)
  have hquad : quadraticExponentialThreshold (fejerCubicLocalQuadraticParameter alpha) ≤
      Real.exp (Real.exp A) := by
    apply (quadraticExponentialThreshold_fejer_le_exp hα hαone).trans
    apply Real.exp_le_exp.mpr
    exact (pow_two_pow_le_exp_pow_succ hx 323).trans (Real.exp_le_exp.mpr
      (pow_le_pow_right₀ hx1 (by norm_num : (324 : Nat) ≤ (2 : Nat) ^ 54)))
  have h4 : (4 : Real) ≤ Real.exp (Real.exp A) :=
    (by linarith only [hA] : (4 : Real) ≤ A).trans (real_le_double_exp _)
  have h := fejerCubicPrimeModelThreshold_le_double_exp_of_double hα hαone hA le_rfl (max_le h4 hquad)
  apply h.trans
  apply Real.exp_le_exp.mpr (Real.exp_le_exp.mpr _)
  have hx2 : (3 : Real) ≤ x ^ (2 : Nat) := by nlinarith only [hx]
  calc
    3 * A ≤ x ^ (2 : Nat) * x ^ ((2 : Nat) ^ 54) := mul_le_mul_of_nonneg_right hx2 (by positivity)
    _ = x ^ (2 + (2 : Nat) ^ 54) := (pow_add _ _ _).symm
    _ ≤ _ := pow_le_pow_right₀ hx1 (by norm_num : 2 + (2 : Nat) ^ 54 ≤ (2 : Nat) ^ 55)

end LeanProofs.GowersSzemeredi
