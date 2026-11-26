import IPRADerivations.Analysis.Gamma.GaussianEulerIntegralGammaIdentification
import IPRADerivations.Core.OrderCertificates

/-!
# The actual rescaled exponent for positive rational power charts

For r=e/f, the exponent z/B is rescaled to the native value
(scale f z)/(B*e). Separate numerical upper and lower bounds on r
supply a new disk and a positive real-part margin, independently of
the denominator used for r.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingParameter

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale normSq oneCode normSq_scale)
open GaussianRootAlgebra (equal_of_values re_mul im_mul re_scale im_scale re_one im_one)
open GaussianRationalHorner
  (ofGaussian ofGaussian_represents ofGaussian_canonical qmul qmul_canonical qmul_represents positive_product
    canonical_unique represents_congr represents_rescale)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def source (z R B A e f L U : PTm n) : Fm PTm n :=
  GaussianEulerIntegralGammaIdentification.source z R B A ⋏
    (le one e ⋏ (le one f ⋏ (le one L ⋏ (le one U ⋏ (le f (L*e) ⋏ le e (U*f))))))
def scaled (z f : PTm n) : PTm n := scale f z

theorem original_rescaled_value (z B e f : PTm n) (hB : Γ ⊢[PRAAx] le one B) (he : Γ ⊢[PRAAx] le one e) :
    Γ ⊢[PRAAx] qmul (ofGaussian z B) (ofGaussian (scale f oneCode) e) ≐ ofGaussian (scaled z f) (B*e) := by
  have D := positive_product _ _ hB he
  apply canonical_unique _ _ _ _ (qmul_canonical _ _) (ofGaussian_canonical _ _ D) D
    (hrv := ofGaussian_represents _ _ D)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := qmul_represents _ _ _ _ _ _ hB he
    (ofGaussian_represents z B hB) (ofGaussian_represents (scale f oneCode) e he))
  apply equal_of_values <;> simp only [scaled,re_mul,im_mul,re_scale,im_scale,re_one,im_one] <;> ring

/-- Multiplication by the original chart exponent recovers the unscaled parameter. -/
theorem rescaled_times_power (z B e f : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (he : Γ ⊢[PRAAx] le one e) (hf : Γ ⊢[PRAAx] le one f) :
    Γ ⊢[PRAAx] qmul (ofGaussian (scaled z f) (B*e)) (ofGaussian (scale e oneCode) f) ≐ ofGaussian z B := by
  have hs := positive_product B e hB he
  have ht := positive_product (B*e) f hs hf
  have left := qmul_represents _ _ _ _ _ _ hs hf
    (ofGaussian_represents (scaled z f) (B*e) hs) (ofGaussian_represents (scale e oneCode) f hf)
  have right := represents_rescale _ _ _ (e*f) (ofGaussian_represents z B hB)
  apply canonical_unique _ _ (scale (e*f) z) ((B*e)*f) (qmul_canonical _ _) (ofGaussian_canonical _ _ hB) ht
  · apply represents_congr (.eqRefl _) ?_ (.eqRefl _) left
    apply equal_of_values <;> simp only [scaled,re_mul,im_mul,re_scale,im_scale,re_one,im_one] <;> ipra_simps <;> ring
  · exact represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _) (by ipra_ring) right

theorem original_rescaled_source (z R B A e f L U : PTm n) (hs : Γ ⊢[PRAAx] source z R B A e f L U) :
    Γ ⊢[PRAAx] GaussianEulerIntegralGammaIdentification.source (scaled z f) (L*R) (B*e) (U*A) := by
  have original := hs.andE₁
  have lower := original.andE₁
  have he := hs.andE₂.andE₁
  have hL := hs.andE₂.andE₂.andE₂.andE₁
  have hU := hs.andE₂.andE₂.andE₂.andE₂.andE₁
  have hRatioLow := hs.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
  have hRatioHigh := hs.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂
  have hD := positive_product _ _ lower.andE₂.andE₁.andE₁ he
  have hdisk : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (scaled z f) ((L*R)*(B*e)) := by
    have size := mul_le_mul_right (R*B) hRatioLow
    have sq := AnalyticNumberTheory.PhiLower.le_mul_mono size size
    have raw := mul_le_mul_right (f*f) lower.andE₂.andE₁.andE₂
    have left : Γ ⊢[PRAAx] normSq z*(f*f) ≐ normSq (scaled z f) :=
      (mul_comm _ _).eqTrans (normSq_scale f z).eqSymm
    have first : Γ ⊢[PRAAx] le (normSq (scaled z f)) ((f*(R*B))*(f*(R*B))) :=
      le_congr left (by ipra_ring) raw
    exact le_trans first (le_congr (.eqRefl _) (by ipra_ring) sq)
  let gap := PolynomialBisection.slack (ZT.ofNat B) (ZT.ofNat A*ComplexLogarithmRemainder.re z)
  have positive : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.realLower (scaled z f) (U*A) (B*e) := by
    have left := zle_toZ lower.andE₂.andE₂
    have right := natEq (eq_add_of_le hRatioHigh)
    unfold GaussianEulerLowerPowerCoefficients.realLower at left ⊢
    apply zle_of_toZ (U*f*gap+B*monus (U*f) e)
    simp only [scaled,re_scale,ZT.toZ_mul,ZT.toZ_ofNat] at left ⊢
    dsimp only [gap,PolynomialBisection.slack]
    ipra_simps
    linear_combination (𝔞 U)*(𝔞 f)*left-𝔞 B*right
  exact .andI (.andI (positive_product _ _ hU lower.andE₁) (.andI (.andI hD hdisk) positive))
    (positive_product _ _ hL original.andE₂)

theorem actual_power_scaling_parameter_source_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      GaussianEulerIntegralGammaIdentification.source (scaled (var 0) (var 5)) (var 6*var 1)
        (var 2*var 4) (var 7*var 3)) :=
  closeUniv 8 (.impI (original_rescaled_source _ _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_rescaled_gamma_parameter_times_chart_power_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((le one (var 1) ⋏ (le one (var 2) ⋏ le one (var 3))) ⟶
        qmul (ofGaussian (scaled (var 0) (var 3)) (var 1*var 2)) (ofGaussian (scale (var 2) oneCode) (var 3))
          ≐ ofGaussian (var 0) (var 1)) :=
  closeUniv 4 (.impI (rescaled_times_power _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingParameter
