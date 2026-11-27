import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Convergence.ResidualBounds.GaussianLogGammaEulerResidualDomain
import IPRADerivations.Analysis.Trigonometry.Arctangent.Inverse.Sampling.GaussianArctangentClippedParameter
import IPRADerivations.Analysis.RationalArithmetic.Grids.GaussianRationalGridRounding
import IPRADerivations.Foundations.EigenvalueBound
import IPRADerivations.Probability.ClipLaws
import IPRADerivations.Probability.RepresentedExpectation

/-!
# Rational geometry of right-half-plane argument increments

For two signed Gaussian numerators at one denominator, the Euclidean
step controls both coordinate increments. If the imaginary signs are
opposite it controls the sum of their heights. On either arctangent
chart, and across the chart boundary, this gives a ratio bound `2H/M`,
where `M` is any positive common lower bound for the real numerators.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneArgumentIncrementGeometry

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Foundations.EigenvalueBound (ad_congr)
open LeanProofs.IPRA.Foundations.GapDecision (zabs zabs_congr zabs_neg zabs_tri)
open LeanProofs.IPRA.Probability.ClipLaws (ad_triangle)
open LeanProofs.IPRA.Probability.MedianWeighted (ad_le_of ad_mul le_add_ad)
open LeanProofs.IPRA.Probability.RepresentedExpectation (ad_le_add)
open LeanProofs.IPRA.Probability.Variance (ad)
open ComplexLogarithmRemainder (re im bounded eval_re_code eval_im_code)
open GaussianArctangentClippedParameter (radius_of_cleared)
open GaussianCoordinateRadius (native_coordinates)
open GaussianL1 (abs_ofNat)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianRootAlgebra (sub re_sub im_sub)
open GaussianRightHalfPlaneLogarithmOffset (signedImag)
open RationalArithmetic (select_zero select_one)
open RationalCubeMidpoint (fraction)
open RationalValueBounds (radius)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def step (A B neg a b sign : PTm n) : PTm n := sub (native a b sign) (native A B neg)

def signBit (neg : PTm n) : Fm PTm n := neg ≐ zero ⋎ neg ≐ one

def oppositeBits (neg sign : PTm n) : Fm PTm n :=
  (neg ≐ zero ⋏ sign ≐ one) ⋎ (neg ≐ one ⋏ sign ≐ zero)

private theorem imag_zero (B neg : PTm n) (h : Γ ⊢[PRAAx] neg ≐ zero) :
    ZT.toZ Γ (signedImag B neg) = 𝔞 B := by
  have e := natEq (select_zero neg B zero h)
  have f := natEq (select_zero neg zero B h)
  simp only [signedImag, ZT.toZ]
  rw [e, f]
  ipra_simps
  ring

private theorem imag_one (B neg : PTm n) (h : Γ ⊢[PRAAx] neg ≐ one) :
    ZT.toZ Γ (signedImag B neg) = -𝔞 B := by
  have e := natEq (select_one neg B zero h)
  have f := natEq (select_one neg zero B h)
  simp only [signedImag, ZT.toZ]
  rw [e, f]
  ipra_simps
  ring

private theorem imag_magnitude (B neg : PTm n) (h : Γ ⊢[PRAAx] signBit neg) :
    Γ ⊢[PRAAx] zabs (signedImag B neg) ≐ B := by
  refine h.orE ?_ ?_
  · let Δ := (neg ≐ zero) :: Γ
    have e : Δ ⊢[PRAAx] zabs (signedImag B neg) ≐ zabs (ZT.ofNat B) :=
      zabs_congr (by rw [imag_zero B neg (Prf.hyp0 (Γ := Γ)), ZT.toZ_ofNat])
    exact e.eqTrans (abs_ofNat B)
  · let Δ := (neg ≐ one) :: Γ
    have e : Δ ⊢[PRAAx] zabs (signedImag B neg) ≐ zabs (-(ZT.ofNat B)) :=
      zabs_congr (by rw [imag_one B neg (Prf.hyp0 (Γ := Γ)), ZT.toZ_neg, ZT.toZ_ofNat])
    exact e.eqTrans ((zabs_neg _).eqTrans (abs_ofNat B))

private theorem signed_magnitude_difference (u v : ZT n) :
    Γ ⊢[PRAAx] le (ad (zabs u) (zabs v)) (zabs (u - v)) := by
  have direct : Γ ⊢[PRAAx] le (zabs u) (zabs v + zabs (u - v)) :=
    zabs_tri (u := v) (v := u - v) (w := u) (by rw [ZT.toZ_sub]; ring)
  have reverse : Γ ⊢[PRAAx] le (zabs v) (zabs u + zabs (v - u)) :=
    zabs_tri (u := u) (v := v - u) (w := v) (by rw [ZT.toZ_sub]; ring)
  have symm : Γ ⊢[PRAAx] zabs (v - u) ≐ zabs (u - v) :=
    (zabs_congr (v := -(u - v)) (by rw [ZT.toZ_neg, ZT.toZ_sub, ZT.toZ_sub]; ring)).eqTrans (zabs_neg _)
  exact ad_le_of direct (le_congr (.eqRefl _) (congrAdd (.eqRefl _) symm) reverse)

private theorem raw_coordinates (z H : PTm n) (h : Γ ⊢[PRAAx] bounded z H) :
    Γ ⊢[PRAAx] le (zabs (re z)) H ⋏ le (zabs (im z)) H := by
  have hsq : Γ ⊢[PRAAx] le ((one * one) * ComplexLogarithmRemainder.normSq z) ((H * H) * (one * one)) :=
    le_congr (by ipra_ring) (by ipra_ring) h
  have both := native_coordinates z H one one hsq
  exact .andI (le_congr (one_mul _) (by ipra_ring) both.andE₁)
    (le_congr (one_mul _) (by ipra_ring) both.andE₂)

private theorem step_real (A B neg a b sign : PTm n) :
    Γ ⊢[PRAAx] zabs (re (step A B neg a b sign)) ≐ ad a A :=
  (zabs_congr (v := ZT.ofNat a - ZT.ofNat A) (by
    simp only [step, re_sub, native, eval_re_code, ZT.toZ_ofNat, ZT.toZ_sub])).eqTrans
    (GaussianRationalGridRounding.signed_absolute a A)

private theorem step_imag (A B neg a b sign : PTm n) :
    Γ ⊢[PRAAx] zabs (im (step A B neg a b sign)) ≐ zabs (signedImag b sign - signedImag B neg) :=
  zabs_congr (by simp only [step, im_sub, native, eval_im_code, ZT.toZ_sub])

/-- A step of native radius `H` controls the real and unsigned imaginary coordinates. -/
theorem coordinates (A B neg a b sign H : PTm n) (hneg : Γ ⊢[PRAAx] signBit neg)
    (hsign : Γ ⊢[PRAAx] signBit sign) (hstep : Γ ⊢[PRAAx] bounded (step A B neg a b sign) H) :
    Γ ⊢[PRAAx] le (ad a A) H ⋏ le (ad b B) H := by
  have both := raw_coordinates (step A B neg a b sign) H hstep
  have unsigned := signed_magnitude_difference (Γ := Γ) (signedImag b sign) (signedImag B neg)
  have e := ad_congr (imag_magnitude b sign hsign) (imag_magnitude B neg hneg)
  exact .andI (le_congr (step_real A B neg a b sign) (.eqRefl H) both.andE₁)
    (le_trans (le_congr e (.eqRefl _) unsigned)
      (le_congr (step_imag A B neg a b sign) (.eqRefl H) both.andE₂))

/-- Complex points on opposite sides of the real axis pay for both heights. -/
theorem opposite_height (A B neg a b sign H : PTm n) (hsigns : Γ ⊢[PRAAx] oppositeBits neg sign)
    (hstep : Γ ⊢[PRAAx] bounded (step A B neg a b sign) H) :
    Γ ⊢[PRAAx] le (B + b) H := by
  have ih := le_congr (step_imag A B neg a b sign) (.eqRefl H)
    (raw_coordinates (step A B neg a b sign) H hstep).andE₂
  refine hsigns.orE ?_ ?_
  · let Δ := (neg ≐ zero ⋏ sign ≐ one) :: Γ
    have hn : Δ ⊢[PRAAx] neg ≐ zero := Prf.hyp0.andE₁
    have hs : Δ ⊢[PRAAx] sign ≐ one := Prf.hyp0.andE₂
    have e : Δ ⊢[PRAAx] zabs (signedImag b sign - signedImag B neg) ≐ zabs (-(ZT.ofNat (B + b))) := by
      apply zabs_congr
      rw [ZT.toZ_sub, imag_one b sign hs, imag_zero B neg hn, ZT.toZ_neg, ZT.toZ_ofNat]
      ipra_simps
      ring
    exact le_congr (e.eqTrans ((zabs_neg _).eqTrans (abs_ofNat _))) (.eqRefl H) ih.wk
  · let Δ := (neg ≐ one ⋏ sign ≐ zero) :: Γ
    have hn : Δ ⊢[PRAAx] neg ≐ one := Prf.hyp0.andE₁
    have hs : Δ ⊢[PRAAx] sign ≐ zero := Prf.hyp0.andE₂
    have e : Δ ⊢[PRAAx] zabs (signedImag b sign - signedImag B neg) ≐ zabs (ZT.ofNat (B + b)) := by
      apply zabs_congr
      rw [ZT.toZ_sub, imag_zero b sign hs, imag_one B neg hn, ZT.toZ_ofNat]
      ipra_simps
      ring
    exact le_congr (e.eqTrans (abs_ofNat _)) (.eqRefl H) ih.wk

private theorem chart_cross (u x v y H M : PTm n)
    (hux : Γ ⊢[PRAAx] le u x) (hMy : Γ ⊢[PRAAx] le M y)
    (hxy : Γ ⊢[PRAAx] le (ad y x) H) (huv : Γ ⊢[PRAAx] le (ad v u) H) :
    Γ ⊢[PRAAx] le (M * ad (u * y) (v * x)) ((two * H) * x * y) := by
  have first : Γ ⊢[PRAAx] le (ad (u * y) (u * x)) (x * H) :=
    le_congr (ad_mul u y x).eqSymm (.eqRefl _) (le_mul_mono hux hxy)
  have secondEq : Γ ⊢[PRAAx] ad (u * x) (v * x) ≐ x * ad v u :=
    (ad_congr (mul_comm u x) (mul_comm v x)).eqTrans
      ((ad_mul x u v).eqTrans (congrMul (.eqRefl x) (add_comm _ _)))
  have second := le_congr secondEq.eqSymm (.eqRefl _) (le_mul_mono (le_refl x) huv)
  have total := le_trans (ad_triangle (u * y) (u * x) (v * x)) (add_le_add₂ first second)
  exact le_congr (.eqRefl _) (by ipra_ring) (le_mul_mono hMy total)

/-- Comparison of the direct ratios when the first endpoint is in the direct chart. -/
theorem small_ratio (A B a b H M : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hMA : Γ ⊢[PRAAx] le M A) (hMa : Γ ⊢[PRAAx] le M a)
    (hB : Γ ⊢[PRAAx] le B A) (hr : Γ ⊢[PRAAx] le (ad a A) H) (hi : Γ ⊢[PRAAx] le (ad b B) H) :
    Γ ⊢[PRAAx] radius (fraction B A) (fraction b a) (two * H) M :=
  radius_of_cleared B A b a (two * H) M (le_trans hM hMA) (le_trans hM hMa)
    (chart_cross B A b a H M hB hMa hr hi)

/-- Both endpoints in the reciprocal chart. -/
theorem large_ratio (A B a b H M : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hMA : Γ ⊢[PRAAx] le M A) (hMa : Γ ⊢[PRAAx] le M a)
    (hB : Γ ⊢[PRAAx] le A B) (hb : Γ ⊢[PRAAx] le a b)
    (hr : Γ ⊢[PRAAx] le (ad a A) H) (hi : Γ ⊢[PRAAx] le (ad b B) H) :
    Γ ⊢[PRAAx] radius (fraction A B) (fraction a b) (two * H) M :=
  small_ratio B A b a H M hM (le_trans hMA hB) (le_trans hMa hb) hB hi hr

private theorem add_step (x y H : PTm n) (h : Γ ⊢[PRAAx] le (ad x y) H) : Γ ⊢[PRAAx] le x (y + H) :=
  le_trans (le_add_ad x y) (add_le_add₂ (le_refl y) h)

private theorem ratio_to_one (u x H M : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hMx : Γ ⊢[PRAAx] le M x) (h : Γ ⊢[PRAAx] le (ad u x) H) :
    Γ ⊢[PRAAx] radius (fraction u x) (fraction one one) H M := by
  apply radius_of_cleared u x one one H M (le_trans hM hMx) (le_refl one)
  exact le_congr (congrMul (.eqRefl M) (ad_congr (by ipra_ring) (one_mul x))).eqSymm
    (by ipra_ring) (le_mul_mono hMx h)

/-- The direct-chart endpoint and the reciprocal-chart endpoint are both close to their common boundary. -/
theorem mixed_ratios (A B a b H M : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hMA : Γ ⊢[PRAAx] le M A) (hMa : Γ ⊢[PRAAx] le M a)
    (hB : Γ ⊢[PRAAx] le B A) (hb : Γ ⊢[PRAAx] le a b)
    (hr : Γ ⊢[PRAAx] le (ad a A) H) (hi : Γ ⊢[PRAAx] le (ad b B) H) :
    Γ ⊢[PRAAx] radius (fraction B A) (fraction one one) (two * H) M ⋏
      radius (fraction a b) (fraction one one) (two * H) M := by
  have hra := le_congr (add_comm _ _) (.eqRefl H) hr
  have ars := add_step A a H hra
  have bis := add_step b B H hi
  have e₁ : Γ ⊢[PRAAx] le A (B + two * H) := by ipra_le sl ars + sl hb + sl bis
  have e₂ : Γ ⊢[PRAAx] le b (a + two * H) := by ipra_le sl bis + sl hB + sl ars
  have p₁ := ad_le_of (le_trans hB (le_add_right A (two * H))) e₁
  have p₂ := ad_le_of (le_trans hb (le_add_right b (two * H))) e₂
  exact .andI (ratio_to_one B A (two * H) M hM hMA p₁)
    (ratio_to_one a b (two * H) M hM (le_trans hMa hb) p₂)

/-- A bounded imaginary height controls its ratio to the real numerator. -/
theorem height_ratio (A B H M : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hMA : Γ ⊢[PRAAx] le M A) (hB : Γ ⊢[PRAAx] le B H) :
    Γ ⊢[PRAAx] radius (fraction B A) (fraction zero one) H M := by
  apply radius_of_cleared B A zero one H M (le_trans hM hMA) (le_refl one)
  have e : Γ ⊢[PRAAx] ad (B * one) (zero * A) ≐ B :=
    (ad_congr (by ipra_ring) (by ipra_ring)).eqTrans
      ((congrAdd (monus_zero B) (zero_monus B)).eqTrans (add_zero B))
  exact le_congr (congrMul (.eqRefl M) e).eqSymm (by ipra_ring) (le_mul_mono hMA hB)

theorem actual_right_half_plane_argument_increment_coordinates_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (bounded (step (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 6) ⟶
        ((signBit (var 2) ⟶ signBit (var 5) ⟶ le (ad (var 3) (var 0)) (var 6) ⋏
          le (ad (var 4) (var 1)) (var 6)) ⋏
         (oppositeBits (var 2) (var 5) ⟶ le (var 1 + var 4) (var 6)))) :=
  closeUniv 7 (.impI (.andI (.impI (.impI (coordinates _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0 hyp2)))
    (.impI (opposite_height _ _ _ _ _ _ _ Prf.hyp0 Prf.hyp1))))

theorem actual_right_half_plane_argument_increment_ratio_bounds_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      ((le one (var 5) ⋏ (le (var 5) (var 0) ⋏ le (var 5) (var 2))) ⋏
        (le (ad (var 2) (var 0)) (var 4) ⋏ le (ad (var 3) (var 1)) (var 4)) ⟶
        ((le (var 1) (var 0) ⟶ radius (fraction (var 1) (var 0)) (fraction (var 3) (var 2)) (two * var 4) (var 5)) ⋏
         ((le (var 0) (var 1) ⋏ le (var 2) (var 3)) ⟶
           radius (fraction (var 0) (var 1)) (fraction (var 2) (var 3)) (two * var 4) (var 5)) ⋏
         ((le (var 1) (var 0) ⋏ le (var 2) (var 3)) ⟶
           radius (fraction (var 1) (var 0)) (fraction one one) (two * var 4) (var 5) ⋏
           radius (fraction (var 2) (var 3)) (fraction one one) (two * var 4) (var 5)))) :=
  closeUniv 6 (.impI (.andI
    (.impI (small_ratio _ _ _ _ _ _ Prf.hyp1.andE₁.andE₁ Prf.hyp1.andE₁.andE₂.andE₁
      Prf.hyp1.andE₁.andE₂.andE₂ Prf.hyp0 Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂))
    (.andI
      (.impI (large_ratio _ _ _ _ _ _ Prf.hyp1.andE₁.andE₁ Prf.hyp1.andE₁.andE₂.andE₁
        Prf.hyp1.andE₁.andE₂.andE₂ Prf.hyp0.andE₁ Prf.hyp0.andE₂ Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂))
      (.impI (mixed_ratios _ _ _ _ _ _ Prf.hyp1.andE₁.andE₁ Prf.hyp1.andE₁.andE₂.andE₁
        Prf.hyp1.andE₁.andE₂.andE₂ Prf.hyp0.andE₁ Prf.hyp0.andE₂ Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂)))))

end LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneArgumentIncrementGeometry
