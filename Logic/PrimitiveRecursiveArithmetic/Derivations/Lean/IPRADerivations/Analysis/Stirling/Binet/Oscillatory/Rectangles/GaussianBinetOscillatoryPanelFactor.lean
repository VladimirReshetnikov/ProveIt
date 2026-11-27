import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.Arctangent.LaplaceTransforms.GaussianBinetArctangentCosineLaplace
import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.GaussianBinetImaginaryExponentialIntegral
import IPRADerivations.Analysis.Polynomials.Translation.GaussianInverseBinomialRows

/-!
# Actual damped cosine panels as products

On a common rectangle cell the two shifted original exponentials
factor, with a uniform dyadic error, into the original damping sample
and a purely imaginary sine/cosine exponential observation.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBinetOscillatoryPanelFactor

open_ipra
open ComplexLogarithmRemainder (eval_im_code eval_re_code)
open GaussianBinetArctangentCosineLaplace (mean mean_distance)
open GaussianBinetArctangentResolvent (pole pole_as_sum signedTimeNumerator)
open GaussianBinetArctangentSignedPole (chart_source argument_chart branch imagNumerator)
open GaussianBinetExponentialIntegralGrid (exponent row)
open GaussianBinetExponentialPanel (sample)
open GaussianBinetImaginaryExponentialIntegral (coefficient coefficient_bound exponent_nonpositive)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianInverseBinomialRows (negative_congr)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (native source)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRightHalfPlaneLogarithmOffset (signedImag)
open GaussianRationalCoefficientScaling (qmul_add)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (qadd qmul qzero ofGaussian ofGaussian_canonical ofGaussian_represents canonical_unique
  represents_congr positive_product)
open GaussianRationalMetric (bounded distanceBounded qnegative qnegative_canonical qsub)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (bounded_product_one bound_congr)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qsub_congr qzero_add qzero_canonical)
open GaussianReciprocalHorner (qmul_associative)
open GaussianRootAlgebra (equal_of_values re_neg im_neg)
open GaussianSineProductImaginaryLogDerivative (axisNumerator)
open RationalArithmetic (select select_zero select_one)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def polarity (s : Bool) : PTm n := if s then one else zero

private theorem polarity_bit (s : Bool) : Γ ⊢[PRAAx] polarity s ≐ zero ⋎ polarity s ≐ one := by
  cases s
  · exact .orI₁ (.eqRefl _)
  · exact .orI₂ (.eqRefl _)

private theorem imaginary_chart (s : Bool) (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    argument zero A B (polarity s) ≐ ofGaussian (signedTimeNumerator s A) B := by
  let x := native zero A (polarity s)
  let y := signedTimeNumerator s A
  apply canonical_unique _ _ y B (ofGaussian_canonical x _ hB) (ofGaussian_canonical y _ hB) hB
    (hrv := ofGaussian_represents _ _ hB)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := ofGaussian_represents x B hB)
  apply equal_of_values
  · cases s <;> simp [x,y,polarity,native,signedTimeNumerator,axisNumerator,eval_re_code,re_neg,ZT.toZ_ofNat]
  · cases s
    · change ZT.toZ Γ (ComplexLogarithmRemainder.im (native zero A zero)) = _
      change ZT.toZ Γ (ComplexLogarithmRemainder.im (native zero A zero)) = ZT.toZ Γ (ComplexLogarithmRemainder.im (axisNumerator A))
      rw [native,eval_im_code,axisNumerator,eval_im_code,ZT.toZ_ofNat]
      change Groth.ι (Q.mk Γ (select zero A zero)) - Groth.ι (Q.mk Γ (select zero zero A)) = Groth.ι (Q.mk Γ A)
      rw [natEq (select_zero (Γ := Γ) zero A zero (.eqRefl _)),natEq (select_zero (Γ := Γ) zero zero A (.eqRefl _))]
      ipra_simps
      ring
    · change ZT.toZ Γ (ComplexLogarithmRemainder.im (native zero A one)) =
        ZT.toZ Γ (ComplexLogarithmRemainder.im (ComplexLogarithmRemainder.neg (axisNumerator A)))
      rw [native,eval_im_code,im_neg,axisNumerator,eval_im_code,ZT.toZ_ofNat]
      change Groth.ι (Q.mk Γ (select one A zero)) - Groth.ι (Q.mk Γ (select one zero A)) = -Groth.ι (Q.mk Γ A)
      rw [natEq (select_one (Γ := Γ) one A zero (.eqRefl _)),natEq (select_one (Γ := Γ) one zero A (.eqRefl _))]
      ipra_simps
      ring

private theorem negative_sum (x y : PTm n) : Γ ⊢[PRAAx]
    qadd (qnegative x) (qnegative y) ≐ qnegative (qadd x y) := by
  have a : Γ ⊢[PRAAx] qsub qzero x ≐ qnegative x := qzero_add _ (qnegative_canonical _)
  have b : Γ ⊢[PRAAx] qsub qzero y ≐ qnegative y := qzero_add _ (qnegative_canonical _)
  exact (qadd_congr a.eqSymm b.eqSymm).eqTrans
    ((GaussianNameArithmetic.sum_difference qzero x qzero y).eqSymm.eqTrans
      ((qsub_congr (qzero_add _ qzero_canonical) (.eqRefl _)).eqTrans (qzero_add _ (qnegative_canonical _))))

theorem exponent_sum (s : Bool) (X Y D sign A B a b : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qadd (GaussianBinetLaplaceExponential.exponent X Y D sign a b) (exponent (coefficient A B (polarity s)) a b) ≐
      exponent (qnegative (pole s X Y D sign A B)) a b := by
  let z := argument X Y D sign
  let u := argument zero A B (polarity s)
  let t := fraction a b
  let x := qnegative z
  let y := qnegative u
  have src : Γ ⊢[PRAAx] qadd z u ≐ pole s X Y D sign A B :=
    (qadd_congr (.eqRefl _) (imaginary_chart s A B hB)).eqTrans (pole_as_sum s X Y D sign A B hD hB)
  exact (qadd_congr (qmul_commutative x t) (qmul_commutative y t)).eqTrans
    ((qmul_add t x y).eqSymm.eqTrans
      ((qmul_commutative t _).eqTrans (qmul_congr ((negative_sum z u).eqTrans (negative_congr src)) (.eqRefl _))))

private theorem sample_congr (p R : PTm n) {x y : PTm n} (h : Γ ⊢[PRAAx] x ≐ y) : Γ ⊢[PRAAx] sample p x R ≐ sample p y R := by
  simpa only [GaussianBinetExponentialPanel.subst_sample,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
    (Prf.eqCongr1 (sample (Syn.shift p) (var 0) (Syn.shift R)) h)

theorem factor_sample (s : Bool) (p X Y D sign A B a b R U T : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hB : Γ ⊢[PRAAx] le one B) (hb : Γ ⊢[PRAAx] le one b)
    (hU : Γ ⊢[PRAAx] le A (U*B)) (ht : Γ ⊢[PRAAx] le a (T*b)) : Γ ⊢[PRAAx]
    distanceBounded (row p (qnegative (pole s X Y D sign A B)) ((R+U)*T) a b)
      (qmul (row p (qnegative (argument X Y D sign)) (R*T) a b)
        (row p (coefficient A B (polarity s)) (U*T) a b)) (num 10) (unit p) := by
  let x := GaussianBinetLaplaceExponential.exponent X Y D sign a b
  let y := exponent (coefficient A B (polarity s)) a b
  let A' := X*B
  let B' := imagNumerator s X Y D sign A B
  let D' := D*B
  let sign' := branch s X Y D sign A B
  let z := GaussianBinetLaplaceExponential.exponent A' B' D' sign' a b
  let z' := exponent (qnegative (pole s X Y D sign A B)) a b
  let S := (R+U)*T
  have hD := hz.andE₁.andE₂
  have hR := GaussianBinetLaplaceExponential.exponent_bound X Y D sign R T a b hz hb ht
  have hn := GaussianBinetLaplaceExponential.exponent_nonpositive X Y D sign a b hD hb
  have hy := bounded_product_one (coefficient_bound A B (polarity s) U hB (polarity_bit s) hU)
      (GaussianEulerExponentCompactBounds.fraction_bound a b T hb ht)
  have hy₀ := exponent_nonpositive A B (polarity s) a b hB hb
  have w := chart_source s X Y D sign A B R U hz hB hU
  have zBound := GaussianBinetLaplaceExponential.exponent_bound A' B' D' sign' (R+U) T a b w hb ht
  have e₁ : Γ ⊢[PRAAx] qadd x y ≐ z' := exponent_sum s X Y D sign A B a b hD hB
  have e₂ : Γ ⊢[PRAAx] z ≐ z' :=
    qmul_congr (negative_congr (argument_chart s X Y D sign A B hD hB)) (.eqRefl _)
  have sBound : Γ ⊢[PRAAx] bounded (qadd x y) S one :=
    bound_congr (e₂.eqTrans e₁.eqSymm) (.eqRefl _) (.eqRefl _) zBound
  exact distance_congr (sample_congr p S e₁) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianBinetExponentialPanel.product_sample p x y (R*T) (U*T) S
      (GaussianSignedNameExponentialOrder.constant_input _ _ hR)
      (GaussianSignedNameExponentialOrder.constant_input _ _ hy)
      (GaussianSignedNameExponentialOrder.constant_input _ _ sBound) hn hy₀)

private theorem mean_factor (w a b : PTm n) : Γ ⊢[PRAAx]
    mean (qmul w a) (qmul w b) ≐ qmul w (mean a b) :=
  (qmul_congr (.eqRefl _) (qmul_add w a b).eqSymm).eqTrans
    (GaussianRationalPowerAlgebra.commute_nested _ w _)

theorem cosine_factor_sample (p X Y D sign A B a b R U T : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hB : Γ ⊢[PRAAx] le one B) (hb : Γ ⊢[PRAAx] le one b)
    (hU : Γ ⊢[PRAAx] le A (U*B)) (ht : Γ ⊢[PRAAx] le a (T*b)) : Γ ⊢[PRAAx]
    distanceBounded (mean (row p (qnegative (pole false X Y D sign A B)) ((R+U)*T) a b)
      (row p (qnegative (pole true X Y D sign A B)) ((R+U)*T) a b))
      (qmul (row p (qnegative (argument X Y D sign)) (R*T) a b)
        (mean (row p (coefficient A B (polarity false)) (U*T) a b)
          (row p (coefficient A B (polarity true)) (U*T) a b))) (num 10) (unit p) :=
  distance_congr (.eqRefl _) (mean_factor _ _ _) (.eqRefl _) (.eqRefl _)
    (mean_distance _ _ _ _ _ _ (unit_positive p)
      (factor_sample false p X Y D sign A B a b R U T hz hB hb hU ht)
      (factor_sample true p X Y D sign A B a b R U T hz hB hb hU ht))

end LeanProofs.IPRA.Analysis.GaussianBinetOscillatoryPanelFactor
