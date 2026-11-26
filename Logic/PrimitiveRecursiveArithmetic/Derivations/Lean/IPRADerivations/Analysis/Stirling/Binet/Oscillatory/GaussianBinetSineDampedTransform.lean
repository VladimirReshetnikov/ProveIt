import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.GaussianBinetSineLaplaceResolvent
import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetImaginaryExponentialScale
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.GaussianLogGammaEulerResidualRadius

/-!
# The finite Laplace transform of the regularized sine quotient

At positive rational frequency, the actual half difference of the two
original exponential panel integrals, divided by the imaginary
frequency, converges to the reciprocal of the exact quadratic
resolvent denominator. The bound is uniform over the original time
mesh, and the frequency division uses its checked separation.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBinetSineDampedTransform

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (eval_re_code eval_im_code normSq scale oneCode)
open GaussianArctangentCayleyValues (imaginaryPoint imaginaryCode)
open GaussianBinetArctangentResolvent (pole polynomial)
open GaussianBinetExponentialIntegralGrid (exponent)
open GaussianBinetImaginaryExponentialIntegral (coefficient)
open GaussianBinetImaginaryExponentialScale (exponent_scale coefficient_congr)
open GaussianBinetOscillatoryPanelFactor (polarity)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (native source)
open GaussianNamedSineFromExponential (multiplier)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (canonical_unique ofGaussian_canonical ofGaussian_represents positive_product qmul qmul_canonical
  qmul_represents represents_congr)
open GaussianRationalLowerBounds (lower lower_from_representation name_lower inverse_bound)
open GaussianRationalMetric (bounded bounded_iff distanceBounded qnegative qnegative_canonical qnegative_represents qsub)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (reciprocal reciprocal_identity reciprocal_canonical)
open GaussianRationalSyntheticDivision (qmul_congr qone)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open GaussianRightHalfPlaneLogarithmOffset (signedImag)
open GaussianRootAlgebra (equal_of_values re_neg im_neg re_mul im_mul re_scale im_scale re_one im_one)
open GaussianSineProductImaginaryLogDerivativeTail (axis_norm)
open RationalArithmetic (select select_one)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "LV" => GaussianBinetExponentialIntegralGrid.value
local notation "P" => GaussianBinetSineLaplaceResolvent.panelValue
local notation "Q" => GaussianBinetSineLaplaceResolvent.value

def value (p X Y D sign A B R U L N : PTm n) : PTm n :=
  let T := D*L
  let c := coefficient A B (polarity true)
  qmul (reciprocal c) (qmul (fraction one two)
    (qsub (LV (p+N) (qnegative (pole true X Y D sign A B)) ((R+U)*T) T N)
      (LV (p+N) (qnegative (pole false X Y D sign A B)) ((R+U)*T) T N)))

private theorem imaginary_unit : Γ ⊢[PRAAx] coefficient one one (polarity true) ≐ (imaginaryPoint : PTm n) := by
  let z := native (zero : PTm n) one (polarity true)
  have h := le_refl (Γ := Γ) one
  have q := qnegative_represents (argument zero one one (polarity true)) z one (ofGaussian_represents z one h)
  apply canonical_unique _ _ imaginaryCode one (qnegative_canonical _) (ofGaussian_canonical _ _ h) h
    (hrv := ofGaussian_represents _ _ h)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := q)
  apply equal_of_values
  · simp [z,native,re_neg,imaginaryCode,eval_re_code,ZT.toZ_ofNat]
  · dsimp only [z]
    rw [im_neg,native,eval_im_code,imaginaryCode,eval_im_code,ZT.toZ_ofNat]
    change -(Groth.ι (LeanProofs.IPRA.Q.mk Γ (select one one zero)) - Groth.ι (LeanProofs.IPRA.Q.mk Γ (select one zero one))) = _
    rw [natEq (select_one (Γ := Γ) one one zero (.eqRefl _)),natEq (select_one (Γ := Γ) one zero one (.eqRefl _))]
    ipra_simps
    ring

theorem coefficient_product (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qmul imaginaryPoint (fraction A B) ≐ coefficient A B (polarity true) :=
  (qmul_congr imaginary_unit.eqSymm (.eqRefl _)).eqTrans
    ((exponent_scale true one one A B (le_refl one) hB).eqTrans (coefficient_congr true (one_mul A) (one_mul B)))

private theorem imaginary_bound : Γ ⊢[PRAAx] bounded (imaginaryPoint : PTm n) one one := by
  have h := le_refl (Γ := Γ) one
  have a : Γ ⊢[PRAAx] normSq (imaginaryCode : PTm n) ≐ one*one := axis_norm one
  exact (bounded_iff _ _ _ _ _ h h (ofGaussian_represents imaginaryCode one h)).iffMpr
    (le_congr (congrMul (.eqRefl (one*one)) a.eqSymm) (.eqRefl _) (le_refl _))

private theorem imaginary_times_multiplier : Γ ⊢[PRAAx] qmul imaginaryPoint multiplier ≐ (fraction one two : PTm n) := by
  let z := (imaginaryCode : PTm n)
  let w := ComplexLogarithmRemainder.neg z
  let t := scale one (oneCode : PTm n)
  have h := le_refl (Γ := Γ) one
  have h₂ := le_succ_self (Γ := Γ) one
  have p := qmul_represents imaginaryPoint multiplier z w one two h h₂ (ofGaussian_represents z one h) (ofGaussian_represents w two h₂)
  apply canonical_unique _ _ t two (qmul_canonical _ _) (ofGaussian_canonical _ _ h₂) h₂
    (hrv := ofGaussian_represents t two h₂)
  apply represents_congr (.eqRefl _) (hAB := one_mul two) (h := p)
  apply equal_of_values <;> simp [z,w,t,imaginaryCode,re_mul,im_mul,re_neg,im_neg,re_scale,im_scale,re_one,im_one,
    eval_re_code,eval_im_code,ZT.toZ_ofNat]

theorem coefficient_lower (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] lower (coefficient A B (polarity true)) A B := by
  let z := native zero A (polarity true)
  let v := ComplexLogarithmRemainder.neg z
  have nv : Γ ⊢[PRAAx] normSq v ≐ A*A := (ComplexLogarithmRemainder.normSq_neg z).eqTrans
    ((GaussianLogGammaEulerResidualRadius.native_norm zero A (polarity true) (.orI₂ (.eqRefl one))).eqTrans (by ipra_ring))
  have r := qnegative_represents (argument zero A B (polarity true)) z B (ofGaussian_represents (Γ := Γ) z B hB)
  exact lower_from_representation _ _ B A B hB hB r
    (le_congr (by ipra_ring) (congrMul (.eqRefl (B*B)) nv.eqSymm) (le_refl ((B*B)*(A*A))))

theorem finite_error (p X Y D sign A B R U K L N : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (hU : Γ ⊢[PRAAx] le A (U*B)) (hm : Γ ⊢[PRAAx] le D (K*X)) (hL : Γ ⊢[PRAAx] le L p)
    (hN : Γ ⊢[PRAAx] le ((R+U)*(D*L)) N) (hpN : Γ ⊢[PRAAx] le (unit p) N) :
    Γ ⊢[PRAAx] distanceBounded (value p X Y D sign A B R U L N) (reciprocal (polynomial X Y D sign A B))
      (B*GaussianBinetArctangentCosineLaplace.error p R U K (D*L) L) (unit p*unit L) := by
  let T := D*L
  let c := coefficient A B (polarity true)
  let W := reciprocal (polynomial X Y D sign A B)
  let E := GaussianBinetArctangentCosineLaplace.error p R U K T L
  let H := unit p*unit L
  let v := P p X Y D sign A B R U L N
  let w := Q X Y D sign A B
  let s := LV (p+N) (qnegative (pole true X Y D sign A B)) ((R+U)*T) T N
  let t := LV (p+N) (qnegative (pole false X Y D sign A B)) ((R+U)*T) T N
  have hH : Γ ⊢[PRAAx] le one H := positive_product _ _ (unit_positive p) (unit_positive L)
  have origin := GaussianBinetSineLaplaceResolvent.finite_error p X Y D sign A B R U K L N hz hB hU hm hL hN hpN
  have eq₁ : Γ ⊢[PRAAx] qmul imaginaryPoint v ≐ qmul (fraction one two) (qsub s t) :=
    (qmul_associative imaginaryPoint multiplier (qsub s t)).eqSymm.eqTrans (qmul_congr imaginary_times_multiplier (.eqRefl _))
  have eq₂ : Γ ⊢[PRAAx] qmul imaginaryPoint w ≐ qmul c W :=
    (qmul_associative imaginaryPoint (fraction A B) W).eqSymm.eqTrans (qmul_congr (coefficient_product A B hB) (.eqRefl _))
  have first := distance_congr eq₁ eq₂ (one_mul E) (.eqRefl _)
    (GaussianApproximateInverseDistance.multiply_distance imaginaryPoint v w one E H hH imaginary_bound origin)
  have low := coefficient_lower A B hB
  have norm := GaussianNameReciprocal.lower_norm_positive c B hB (name_lower c A B hA hB low)
  have raw : Γ ⊢[PRAAx] le (B*one) (B*A) := le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right B hA)
  have inverse : Γ ⊢[PRAAx] bounded (reciprocal c) B one :=
    bounded_radius_mono _ _ _ _ _ hA (le_refl one) raw (inverse_bound _ _ _ hA hB low)
  have cancelled : Γ ⊢[PRAAx] qmul (reciprocal c) (qmul c W) ≐ W :=
    (qmul_associative _ _ _).eqSymm.eqTrans
      ((qmul_congr ((qmul_commutative _ _).eqTrans (reciprocal_identity c norm)) (.eqRefl _)).eqTrans
        ((qmul_commutative _ _).eqTrans (qmul_one_right W (reciprocal_canonical _))))
  exact distance_congr (.eqRefl _) cancelled (.eqRefl _) (.eqRefl _)
    (GaussianApproximateInverseDistance.multiply_distance (reciprocal c) _ _ B E H hH inverse first)

end LeanProofs.IPRA.Analysis.GaussianBinetSineDampedTransform
