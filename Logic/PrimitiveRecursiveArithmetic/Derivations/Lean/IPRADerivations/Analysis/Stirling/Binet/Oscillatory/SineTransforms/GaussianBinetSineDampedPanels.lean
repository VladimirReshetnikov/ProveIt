import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.SineTransforms.GaussianBinetSineDampedTransform
import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.Rectangles.GaussianBinetOscillatorySineQuotient
import IPRADerivations.Analysis.Exponential.Estimates.GaussianRationalExponentialTangent

/-!
# The same sine quotient on the original damped panels

The two shifted Laplace exponential samples are compared on their
common mesh with the actual damping times the regularized sine
quotient used by the arctangent rectangle. Positive frequency supplies
the same separated reciprocal throughout this fixed-frequency row.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBinetSineDampedPanels

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetArctangentResolvent (pole)
open GaussianBinetExponentialIntegralGrid (row exponent)
open GaussianBinetExponentialPanel (sample)
open GaussianBinetImaginaryExponentialIntegral (coefficient)
open GaussianBinetImaginaryExponentialScale (coefficient_congr exponent_scale)
open GaussianBinetOscillatoryPanelFactor (polarity factor_sample)
open GaussianBinetOscillatorySineQuotient (quotient)
open GaussianBinetSineDampedTransform (coefficient_lower)
open GaussianCoefficientNameBounds (bounded_radius_mono unit unit_positive)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (source)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalLowerBounds (inverse_bound)
open GaussianRationalMetric (bounded distanceBounded qnegative qnegative_canonical qsub)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (reciprocal bound_congr bounded_product)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def multiplier (A B : PTm n) : PTm n := qmul (reciprocal (coefficient A B (polarity true))) (fraction one two)

def shiftedPanel (p X Y D sign A B a b R U T : PTm n) : PTm n :=
  qmul (multiplier A B)
    (qsub (row p (qnegative (pole true X Y D sign A B)) ((R+U)*T) a b)
      (row p (qnegative (pole false X Y D sign A B)) ((R+U)*T) a b))

def targetPanel (p X Y D sign A B a b R U T : PTm n) : PTm n :=
  qmul (row p (qnegative (argument X Y D sign)) (R*T) a b) (quotient p a b (U*T) A B)

@[simp] theorem subst_multiplier {m : ℕ} (σ : Fin n → PTm m) (A B : PTm n) :
    Syn.subst σ (multiplier A B) = multiplier (Syn.subst σ A) (Syn.subst σ B) := by simp [multiplier,one,two]

private theorem sample_cast (p C C' x y : PTm n) (hC : Γ ⊢[PRAAx] C ≐ C') (e : Γ ⊢[PRAAx] x ≐ y) :
    Γ ⊢[PRAAx] sample p x C ≐ sample p y C' :=
  congrAp2 GaussianBinetExponentialPanel.expoF (.eqRefl p) (congrPairT hC e)

theorem imaginary_panel (s : Bool) (p A B a b C : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] row p (coefficient A B (polarity s)) C a b ≐ row p (coefficient (a*A) (b*B) (polarity s)) (C*one) one one := by
  let v := coefficient (a*A) (b*B) (polarity s)
  have e : Γ ⊢[PRAAx] exponent (coefficient A B (polarity s)) a b ≐ v :=
    (exponent_scale s A B a b hB hb).eqTrans (coefficient_congr s (mul_comm _ _) (mul_comm _ _))
  have w : Γ ⊢[PRAAx] exponent v one one ≐ v :=
    (qmul_congr (.eqRefl _) (GaussianRationalExponentialTangent.fraction_one one (le_refl one))).eqTrans
      (qmul_one_right v (qnegative_canonical _))
  exact sample_cast p C (C*one) _ _ (by ipra_ring) (e.eqTrans w.eqSymm)

theorem multiplier_bound (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] bounded (multiplier A B) B one := by
  have inv : Γ ⊢[PRAAx] bounded (reciprocal (coefficient A B (polarity true))) B one :=
    bounded_radius_mono _ _ _ _ _ hA (le_refl one)
      (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right B hA)) (inverse_bound _ _ _ hA hB (coefficient_lower A B hB))
  have h₂ := le_succ_self (Γ := Γ) one
  have half : Γ ⊢[PRAAx] bounded (fraction one two) one one :=
    GaussianEulerExponentCompactBounds.fraction_bound one two one h₂
      (le_congr (.eqRefl _) (one_mul two).eqSymm h₂)
  exact bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (bounded_product _ _ B one one one (le_refl one) (le_refl one) inv half)

theorem quotient_at (p A B a b C : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] qmul (multiplier A B) (qsub (row p (coefficient A B (polarity true)) C a b)
      (row p (coefficient A B (polarity false)) C a b)) ≐ quotient p a b C A B :=
  (qmul_associative _ _ _).eqTrans (qmul_congr (.eqRefl _) (qmul_congr (.eqRefl _)
    (qsub_congr (imaginary_panel true p A B a b C hB hb) (imaginary_panel false p A B a b C hB hb))))

theorem panel_error (p X Y D sign A B a b R U T : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (hb : Γ ⊢[PRAAx] le one b) (hU : Γ ⊢[PRAAx] le A (U*B)) (ht : Γ ⊢[PRAAx] le a (T*b)) :
    Γ ⊢[PRAAx] distanceBounded (shiftedPanel p X Y D sign A B a b R U T) (targetPanel p X Y D sign A B a b R U T)
      (B*num 20) (unit p) := by
  let k := multiplier A B
  let e := row p (qnegative (argument X Y D sign)) (R*T) a b
  let x := row p (coefficient A B (polarity true)) (U*T) a b
  let y := row p (coefficient A B (polarity false)) (U*T) a b
  let z := qsub x y
  have h := unit_positive (Γ := Γ) p
  have plus := factor_sample true p X Y D sign A B a b R U T hz hB hb hU ht
  have minus := factor_sample false p X Y D sign A B a b R U T hz hB hb hU ht
  have d := GaussianNamedDifference.difference_distance _ _ _ _ (num 10) (num 10) (unit p) h plus minus
  have factored : Γ ⊢[PRAAx] qmul k (qsub (qmul e x) (qmul e y)) ≐ qmul e (qmul k z) :=
    (qmul_congr (.eqRefl _) (GaussianRationalRoundedPower.multiplication_difference e x y)).eqTrans
      ((qmul_associative k e z).eqSymm.eqTrans ((qmul_congr (qmul_commutative k e) (.eqRefl _)).eqTrans (qmul_associative e k z)))
  have regularized : Γ ⊢[PRAAx] qmul k z ≐ quotient p a b (U*T) A B :=
    quotient_at p A B a b (U*T) hB hb
  exact distance_congr (.eqRefl _) (factored.eqTrans (qmul_congr (.eqRefl _) regularized)) (by ipra_ring) (.eqRefl _)
    (GaussianApproximateInverseDistance.multiply_distance k _ _ B _ (unit p) h (multiplier_bound A B hA hB) d)

end LeanProofs.IPRA.Analysis.GaussianBinetSineDampedPanels
