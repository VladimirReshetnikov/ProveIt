import IPRADerivations.Analysis.GaussianBinetSineDampedPanels
import IPRADerivations.Analysis.GaussianBinetSineDampedAxis

/-!
# Actual real decay samples in the damped sine panels

Read the damping factor through the canonical real evaluator used by
the geometric sum. The original sine quotient has a uniform majorant
throughout this fixed positive-frequency panel family.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBinetSineRealDampedPanels

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetExponentialIntegralGrid (row exponent)
open GaussianBinetExponentialPanel (unit_bound)
open GaussianBinetImaginaryExponentialIntegral (coefficient coefficient_bound exponent_nonpositive)
open GaussianBinetOscillatoryPanelFactor (polarity)
open GaussianBinetOscillatorySineQuotient (quotient)
open GaussianBinetSineDampedPanels (multiplier multiplier_bound quotient_at shiftedPanel targetPanel panel_error)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerDecayMesh (observation)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (source)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (bounded distanceBounded qnegative qsub)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (bound_congr bounded_negative bounded_product bounded_sum)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def value (p X D A B a b U T : PTm n) : PTm n :=
  qmul (observation (X*a) (D*b) p) (quotient p a b (U*T) A B)

private theorem polarity_bit (s : Bool) : Γ ⊢[PRAAx] polarity s ≐ zero ⋎ polarity s ≐ one := by
  cases s
  · exact .orI₁ (.eqRefl _)
  · exact .orI₂ (.eqRefl _)

theorem quotient_bound (p A B a b U T : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (hb : Γ ⊢[PRAAx] le one b) (hU : Γ ⊢[PRAAx] le A (U*B)) (ht : Γ ⊢[PRAAx] le a (T*b)) :
    Γ ⊢[PRAAx] bounded (quotient p a b (U*T) A B) (B*num 4) one := by
  let f (s : Bool) := coefficient A B (polarity s)
  let C := U*T
  let x := row p (f true) C a b
  let y := row p (f false) C a b
  have bd (s : Bool) : Γ ⊢[PRAAx] bounded (row p (f s) C a b) two one := by
    have expo : Γ ⊢[PRAAx] bounded (exponent (f s) a b) C one :=
      bound_congr (.eqRefl _) (.eqRefl _) (one_mul one)
        (bounded_product _ _ U one T one (le_refl one) (le_refl one) (coefficient_bound A B (polarity s) U hB (polarity_bit s) hU)
          (GaussianEulerExponentCompactBounds.fraction_bound a b T hb ht))
    exact unit_bound p _ C (GaussianSignedNameExponentialOrder.constant_input _ _ expo) (exponent_nonpositive A B _ a b hB hb)
  have dif : Γ ⊢[PRAAx] bounded (qsub x y) (num 4) one :=
    bound_congr (.eqRefl _) (by ipra_ring) (one_mul one)
      (bounded_sum x (qnegative y) two one two one (le_refl one) (le_refl one) (bd true)
        (bounded_negative y two one (le_refl one) (bd false)))
  exact bound_congr (quotient_at p A B a b C hB hb) (.eqRefl _) (one_mul one)
    (bounded_product _ _ B one (num 4) one (le_refl one) (le_refl one) (multiplier_bound A B hA hB) dif)

theorem real_panel_error (p X D A B a b R U T : PTm n)
    (hz : Γ ⊢[PRAAx] source X zero D zero R) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (hb : Γ ⊢[PRAAx] le one b) (hU : Γ ⊢[PRAAx] le A (U*B)) (ht : Γ ⊢[PRAAx] le a (T*b)) :
    Γ ⊢[PRAAx] distanceBounded (shiftedPanel p X zero D zero A B a b R U T) (value p X D A B a b U T)
      (B*num 28) (unit p) := by
  let H := unit p
  let e := row p (qnegative (argument X zero D zero)) (R*T) a b
  let d := observation (X*a) (D*b) p
  let v := quotient p a b (U*T) A B
  have h := unit_positive (Γ := Γ) p
  have observed : Γ ⊢[PRAAx] distanceBounded e d two H :=
    distance_radius_mono _ _ (H+H) (H*H) two H (positive_product _ _ h h) h
      (le_of_eq_add (d := zero) (by ipra_ring)) (GaussianBinetSineDampedAxis.same_observation p p X D a b R T hz hb ht)
  have first := panel_error p X zero D zero A B a b R U T hz hA hB hb hU ht
  have last : Γ ⊢[PRAAx] distanceBounded (targetPanel p X zero D zero A B a b R U T) (value p X D A B a b U T)
      ((B*num 4)*two) H :=
    distance_congr (qmul_commutative v e) (qmul_commutative v d) (.eqRefl _) (.eqRefl _)
      (GaussianApproximateInverseDistance.multiply_distance v e d (B*num 4) two H h (quotient_bound p A B a b U T hA hB hb hU ht) observed)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) (distance_triangle_same _ _ _ _ _ _ h first last)

end LeanProofs.IPRA.Analysis.GaussianBinetSineRealDampedPanels
