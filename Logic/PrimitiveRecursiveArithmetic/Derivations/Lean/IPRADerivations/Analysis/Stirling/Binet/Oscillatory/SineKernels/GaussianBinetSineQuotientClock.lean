import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.SineTransforms.GaussianBinetSineDampedPanels
import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.Rectangles.GaussianBinetOscillatorySineRows

/-!
# Independent clocks and radii for the actual positive sine quotient

The paired imaginary exponential names can be read at independent
precisions and with independently admitted angle radii. The same
positive-frequency reciprocal bounds the resulting quotient error.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBinetSineQuotientClock

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetExponentialIntegralGrid (row exponent)
open GaussianBinetImaginaryExponentialIntegral (coefficient coefficient_bound)
open GaussianBinetOscillatoryPanelFactor (polarity)
open GaussianBinetOscillatorySineQuotient (quotient)
open GaussianBinetSineDampedPanels (multiplier multiplier_bound)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF)
open GaussianNameEquivalence (cross_at)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianReciprocalHorner (qmul_associative)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem polarity_bit (s : Bool) : Γ ⊢[PRAAx] polarity s ≐ zero ⋎ polarity s ≐ one := by
  cases s
  · exact .orI₁ (.eqRefl _)
  · exact .orI₂ (.eqRefl _)

private theorem row_input (s : Bool) (a b C : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hC : Γ ⊢[PRAAx] le a (C*b)) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input constantF (C*one) (exponent (coefficient a b (polarity s)) one one) := by
  have f := GaussianEulerExponentCompactBounds.fraction_bound (Γ := Γ) one one one (le_refl one)
    (le_congr (.eqRefl _) (one_mul one).eqSymm (le_refl one))
  have b := bounded_product _ _ C one one one (le_refl one) (le_refl one) (coefficient_bound a b (polarity s) C hb (polarity_bit s) hC) f
  exact GaussianSignedNameExponentialOrder.constant_input _ _ (bound_congr (.eqRefl _) (.eqRefl _) (one_mul one) b)

theorem same_input_rate (p q a b C D A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (hb : Γ ⊢[PRAAx] le one b) (hC : Γ ⊢[PRAAx] le (a*A) (C*(b*B))) (hD : Γ ⊢[PRAAx] le (a*A) (D*(b*B))) : Γ ⊢[PRAAx]
    distanceBounded (quotient p a b C A B) (quotient q a b D A B)
      (B*((unit p+unit q)+(unit p+unit q))) (unit p*unit q) := by
  let h := unit p+unit q
  let W := unit p*unit q
  let k := multiplier A B
  let f (s : Bool) := coefficient (a*A) (b*B) (polarity s)
  let xp := row p (f true) (C*one) one one
  let xn := row p (f false) (C*one) one one
  let yp := row q (f true) (D*one) one one
  let yn := row q (f false) (D*one) one one
  have wb : Γ ⊢[PRAAx] le one (b*B) := positive_product _ _ hb hB
  have hW : Γ ⊢[PRAAx] le one W := positive_product _ _ (unit_positive p) (unit_positive q)
  have rows (s : Bool) : Γ ⊢[PRAAx] distanceBounded (row p (f s) (C*one) one one) (row q (f s) (D*one) one one) h W :=
    cross_at _ _ _ _ p q (GaussianExponentialRadiusIndependence.same_input_cross constantF (C*one) (D*one)
      (exponent (f s) one one) (row_input s (a*A) (b*B) C wb hC) (row_input s (a*A) (b*B) D wb hD))
  have d := GaussianNamedDifference.difference_distance xp yp xn yn h h W hW (rows true) (rows false)
  exact distance_congr (qmul_associative _ _ _ ) (qmul_associative _ _ _) (.eqRefl _) (.eqRefl _)
    (GaussianApproximateInverseDistance.multiply_distance k _ _ B _ W hW (multiplier_bound A B hA hB) d)

end LeanProofs.IPRA.Analysis.GaussianBinetSineQuotientClock
