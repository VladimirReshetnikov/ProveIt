import IPRADerivations.Analysis.Trigonometry.SineProducts.SampleProducts.GaussianSineNormalizedSampleReconstruction
import IPRADerivations.Analysis.Polynomials.Horner.GaussianRationalHornerLipschitz

/-!
# Variation of the normalized sine polynomial

A sum of natural bounds on the actual stored coefficients gives an
explicit Horner coefficient budget. The squared-trace transformation
and division by the odd order give a uniform sample variation bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianSinePolynomialVariation

open_ipra
open ComplexLogarithmRemainder (normSq)
open GaussianCoefficientNameBounds (bounded_radius_mono)
open GaussianEuclideanResidualRadius (coefficientBounds)
open GaussianRationalHorner (qmul)
open GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open GaussianRationalMetric (bounded bounded_of_cleared distanceBounded qsub)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianSineNormalizedSampleReconstruction (traceBudget trace_bound normalizedValue inverseOdd inverse_odd_bound)
open GaussianSineRootNormalization (trace_difference)
open GaussianSineSquaredTrace (fromSine)
open GaussianSineSquaredPolynomial (coefficients coefficients_length)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def pointBound (q : PTm n) : PTm n := normSq (rawGaussian q)+one
def boundBody : PTm 2 := pointBound (entry (var 1) (var 0))
def coefficientBound (C : PTm n) : PTm n := ap2 (sumF boundBody) (length C) C
def variationBudget (J B : PTm n) : PTm n :=
  GaussianRationalHornerLipschitz.constant J (traceBudget B) (coefficientBound (coefficients J))*(num 8*B)

ipra_subst coefficientBound

ipra_subst variationBudget [GaussianRationalHornerLipschitz.constant, traceBudget, one]

theorem point_bound (q : PTm n) : Γ ⊢[PRAAx] bounded q (pointBound q) one := by
  let a := rawGaussian q
  let d := rawDen q
  let w := pointBound q
  have hD := raw_den_positive (Γ := Γ) q
  have e : Γ ⊢[PRAAx] le (normSq a) (w*w) :=
    le_of_eq_add (d := normSq a*normSq a+normSq a+one) (by dsimp only [w,pointBound,a]; ipra_ring)
  have range := le_mul_mono e (le_mul_mono hD hD)
  exact bounded_of_cleared _ _ _ _ _ hD (le_refl _) (raw_represents q)
    (le_congr (by ipra_ring) (.eqRefl _) range)

theorem coefficients_bound (C : PTm n) : Γ ⊢[PRAAx] coefficientBounds C (coefficientBound C) := by
  refine .allI (.impI ?_)
  let X := Syn.shift C
  let j : PTm (n+1) := var 0
  let Δ := lt j (length X) :: Γ.map Fm.shift
  have term : Δ ⊢[PRAAx] le (pointBound (entry X j)) (coefficientBound X) := by
    simpa [boundBody,LeanProofs.IPRA.inst2,coefficientBound,pointBound] using
      term_le_sum boundBody (i := j) (M := length X) (x := X) (Prf.hyp0 : Δ ⊢[PRAAx] lt j (length X))
  have h : Δ ⊢[PRAAx] bounded (entry X j) (coefficientBound X) one :=
    bounded_radius_mono _ _ _ _ _ (le_refl _) (le_refl _) (mul_le_mul_right _ term) (point_bound _)
  simpa [coefficientBounds,Δ,Syn.shift,X,j] using h

theorem trace_distance (s t B H K : PTm n) (hk : Γ ⊢[PRAAx] le one K)
    (hs : Γ ⊢[PRAAx] bounded s B one) (ht : Γ ⊢[PRAAx] bounded t B one)
    (h : Γ ⊢[PRAAx] distanceBounded s t H K) :
    Γ ⊢[PRAAx] distanceBounded (fromSine s) (fromSine t) ((num 8*B)*H) K := by
  have square := GaussianNameArithmetic.product_distance s t s t H H K B B hk h h hs ht
  have opposite := distance_symmetric _ _ _ _ hk square
  have scalar := GaussianNamedNaturalScale.natural_point_bound (Γ := Γ) (num 4 : PTm n)
  exact bound_congr (trace_difference s t).eqSymm (by ipra_ring) (by ipra_ring)
    (bounded_product (naturalPoint (num 4)) (qsub (qmul t t) (qmul s s)) (num 4) one _ K (le_refl _) hk scalar opposite)

theorem normalized_value_distance (J s t B H K : PTm n) (hk : Γ ⊢[PRAAx] le one K)
    (hs : Γ ⊢[PRAAx] bounded s B one) (ht : Γ ⊢[PRAAx] bounded t B one)
    (h : Γ ⊢[PRAAx] distanceBounded s t H K) :
    Γ ⊢[PRAAx] distanceBounded (normalizedValue J (fromSine s)) (normalizedValue J (fromSine t)) (variationBudget J B*H) K :=
  distance_congr (.eqRefl _) (.eqRefl _) (by unfold variationBudget; ipra_ring) (.eqRefl _)
    (GaussianRationalRoundedPower.multiply_distance_bound (inverseOdd J) _ _ _ K hk (inverse_odd_bound J)
      (GaussianRationalHornerLipschitz.evaluation_bound (coefficients J) (fromSine s) (fromSine t) J (traceBudget B) _ _ K
        (coefficients_length J) (coefficients_bound _) (trace_bound s B hs) (trace_bound t B ht) hk
        (trace_distance s t B H K hk hs ht h)))

theorem actual_normalized_sine_polynomial_variation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le one (var 5) ⋏ bounded (var 1) (var 3) one ⋏ bounded (var 2) (var 3) one) ⟶
      distanceBounded (var 1) (var 2) (var 4) (var 5) ⟶
      distanceBounded (normalizedValue (var 0) (fromSine (var 1))) (normalizedValue (var 0) (fromSine (var 2)))
        (variationBudget (var 0) (var 3)*var 4) (var 5)) :=
  closeUniv 6 (.impI (.impI (normalized_value_distance _ _ _ _ _ _
    Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianSinePolynomialVariation
