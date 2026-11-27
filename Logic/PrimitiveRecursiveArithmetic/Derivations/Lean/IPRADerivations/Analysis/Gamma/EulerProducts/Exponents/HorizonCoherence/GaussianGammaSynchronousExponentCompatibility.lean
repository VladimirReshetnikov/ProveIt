import IPRADerivations.Analysis.Gamma.EulerProducts.Exponents.HorizonCoherence.GaussianGammaSynchronousExponentName

/-!
# The actual shared-clock exponent is the original canonical C7 exponent

Original gamma and tail regularities, together with the actual arithmetic
sample-error theorems, give a finite diagonal envelope. Both actual names
are regular, so finite slack removal proves independent-precision name
equivalence. No limiting exponent equality is an input assumption.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaSynchronousExponentCompatibility

open_ipra
open GaussianRationalHorner (qadd qmul ofGaussian)
open GaussianRationalMetric (bounded distanceBounded qnegative)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open GaussianRationalReciprocal (bound_congr)
open GaussianGammaCanonicalExponent (source harmonicPoint constantF constant_at constant_regular gammaF gamma_regular
  differenceF differenceData difference_regular productF productData product_regular exponentF exponentData exponentPoint exponent_regular)
open GaussianGammaSynchronousExponentName (gammaClock rawValue linearValue sample rawData rawF)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNameRingLaws (three)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def differencePoint (p R : PTm n) : PTm n := ap2 differenceF p (differenceData (two*R))
def productPoint (p z R B : PTm n) : PTm n := ap2 productF p (productData z B (two*R))
def productModulus (z R B : PTm n) : PTm n := GaussianNameArithmetic.multiplyModulus differenceF constantF
  (differenceData (two*R)) (ofGaussian z B)
def cost (z R B : PTm n) : PTm n := num 6*R+productModulus z R B+num 8
ipra_subst productModulus
ipra_subst cost

theorem shared_coefficient_error (p R : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (GaussianGammaLinearCoefficient.coefficient (gammaClock p R) (two*R))
      (GaussianGammaLinearCoefficient.coefficient p (two*R)) two (unit p) := by
  have raw := GaussianNameRingLaws.sum_left_error (Γ := Γ) _ _ (qnegative (harmonicPoint (two*R))) _ _
    (GaussianRationalHorner.positive_product _ _ (unit_positive p) (unit_positive p))
    (GaussianGammaSynchronousExponentName.gamma_later_distance p p _ p
      (GaussianGammaSynchronousExponentName.gamma_clock_later p R) (le_refl p))
  exact distance_radius_mono _ _ _ _ _ _
    (GaussianRationalHorner.positive_product _ _ (unit_positive p) (unit_positive p)) (unit_positive p)
    (le_of_eq_add (d := zero) (by ipra_ring)) raw

theorem original_difference_error (p R : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (differencePoint p R) (GaussianGammaLinearCoefficient.coefficient p (two*R)) three (unit p) :=
  distance_congr (.eqRefl _)
    (qadd_congr (GaussianGammaCanonicalExponent.gamma_sample_at p) (constant_at p (qnegative (harmonicPoint (two*R)))))
      (.eqRefl _) (.eqRefl _)
      (GaussianNameRingLaws.add_sample_error gammaF constantF zero (qnegative (harmonicPoint (two*R))) p gamma_regular (constant_regular _))

theorem coefficient_sample_error (p R : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (GaussianGammaLinearCoefficient.coefficient (gammaClock p R) (two*R)) (differencePoint p R) (num 5) (unit p) :=
  bound_congr (.eqRefl _) (show Γ ⊢[PRAAx] two+three ≐ num 5 by unfold three; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) (shared_coefficient_error p R)
      (distance_symmetric _ _ _ _ (unit_positive p) (original_difference_error p R)))

theorem linear_sample_error (p z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    distanceBounded (linearValue p z R B) (qmul (differencePoint p R) (ofGaussian z B)) (num 5*R) (unit p) := by
  have oldBound : Γ ⊢[PRAAx] bounded (differencePoint p R) (one+two*R) one :=
    bound_congr (GaussianGammaCanonicalExponent.difference_sample_at p (two*R)).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianGammaCanonicalExponentBound.difference_value_bound p (two*R))
  exact bound_congr (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianNameArithmetic.product_distance _ _ _ _ (num 5) zero (unit p) R (one+two*R) (unit_positive p)
      (coefficient_sample_error p R) (GaussianRationalPowerDifference.distance_refl_zero _ _ (unit_positive p))
      (GaussianGammaSynchronousExponentName.query_bound z R B h) oldBound)

theorem original_product_error (p z R B : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (productPoint p z R B) (qmul (differencePoint p R) (ofGaussian z B)) (productModulus z R B+one) (unit p) :=
  distance_congr (.eqRefl _) (qmul_congr (.eqRefl _) (constant_at p (ofGaussian z B))) (.eqRefl _) (.eqRefl _)
    (GaussianNameRingLaws.multiply_sample_error differenceF constantF (differenceData (two*R)) (ofGaussian z B) p
      (difference_regular (two*R)) (constant_regular _))

theorem raw_product_error (p z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    distanceBounded (linearValue p z R B) (productPoint p z R B) (num 5*R+productModulus z R B+one) (unit p) :=
  bound_congr (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) (linear_sample_error p z R B h)
      (distance_symmetric _ _ _ _ (unit_positive p) (original_product_error p z R B)))

theorem original_tail_error (p z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    distanceBounded (GaussianGammaZetaTailSeries.sample p z R B (two*R))
      (GaussianGammaCanonicalTailName.point p z R B (two*R)) two (unit p) := by
  have he := GaussianNameEquivalence.cross_at GaussianGammaZetaTailSeries.nameF GaussianGammaCanonicalTailName.pointF
    (GaussianGammaZetaTailSeries.data z R B (two*R)) (GaussianGammaCanonicalTailName.data z R B (two*R)) p p
    (GaussianGammaZetaTailSeries.original_C16_name_identity z R B (two*R) (GaussianGammaCanonicalExponent.tail_source z R B h))
  exact distance_radius_mono _ _ _ _ _ _
    (GaussianRationalHorner.positive_product _ _ (unit_positive p) (unit_positive p)) (unit_positive p)
    (le_of_eq_add (d := zero) (by ipra_ring)) he

theorem original_exponent_error (p z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    distanceBounded (rawValue p z R B) (exponentPoint p z R B) (num 5*R+productModulus z R B+num 6) (unit p) := by
  have addError := GaussianNameRingLaws.add_sample_error productF GaussianGammaCanonicalTailName.pointF
    (productData z B (two*R)) (GaussianGammaCanonicalTailName.data z R B (two*R)) p
    (product_regular z B (two*R))
    (GaussianGammaCanonicalTailName.name_regular z R B (two*R) (GaussianGammaCanonicalExponent.tail_source z R B h))
  have rawError := GaussianNameArithmetic.sum_distance (Γ := Γ) _ _ _ _ _ _ _ (unit_positive p)
    (raw_product_error p z R B h) (original_tail_error p z R B h)
  exact bound_congr (.eqRefl _) (by unfold three; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) rawError
      (distance_symmetric _ _ _ _ (unit_positive p) addError))

theorem normalized_error (p z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    distanceBounded (sample p z R B) (exponentPoint p z R B) (cost z R B) (unit p) := by
  have front := distance_congr (.eqRefl _) (GaussianGammaSynchronousExponentName.raw_at p z R B) (.eqRefl _) (.eqRefl _)
    (GaussianNameRingLaws.normalized_to_sample rawF (R+one) (rawData z R B) p
      (GaussianGammaSynchronousExponentName.raw_name_regular z R B h))
  exact bound_congr (.eqRefl _) (by unfold cost; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) front (original_exponent_error p z R B h))

theorem diagonal_envelope (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    GaussianValueNormalizerExtensionality.rawDiagonal GaussianGammaSynchronousExponentName.nameF exponentF
      (GaussianGammaSynchronousExponentName.data z R B) (exponentData z R B) (cost z R B) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,GaussianGammaSynchronousExponentName.subst_data,
    GaussianGammaCanonicalExponent.subst_exponentData,subst_cost,GaussianGammaSynchronousExponentName.sample,
    exponentPoint,GaussianCoefficientNameBounds.unit] using
      normalized_error (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) hs

theorem original_exponent_identity (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    crossEquivalent GaussianGammaSynchronousExponentName.nameF exponentF
      (GaussianGammaSynchronousExponentName.data z R B) (exponentData z R B) :=
  GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ _
    (GaussianGammaSynchronousExponentName.name_regular z R B h) (exponent_regular z R B h) (diagonal_envelope z R B h)

theorem actual_shared_clock_is_original_C7_exponent_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) (var 2) ⟶ crossEquivalent GaussianGammaSynchronousExponentName.nameF exponentF
      (GaussianGammaSynchronousExponentName.data (var 0) (var 1) (var 2)) (exponentData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (original_exponent_identity _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaSynchronousExponentCompatibility
