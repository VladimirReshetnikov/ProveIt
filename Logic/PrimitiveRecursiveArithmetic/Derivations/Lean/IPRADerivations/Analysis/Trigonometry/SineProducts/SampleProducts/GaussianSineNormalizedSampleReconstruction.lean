import IPRADerivations.Analysis.Trigonometry.SineProducts.SampleProducts.GaussianSineNormalizedSampleProduct
import IPRADerivations.Analysis.Trigonometry.SineProducts.Roots.GaussianSineSampleRootGuards

/-!
# Evaluation of the normalized sampled sine product

The folded product is multiplied by the actual polynomial sample at
four. Its error from the normalized polynomial uses the reconstruction
estimates at four and at the sampled squared trace. The only division
in the comparison is by the positive odd natural degree parameter.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianSineNormalizedSampleReconstruction

open_ipra
open ComplexLogarithmRemainder (oneCode normSq_one scale)
open GaussianArctangentDivisionAngles (modulus)
open GaussianArctangentDivisionAngleResidual (positiveBudget)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same distance_radius_mono)
open GaussianRationalHorner (evaluate qmul ofGaussian ofGaussian_represents canonical_unique positive_product)
open GaussianRationalMetric (bounded bounded_of_cleared distanceBounded qsub)
open GaussianRationalNaturalScale (naturalPoint natScale natScale_as_product natScale_canonical natScale_represents)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (qone qone_represents_scaled qone_bounded bound_congr bounded_product bounded_difference_one)
open GaussianRationalReconstruction (product)
open GaussianRationalSeparatedReconstruction (errorNumerator)
open GaussianRationalSyntheticDivision (qone_canonical)
open GaussianSineNormalizedSampleProduct (normalizedProduct productBudget canonical_product folded_identity product_bound)
open GaussianSineSampleRootGuards (fine clock clock_fine clock_later sineDenominator rootDenominator sine_margins
  sine_denominator_positive reconstruction_at normalization_at)
open GaussianSineSampleRootList (roots)
open GaussianSineSquaredPolynomial (coefficients)
open GaussianSineSquaredTrace (fromSine)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def inverseOdd (J : PTm n) : PTm n := ofGaussian oneCode (modulus J)
def normalizedValue (J y : PTm n) : PTm n := qmul (inverseOdd J) (evaluate (coefficients J) y)
def traceBudget (B : PTm n) : PTm n := num 4*(one+B*B)
def reconstructionBudget (J C : PTm n) : PTm n :=
  errorNumerator (sineDenominator J*positiveBudget J) (rootDenominator J) J (C+num 8) J
def normalizedBudget (J B : PTm n) : PTm n :=
  productBudget B (sineDenominator J) J*reconstructionBudget J (num 4)+reconstructionBudget J (traceBudget B)

ipra_subst inverseOdd

ipra_subst normalizedValue

ipra_subst normalizedBudget [reconstructionBudget, traceBudget, positiveBudget, two, one]

theorem inverse_odd_unit (J : PTm n) :
    Γ ⊢[PRAAx] qmul (inverseOdd J) (naturalPoint (modulus J)) ≐ qone := by
  let m := modulus J
  have hm : Γ ⊢[PRAAx] le one m := zero_lt_succ _
  have r : Γ ⊢[PRAAx] natScale m (inverseOdd J) ≐ qone :=
    canonical_unique _ _ (scale m oneCode) m (natScale_canonical _ _) qone_canonical hm
      (natScale_represents _ _ _ _ hm (ofGaussian_represents _ _ hm)) (qone_represents_scaled _)
  exact (qmul_commutative _ _).eqTrans ((natScale_as_product _ _).eqSymm.eqTrans r)

theorem inverse_odd_bound (J : PTm n) : Γ ⊢[PRAAx] bounded (inverseOdd J) one one := by
  let m := modulus J
  have hm : Γ ⊢[PRAAx] le one m := zero_lt_succ _
  apply bounded_of_cleared _ oneCode m one one hm (le_refl _) (ofGaussian_represents _ _ hm)
  exact le_congr (congrMul (.eqRefl _) normSq_one).eqSymm (.eqRefl _) (AnalyticNumberTheory.PhiLower.le_mul_mono
    (le_refl (one*one)) (positive_product m m hm hm))

theorem trace_bound (s B : PTm n) (hs : Γ ⊢[PRAAx] bounded s B one) :
    Γ ⊢[PRAAx] bounded (fromSine s) (traceBudget B) one := by
  have square : Γ ⊢[PRAAx] bounded (qmul s s) (B*B) one :=
    bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring)
      (bounded_product s s B one B one (le_refl _) (le_refl _) hs hs)
  have complement : Γ ⊢[PRAAx] bounded (qsub qone (qmul s s)) (one+B*B) one :=
    bounded_difference_one qone_bounded square
  exact bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring)
    (bounded_product _ _ _ _ _ _ (le_refl _) (le_refl _) (GaussianNamedNaturalScale.natural_point_bound (num 4)) complement)

private theorem right_product_distance (a b t H K T : PTm n) (hk : Γ ⊢[PRAAx] le one K)
    (ht : Γ ⊢[PRAAx] bounded t T one) (h : Γ ⊢[PRAAx] distanceBounded a b H K) :
    Γ ⊢[PRAAx] distanceBounded (qmul a t) (qmul b t) (T*H) K :=
  distance_congr (qmul_commutative _ _) (qmul_commutative _ _) (.eqRefl _) (by ipra_ring)
    (bound_congr (GaussianRationalRoundedPower.multiplication_difference t a b).eqSymm (.eqRefl _) (.eqRefl _)
      (bounded_product t (qsub a b) T one H K (le_refl _) hk ht h))

theorem normalized_distance (p J z s B : PTm n) (hf : Γ ⊢[PRAAx] fine p J) (hs : Γ ⊢[PRAAx] bounded s B one) :
    Γ ⊢[PRAAx] distanceBounded (normalizedProduct p J z s) (normalizedValue J (fromSine s)) (normalizedBudget J B) (unit p) := by
  let y := fromSine s
  let a := naturalPoint (modulus J)
  let b := product (roots p J z) J (naturalPoint (num 4))
  let t := normalizedProduct p J z s
  let u := product (roots p J z) J y
  let w := evaluate (coefficients J) y
  let W := unit p
  let D := sineDenominator J
  let P := productBudget B D J
  let C := reconstructionBudget J (num 4)
  let E := reconstructionBudget J (traceBudget B)
  have ht : Γ ⊢[PRAAx] bounded t P one :=
    product_bound p J z s B D (sine_denominator_positive J) hs (sine_margins p J z hf)
  have eq : Γ ⊢[PRAAx] qmul b t ≐ u :=
    folded_identity p J z s B D (sine_denominator_positive J) hs (sine_margins p J z hf)
  have first : Γ ⊢[PRAAx] distanceBounded a b C W := normalization_at p J z hf
  have second : Γ ⊢[PRAAx] distanceBounded w u E W := reconstruction_at p J z y (traceBudget B) hf (trace_bound s B hs)
  have scaled := distance_congr (.eqRefl _) eq (.eqRefl _) (.eqRefl _)
    (right_product_distance a b t C W P (unit_positive p) ht first)
  have error := distance_triangle_same (qmul a t) u w (P*C) E W (unit_positive p) scaled
    (distance_symmetric _ _ _ _ (unit_positive p) second)
  have normalized := GaussianRationalRoundedPower.multiply_distance_bound (inverseOdd J) (qmul a t) w _ W
    (unit_positive p) (inverse_odd_bound J) error
  exact distance_congr (GaussianRationalInverseQuadraticAlgebra.cancel_nested_product _ _ _
    (canonical_product p J z s) (inverse_odd_unit J)) (.eqRefl _) (.eqRefl _) (.eqRefl _) normalized

theorem cofinal_normalized_distance (p J z s B : PTm n) (hs : Γ ⊢[PRAAx] bounded s B one) :
    Γ ⊢[PRAAx] distanceBounded (normalizedProduct (clock p J) J z s) (normalizedValue J (fromSine s))
      (normalizedBudget J B) (unit p) :=
  distance_radius_mono _ _ _ _ _ _ (unit_positive _) (unit_positive _)
    (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl _) (GaussianExponentialReference.unit_monotone (clock_later p J)))
    (normalized_distance _ _ _ _ _ (clock_fine _ _) hs)

theorem actual_cofinal_normalized_sine_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (bounded (var 3) (var 4) one ⟶ distanceBounded (normalizedProduct (clock (var 0) (var 1)) (var 1) (var 2) (var 3))
      (normalizedValue (var 1) (fromSine (var 3))) (normalizedBudget (var 1) (var 4)) (unit (var 0))) :=
  closeUniv 5 (.impI (cofinal_normalized_distance _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianSineNormalizedSampleReconstruction
