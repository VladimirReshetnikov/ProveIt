import IPRADerivations.Analysis.GaussianEulerIntegrandName
import IPRADerivations.Analysis.GaussianNaturalExponentialDyadicBound
import IPRADerivations.Analysis.GaussianPositiveRationalExponentialDecay
import IPRADerivations.Analysis.GaussianNameConjugation

/-!
# Bounds on the original decay factor of the Euler integrand

The original Euler sampler uses the exponential of a constant negative
rational point. Its independently clocked name equals the explicit
reciprocal of the positive exponential. This transfers the exact
integer dyadic bound and the factorial monomial bound at the half
argument to the actual original integrand factor.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerDecayFactorBounds

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIntegrandName (decayF decayData decayPoint)
open GaussianPositiveRationalExponentialDecay
  (expF negF negData inverseData inverseQuery inverse_sample_at degree_in_cutoff
    named_negative_is_reciprocal actual_positive_input exact_reciprocal_weighted_decay doubled_monomial)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianRationalPolynomialExponential (scalarSum scalarBody)
open GaussianDominantPairAlgebra (radiusPoint radiusNumerator radius_represents radius_bounded radius_power)
open GaussianRationalHorner (ofGaussian positive_product canonical_unique represents_congr qmul qmul_canonical qzero)
open GaussianRationalMetric (bounded qnegative qsub)
open GaussianRationalReciprocal (reciprocal power bound_congr bounded_product bounded_sum)
open GaussianRationalSyntheticDivision (qsub_congr qmul_congr qzero_add)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans cross_to_diagonal diagonal_at)
open GaussianNameRingLaws (negativeF negativeData negative_at negative_fast)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRootAlgebra (equal_of_values)
open Products (fact)
open ComplexLogarithmRemainder (scale oneCode)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem fraction_is_radius_point (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.fraction a b ≐ radiusPoint a b := by
  apply canonical_unique _ _ (radiusNumerator a) b
    (GaussianRationalHorner.ofGaussian_canonical _ _ hb) (GaussianRationalHorner.ofGaussian_canonical _ _ hb) hb
    (hrv := radius_represents a b hb)
  apply represents_congr (.eqRefl _) _ (.eqRefl _)
    (GaussianRationalHorner.ofGaussian_represents (scale a oneCode) b hb)
  apply equal_of_values
  all_goals
    try simp only [radiusNumerator, GaussianRootAlgebra.re_scale, GaussianRootAlgebra.im_scale,
      GaussianRootAlgebra.re_one, GaussianRootAlgebra.im_one, ComplexLogarithmRemainder.eval_re_code,
      ComplexLogarithmRemainder.eval_im_code, ZT.toZ_ofNat]
    try ipra_simps
    ring

theorem negative_constant_at (a b p : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] ap2 (negativeF constantF) p (negativeData (radiusPoint a b)) ≐ decayPoint a b := by
  let w := radiusPoint a b
  let u := GaussianPositiveRationalLogarithm.fraction a b
  let k := GaussianFastValueCut.exponent (one+one) p
  have e : Γ ⊢[PRAAx] qsub qzero (ap2 constantF k w) ≐ decayPoint a b :=
    (qsub_congr (.eqRefl _) ((constant_at k w).eqTrans (fraction_is_radius_point a b hb).eqSymm)).eqTrans
      (qzero_add (qnegative u) (GaussianRationalMetric.qnegative_canonical u))
  exact (negative_at constantF w p).eqTrans ((GaussianNameArithmetic.recode_congr e).eqTrans
    (GaussianExponentialReference.recode_fixed _ (GaussianRationalMetric.qnegative_canonical u)))

theorem negative_constant_cross (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] crossEquivalent (negativeF constantF) constantF
      (negativeData (radiusPoint a b)) (decayPoint a b) := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _
    (negative_fast _ _ (constant_regular _)) (constant_regular _)
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift b) := by simpa [Fm.shift, Syn.shift] using hb.shift
  simpa only [GaussianNameConjugation.pointwiseEqual, Syn.shift, GaussianNameRingLaws.subst_negativeData,
    GaussianDominantPairAlgebra.subst_radiusPoint, GaussianEulerIntegrandName.subst_decayPoint] using
    (negative_constant_at (Syn.shift a) (Syn.shift b) (var 0) hs).eqTrans (constant_at _ _).eqSymm

theorem original_decay_matches_reciprocal (a b j : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianNameReciprocal.nameF expF) decayF (inverseData a b j) (decayData a b) := by
  let x := radiusPoint a b
  let y := decayPoint a b
  let R := a+j
  let S := GaussianNameBounds.U constantF y
  have h := GaussianExponentialInverse.negative_input constantF R x (actual_positive_input a b j hb)
  have hy := GaussianGammaFiniteApproximantName.exponential_input constantF y (constant_regular (Γ := Γ) y)
  have e : Γ ⊢[PRAAx] crossEquivalent negF decayF (negData a b j) (decayData a b) :=
    GaussianExponentialRadiusIndependence.independent_radii_proper (negativeF constantF) constantF
      R S (negativeData x) y h hy (negative_constant_cross a b hb)
  exact cross_trans _ _ _ _ _ _ (named_negative_is_reciprocal a b j hb) e

theorem natural_inverse_sample_bound (R p : PTm n) :
    Γ ⊢[PRAAx] bounded (ap2 (GaussianNameReciprocal.nameF expF) p (inverseData R one R)) one (unit R) := by
  let K := GaussianRadiusExponentialName.index (R+R) (inverseQuery p)
  have ha := GaussianNaturalExponentialDyadicBound.original_natural_scalar_dyadic_lower (Γ := Γ) R K
    (degree_in_cutoff R R (inverseQuery p))
  have same : Γ ⊢[PRAAx] naturalPoint R ≐ radiusPoint R one := fraction_is_radius_point R one (le_refl one)
  have base := GaussianRationalLowerBounds.lower_congr
    (GaussianRationalFiniteSum.sum_index_congr scalarBody (.eqRefl (succ K)) same) (.eqRefl _) (.eqRefl _) ha
  exact bound_congr (inverse_sample_at R one R p).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianRationalLowerBounds.inverse_bound _ _ _ (unit_positive R) (le_refl one) base)

theorem original_integer_decay_bound (R p : PTm n) :
    Γ ⊢[PRAAx] bounded (ap2 decayF p (decayData R one)) (unit p+two*unit R) (unit R*unit p) := by
  let F := GaussianNameReciprocal.nameF expF
  let x := ap2 decayF p (decayData R one)
  let y := ap2 F p (inverseData R one R)
  have e := cross_symm (Γ := Γ) F decayF (inverseData R one R) (decayData R one)
    (original_decay_matches_reciprocal R one R (le_refl one))
  have d := diagonal_at _ _ _ _ p (cross_to_diagonal _ _ _ _ e)
  have hcan : Γ ⊢[PRAAx] GaussianRationalHorner.canonical x :=
    GaussianRadiusExponentialName.sample_canonical constantF _ p (decayPoint R one)
  exact bound_congr (GaussianRationalLinearProduct.add_sub_right y x hcan) (by ipra_ring) (.eqRefl _)
    (bounded_sum y (qsub x y) one (unit R) two (unit p)
      (unit_positive R) (unit_positive p) (natural_inverse_sample_bound R p) d)

theorem original_half_decay_factor_bound (a b j p : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] bounded (qmul (power (radiusPoint (two*a) b) j) (ap2 decayF p (decayData a b)))
      (unit j*fact j*unit p+two*pw (two*a) j) (unit p) := by
  let F := GaussianNameReciprocal.nameF expF
  let w := power (radiusPoint (two*a) b) j
  let x := ap2 decayF p (decayData a b)
  let y := ap2 F p (inverseData a b j)
  let A := radiusPoint (unit j) one
  have repr : Γ ⊢[PRAAx] qmul w y ≐ qmul A (qmul (power (radiusPoint a b) j) y) :=
    (qmul_congr (doubled_monomial a b j hb) (.eqRefl y)).eqTrans
      (GaussianReciprocalHorner.qmul_associative A (power (radiusPoint a b) j) y)
  have exactBound : Γ ⊢[PRAAx] bounded (qmul w y) (unit j*fact j) one :=
    bound_congr repr.eqSymm (.eqRefl _) (one_mul _) (bounded_product A _ _ one _ one
      (le_refl one) (le_refl one) (radius_bounded (unit j) one (le_refl one))
      (exact_reciprocal_weighted_decay a b j p ha hb))
  have e := cross_symm F decayF (inverseData a b j) (decayData a b) (original_decay_matches_reciprocal a b j hb)
  have d := diagonal_at _ _ _ _ p (cross_to_diagonal _ _ _ _ e)
  have hY := GaussianPolynomialPerturbation.power_positive b j hb
  have wBound : Γ ⊢[PRAAx] bounded w (pw (two*a) j) one :=
    bound_congr (radius_power (two*a) b j hb).eqSymm (.eqRefl _) (.eqRefl _)
      (bounded_radius_mono _ _ _ _ _ hY (le_refl one)
        (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (pw (two*a) j) hY))
        (radius_bounded (pw (two*a) j) (pw b j) hY))
  have near := GaussianApproximateInverseDistance.multiply_distance w x y (pw (two*a) j) two (unit p)
    (unit_positive p) wBound d
  exact bound_congr (GaussianRationalLinearProduct.add_sub_right (qmul w y) (qmul w x) (qmul_canonical w x))
    (by ipra_ring) (one_mul _)
    (bounded_sum (qmul w y) (qsub (qmul w x) (qmul w y)) (unit j*fact j) one (pw (two*a) j*two) (unit p)
      (le_refl one) (unit_positive p) exactBound near)

theorem original_Euler_decay_integer_dyadic_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (bounded (ap2 decayF (var 1) (decayData (var 0) one))
      (unit (var 1)+two*unit (var 0)) (unit (var 0)*unit (var 1))) :=
  closeUniv 2 (original_integer_decay_bound _ _)

theorem original_Euler_decay_half_argument_monomial_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 0) ⟶ le one (var 1) ⟶
      bounded (qmul (power (radiusPoint (two*var 0) (var 1)) (var 2)) (ap2 decayF (var 3) (decayData (var 0) (var 1))))
        (unit (var 2)*fact (var 2)*unit (var 3)+two*pw (two*var 0) (var 2)) (unit (var 3))) :=
  closeUniv 4 (.impI (.impI (original_half_decay_factor_bound _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEulerDecayFactorBounds
