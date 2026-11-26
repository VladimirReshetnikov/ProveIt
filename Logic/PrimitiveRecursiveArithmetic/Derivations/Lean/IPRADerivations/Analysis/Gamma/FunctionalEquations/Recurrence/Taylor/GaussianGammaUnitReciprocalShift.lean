import IPRADerivations.Analysis.Gamma.EulerProducts.Derivatives.GaussianGammaUnitEulerDifference
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.GaussianGammaRepeatedShift
import IPRADerivations.Analysis.Gamma.Names.Input.GaussianGammaInputProperness

/-!
# The observed reciprocal Gamma shift for positive steps at one

The repeated-shift proof at index zero supplies the original reciprocal
Gamma product at a shared query. The shifted point is transported to the
actual encoding used in the Euler divided difference. The resulting
observation bound has a numerical constant independent of the step's
native denominator.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaUnitReciprocalShift

open_ipra
open GaussianGammaC7Name (sample nameF data)
open GaussianGammaRepeatedShift (stage C7_data_congr stage_zero stepCost)
open GaussianGammaShiftTrajectory (point point_source point_zero point_linear point_native)
open ComplexLogarithmRemainder (oneCode normSq_one)
open GaussianGammaC7Name (sample_canonical)
open GaussianRootAlgebra (equal equal_of_values equal_of_code re_add im_add re_scale im_scale re_one im_one)
open GaussianRationalHorner (ofGaussian qmul positive_product)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def neighbor (D : PTm n) : PTm n := GaussianEulerParameterExponentialIncrement.shifted oneCode one oneCode D
def small (t D : PTm n) : PTm n := sample t oneCode one D
def large (t D : PTm n) : PTm n := sample t (neighbor D) (one+one) (one*D)
def step (D : PTm n) : PTm n := ofGaussian oneCode D

theorem small_source (D : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    GaussianGammaCanonicalExponent.source oneCode one D :=
  .andI (le_refl one) (.andI hD
    (le_congr normSq_one.eqSymm (by ipra_ring) (positive_product _ _ hD hD)))

theorem native_shift (D : PTm n) : Γ ⊢[PRAAx] equal (point oneCode D (succ zero)) (neighbor D) := by
  refine GaussianRootAlgebra.equal_trans (point_native oneCode D (succ zero)) ?_
  apply equal_of_values <;>
    simp only [neighbor,GaussianGammaEulerHeadLower.translated,GaussianEulerParameterExponentialIncrement.shifted,
      re_add,im_add,re_scale,im_scale,re_one,im_one,Q.mk_mul,map_mul,map_one,
      Q.mk_succ,Q.mk_zero,map_add,map_zero] <;> ring

theorem original_reciprocal_shift_observations (t D : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    distanceBounded (small t D) (qmul (step D) (large t D)) (num 10) (unit t) := by
  let Z := point oneCode D (succ zero)
  let V := sample t Z (one+one) D
  let W := sample t (neighbor D) (one+one) D
  let S := step D
  have smallSource := small_source D hD
  have traceSource : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source Z (one+one) D :=
    point_source oneCode one D (succ zero) smallSource
  have factor : Γ ⊢[PRAAx] GaussianGammaEulerHeadShift.linear oneCode D zero ≐ S :=
    (point_linear oneCode D zero hD).eqSymm.eqTrans
      (GaussianGammaFiniteValueProperness.fraction_equal _ _ D hD (equal_of_code (point_zero oneCode D)))
  have trace := GaussianGammaRepeatedShift.stage_step_error t oneCode one D one zero smallSource (zero_le one)
  have start : Γ ⊢[PRAAx] distanceBounded (small t D) (qmul S V) (num 8) (unit t) :=
    distance_congr (stage_zero t oneCode one D) (qmul_congr factor (.eqRefl _))
      (by unfold stepCost GaussianGammaRepeatedShift.factorBound; ipra_ring) (.eqRefl _) trace
  have eqn := GaussianGammaInputProperness.original_C7_proper Z (neighbor D) (one+one) D traceSource (native_shift D)
  have moved : Γ ⊢[PRAAx] distanceBounded V W two (unit t) :=
    GaussianNameEquivalence.cross_diagonal_at t eqn
  have norm := GaussianGammaUnitEulerDifference.increment_bound one D (le_refl one) hD
  have near := GaussianNamedDifferenceQuotient.scale_distance S V W one two (unit t) (unit_positive t) norm moved
  have actual : Γ ⊢[PRAAx] W ≐ large t D :=
    congrAp2 nameF (.eqRefl _) (C7_data_congr (.eqRefl _) (.eqRefl _) (by ipra_ring))
  have combined := distance_triangle_same _ _ _ _ _ _ (unit_positive t) start near
  exact distance_congr (.eqRefl _) (qmul_congr (.eqRefl _) actual) (by ipra_ring) (.eqRefl _) combined

theorem actual_original_reciprocal_unit_shift_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶ distanceBounded (small (var 0) (var 1))
      (qmul (step (var 1)) (large (var 0) (var 1))) (num 10) (unit (var 0))) :=
  closeUniv 2 (.impI (original_reciprocal_shift_observations _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaUnitReciprocalShift
