import IPRADerivations.Analysis.Polynomials.RootFinding.Descent.Monic.GaussianMonicRootSupport
import IPRADerivations.Analysis.Polynomials.RootFinding.Adequacy.GaussianRootCompletedAdequacy

/-!
# Concrete named monic root adequacy and completed distance

The proved fixed GaussianMonicRD.step discharges RD internally. The input
contains only the genuine coefficient and point Cauchy-name conditions,
positive numerical degree, and the original represented disk bound Z.
The source's full root-adequacy conclusion retains its original C_Z and
M_Z constants. Its completed-distance corollary queries the actual PR2
distance and polynomial-value names, and represented membership agrees
with zero of both names. No realization or completed-field axiom is used.
All degrees, disks, stage indices, precisions and persistent data are
numerical; only the fixed coefficient/point program schemas are external.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianMonicRootAdequacy

open_ipra
open LeanProofs.IPRA.Analysis.GaussianMonicRD (step)
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (CN R)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (pointCN)
open LeanProofs.IPRA.Analysis.GaussianRepresentedPointBounds (normLE)
open LeanProofs.IPRA.Analysis.GaussianEuclideanPointDistance (unit)
open LeanProofs.IPRA.Analysis.GaussianRootSupport (coverDenominator)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def input (a : PR 3) (point : PR 2) (N Z x : PTm n) : Fm PTm n :=
  CN a N x ⋏ (le one N ⋏ (le (R a N x) Z ⋏ (pointCN point x ⋏ normLE point Z x)))
def completionInput (a : PR 3) (point : PR 2) (N x : PTm n) : Fm PTm n :=
  CN a N x ⋏ (le one N ⋏ pointCN point x)
def roots (a : PR 3) (N t x : PTm n) : PTm n := GaussianMonicRootSupport.roots a N t x
def rootNameF (a : PR 3) : PR 3 := GaussianMonicRootSupport.rootNameF a
def distanceNameF (a : PR 3) (point : PR 2) : PR 2 := GaussianRootDistanceCompletion.nameF step a point
def distanceData (N x : PTm n) : PTm n := GaussianRootDistanceCompletion.nameData N x
def distanceSample (a : PR 3) (point : PR 2) (N x k : PTm n) : PTm n := GaussianRootDistanceCompletion.sample step a point N x k
def polynomialNameF (a : PR 3) (point : PR 2) : PR 2 := GaussianPolynomialValueName.nameF a point
def polynomialData (N Z x : PTm n) : PTm n := GaussianPolynomialValueName.nameData N (Z+one) x
def member (a : PR 3) (point : PR 2) (N x : PTm n) : Fm PTm n := GaussianRootMembership.member step a point N x
def completedZero (a : PR 3) (point : PR 2) (N x : PTm n) : Fm PTm n := GaussianRootDistanceZero.completedZero step a point N x
def polynomialZero (a : PR 3) (point : PR 2) (N Z x : PTm n) : Fm PTm n := GaussianPolynomialValueName.nameZero a point N (Z+one) x
def sourceConclusion (a : PR 3) (point : PR 2) (N Z x : PTm n) : Fm PTm n := GaussianRootAdequacyTheorem.conclusion step a point N Z x
def conclusion (a : PR 3) (point : PR 2) (N Z x : PTm n) : Fm PTm n := GaussianRootCompletedAdequacy.conclusion step a point N Z x

ipra_subst input
ipra_subst completionInput
ipra_subst roots
ipra_subst distanceData
ipra_subst distanceSample
ipra_subst polynomialData
ipra_subst member
ipra_subst completedZero
ipra_subst polynomialZero
ipra_subst sourceConclusion
ipra_subst conclusion

theorem legacy_input (a : PR 3) (point : PR 2) (N Z x : PTm n) (h : Γ ⊢[PRAAx] input a point N Z x) : Γ ⊢[PRAAx]
    GaussianRootAdequacy.inputContract step a point N Z x := .andI GaussianMonicRD.monic_rd h
theorem completion_legacy_input (a : PR 3) (point : PR 2) (N x : PTm n) (h : Γ ⊢[PRAAx] completionInput a point N x) : Γ ⊢[PRAAx]
    GaussianRootDistanceCompletion.input step a point N x := .andI GaussianMonicRD.monic_rd h
theorem completion_input_from_input (a : PR 3) (point : PR 2) (N Z x : PTm n)
    (h : Γ ⊢[PRAAx] input a point N Z x) : Γ ⊢[PRAAx] completionInput a point N x :=
  .andI (Prf.andE₁ h) (.andI (Prf.andE₁ (Prf.andE₂ h)) (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))))

/-- Every clause of the original named source proposition, at the
original Z and its original sharp constants, for the fixed actual step. -/
theorem source_root_adequacy (a : PR 3) (point : PR 2) (N Z x : PTm n)
    (h : Γ ⊢[PRAAx] input a point N Z x) : Γ ⊢[PRAAx] sourceConclusion a point N Z x :=
  GaussianRootAdequacyTheorem.root_adequacy step a point N Z x (legacy_input a point N Z x h)

/-- The full source proposition and its completed-distance corollary,
without an incoming RD or step contract. -/
theorem root_adequacy (a : PR 3) (point : PR 2) (N Z x : PTm n)
    (h : Γ ⊢[PRAAx] input a point N Z x) : Γ ⊢[PRAAx] conclusion a point N Z x :=
  GaussianRootCompletedAdequacy.completed_root_adequacy step a point N Z x (legacy_input a point N Z x h)

theorem stage_estimates (a : PR 3) (point : PR 2) (N Z t x : PTm n)
    (h : Γ ⊢[PRAAx] input a point N Z x) : Γ ⊢[PRAAx]
    GaussianRootAdequacyTheorem.stageEstimates step a point N Z t x :=
  GaussianRootAdequacyTheorem.estimates_at_stage step a point N Z t x (legacy_input a point N Z x h)

theorem sharp_evaluation_error (a : PR 3) (point : PR 2) (N Z t x : PTm n)
    (h : Γ ⊢[PRAAx] input a point N Z x) : Γ ⊢[PRAAx]
    GaussianFastValueCut.radiusCut (GaussianRootSharpEvaluation.rawF step a point)
      (GaussianRootSharpEvaluation.modulus a N Z x) (GaussianRootSharpEvaluation.data N t x)
      (two*GaussianRootSchedule.coefficientConstant N Z) (GaussianRootFiniteEvaluation.denominator a N t x) :=
  GaussianRootSharpEvaluation.sharp_evaluation_error step a point N Z t x (legacy_input a point N Z x h)

theorem sharp_distance_residual (a : PR 3) (point : PR 2) (N Z t x : PTm n)
    (h : Γ ⊢[PRAAx] input a point N Z x) : Γ ⊢[PRAAx]
    GaussianScalarOrderCut.jointCut (polynomialNameF a point) (GaussianLinearDistanceName.nameF point)
      (polynomialData N Z x) (GaussianRootSharpDistance.rhsData step a N Z t x) :=
  GaussianRootSharpDistance.sharp_distance_residual step a point N Z t x (legacy_input a point N Z x h)

theorem member_iff_polynomial_zero (a : PR 3) (point : PR 2) (N Z x : PTm n)
    (h : Γ ⊢[PRAAx] input a point N Z x) : Γ ⊢[PRAAx] Fm.iff (member a point N x) (polynomialZero a point N Z x) :=
  GaussianRootAdequacy.member_iff_computed_polynomial_zero step a point N Z x (legacy_input a point N Z x h)

theorem member_iff_completed_zero (a : PR 3) (point : PR 2) (N x : PTm n)
    (h : Γ ⊢[PRAAx] completionInput a point N x) : Γ ⊢[PRAAx] Fm.iff (member a point N x) (completedZero a point N x) :=
  GaussianRootDistanceZero.member_iff_completed_zero step a point N x (completion_legacy_input a point N x h)

theorem completed_zero_iff_polynomial_zero (a : PR 3) (point : PR 2) (N Z x : PTm n)
    (h : Γ ⊢[PRAAx] input a point N Z x) : Γ ⊢[PRAAx]
    Fm.iff (completedZero a point N x) (polynomialZero a point N Z x) :=
  GaussianRootCompletedAdequacy.completed_zero_iff_polynomial_zero step a point N Z x (legacy_input a point N Z x h)

theorem primitive_root_stage (a : PR 3) (point : PR 2) (N Z x k : PTm n)
    (h : Γ ⊢[PRAAx] input a point N Z x) (hz : Γ ⊢[PRAAx] polynomialZero a point N Z x) : Γ ⊢[PRAAx]
    GaussianRootMembership.stageCondition step a point N x k (GaussianRootApproximationWitness.stageIndex N (Z+one) k) :=
  GaussianRootAdequacy.primitive_root_stage step a point N Z x k (legacy_input a point N Z x h)
    (GaussianPolynomialValueName.name_zero_to_value_zero a point N (Z+one) x hz)

theorem completed_distance_fast (a : PR 3) (point : PR 2) (N x : PTm n)
    (h : Γ ⊢[PRAAx] completionInput a point N x) : Γ ⊢[PRAAx]
    GaussianLinearDistanceName.scalarCN (distanceNameF a point) (distanceData N x) :=
  GaussianRootDistanceCompletion.name_fast step a point N x (completion_legacy_input a point N x h)
theorem completed_distance_nonnegative (a : PR 3) (point : PR 2) (N x k : PTm n) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (GaussianEuclideanDistanceName.fraction zero one)
      (ap2 (distanceNameF a point) k (distanceData N x)) :=
  GaussianRootDistanceCompletion.name_nonnegative step a point N x k
theorem completed_distance_canonical (a : PR 3) (point : PR 2) (N x k : PTm n) : Γ ⊢[PRAAx]
    RationalNormalForm.wellFormed (ap2 (distanceNameF a point) k (distanceData N x)) :=
  GaussianRootDistanceCompletion.name_canonical step a point N x k

theorem stage_distance_variation (a : PR 3) (point : PR 2) (N t u x m l : PTm n)
    (h : Γ ⊢[PRAAx] completionInput a point N x) (htu : Γ ⊢[PRAAx] le t u) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (GaussianEuclideanDistanceName.distanceSample point (roots a N t x) x m)
      (GaussianEuclideanDistanceName.distanceSample point (roots a N u x) x l)
      (unit m*unit l+coverDenominator t*(unit m+unit l)) (coverDenominator t*unit m*unit l) :=
  GaussianRootDistanceCompletion.stage_variation step a point N t u x m l GaussianMonicRD.monic_rd
    (Prf.andE₁ h) (Prf.andE₁ (Prf.andE₂ h)) (Prf.andE₂ (Prf.andE₂ h)) htu

theorem root_name_at (a : PR 3) (N t x : PTm n) : Γ ⊢[PRAAx]
    ap3 (rootNameF a) N t x ≐ roots a N t x := GaussianRootSupport.root_name_program step a N t x
theorem distance_name_at (a : PR 3) (point : PR 2) (N x k : PTm n) : Γ ⊢[PRAAx]
    ap2 (distanceNameF a point) k (distanceData N x) ≐ distanceSample a point N x k :=
  GaussianRootDistanceCompletion.name_at step a point N x k
theorem polynomial_name_at (a : PR 3) (point : PR 2) (N Z x k : PTm n) : Γ ⊢[PRAAx]
    ap2 (polynomialNameF a point) k (polynomialData N Z x) ≐ GaussianPolynomialValueName.value a point N (Z+one) x k :=
  GaussianPolynomialValueName.name_at a point N (Z+one) x k

def distanceConclusion (a : PR 3) (point : PR 2) (N x : PTm n) : Fm PTm n :=
  GaussianLinearDistanceName.scalarCN (distanceNameF a point) (distanceData N x) ⋏
    (.all (RationalArgmin.rationalLE (GaussianEuclideanDistanceName.fraction zero one)
      (ap2 (distanceNameF a point) (var 0) (distanceData (Syn.shift N) (Syn.shift x))) ⋏
      RationalNormalForm.wellFormed (ap2 (distanceNameF a point) (var 0) (distanceData (Syn.shift N) (Syn.shift x)))) ⋏
      Fm.iff (member a point N x) (completedZero a point N x))
ipra_subst distanceConclusion [Fm.iff, Syn.subst_shift, Syn.shift_subst]

/-- Completion and its zero-membership interpretation require no disk
or polynomial-value bound beyond the genuine coefficient/point names. -/
theorem completed_distance (a : PR 3) (point : PR 2) (N x : PTm n)
    (h : Γ ⊢[PRAAx] completionInput a point N x) : Γ ⊢[PRAAx] distanceConclusion a point N x :=
  .andI (completed_distance_fast a point N x h)
    (.andI (.allI (.andI (completed_distance_nonnegative a point (Syn.shift N) (Syn.shift x) (var 0))
      (completed_distance_canonical a point (Syn.shift N) (Syn.shift x) (var 0))))
      (member_iff_completed_zero a point N x h))

theorem concrete_monic_source_root_adequacy_closed (a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (input a point (var 0) (var 1) (var 2) ⟶ sourceConclusion a point (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (source_root_adequacy _ _ _ _ _ Prf.hyp0))
theorem concrete_monic_completed_root_adequacy_closed (a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (input a point (var 0) (var 1) (var 2) ⟶ conclusion a point (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (root_adequacy _ _ _ _ _ Prf.hyp0))
theorem concrete_monic_sharp_stage_estimates_closed (a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input a point (var 0) (var 1) (var 3) ⟶
      GaussianRootAdequacyTheorem.stageEstimates step a point (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (stage_estimates _ _ _ _ _ _ Prf.hyp0))
theorem concrete_member_polynomial_zero_closed (a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (input a point (var 0) (var 1) (var 2) ⟶
      Fm.iff (member a point (var 0) (var 2)) (polynomialZero a point (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (member_iff_polynomial_zero _ _ _ _ _ Prf.hyp0))
theorem concrete_distance_polynomial_zero_closed (a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (input a point (var 0) (var 1) (var 2) ⟶
      Fm.iff (completedZero a point (var 0) (var 2)) (polynomialZero a point (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (completed_zero_iff_polynomial_zero _ _ _ _ _ Prf.hyp0))
theorem concrete_completed_distance_closed (a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (completionInput a point (var 0) (var 1) ⟶ distanceConclusion a point (var 0) (var 1)) :=
  closeUniv 2 (.impI (completed_distance _ _ _ _ Prf.hyp0))
theorem concrete_member_completed_zero_closed (a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (completionInput a point (var 0) (var 1) ⟶
      Fm.iff (member a point (var 0) (var 1)) (completedZero a point (var 0) (var 1))) :=
  closeUniv 2 (.impI (member_iff_completed_zero _ _ _ _ Prf.hyp0))
theorem concrete_forward_root_stage_closed (a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input a point (var 0) (var 1) (var 2) ⟶ polynomialZero a point (var 0) (var 1) (var 2) ⟶
      GaussianRootMembership.stageCondition step a point (var 0) (var 2) (var 3)
        (GaussianRootApproximationWitness.stageIndex (var 0) (var 1+one) (var 3))) :=
  closeUniv 4 (.impI (.impI (primitive_root_stage _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem concrete_stage_distance_variation_closed (a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (completionInput a point (var 0) (var 3) ⟶ le (var 1) (var 2) ⟶
      RationalValueBounds.radius
        (GaussianEuclideanDistanceName.distanceSample point (roots a (var 0) (var 1) (var 3)) (var 3) (var 4))
        (GaussianEuclideanDistanceName.distanceSample point (roots a (var 0) (var 2) (var 3)) (var 3) (var 5))
        (unit (var 4)*unit (var 5)+coverDenominator (var 1)*(unit (var 4)+unit (var 5)))
        (coverDenominator (var 1)*unit (var 4)*unit (var 5))) :=
  closeUniv 6 (.impI (.impI (stage_distance_variation _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem concrete_names_program_closed (a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (ap3 (rootNameF a) (var 0) (var 2) (var 3) ≐ roots a (var 0) (var 2) (var 3) ⋏
      (ap2 (distanceNameF a point) (var 4) (distanceData (var 0) (var 3)) ≐ distanceSample a point (var 0) (var 3) (var 4) ⋏
        ap2 (polynomialNameF a point) (var 4) (polynomialData (var 0) (var 1) (var 3)) ≐
          GaussianPolynomialValueName.value a point (var 0) (var 1+one) (var 3) (var 4))) :=
  closeUniv 5 (.andI (root_name_at _ _ _ _) (.andI (distance_name_at _ _ _ _ _) (polynomial_name_at _ _ _ _ _ _)))

end LeanProofs.IPRA.Analysis.GaussianMonicRootAdequacy
