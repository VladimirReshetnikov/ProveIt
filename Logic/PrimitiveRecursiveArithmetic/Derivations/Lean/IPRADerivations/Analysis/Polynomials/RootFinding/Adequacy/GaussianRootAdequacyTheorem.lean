import IPRADerivations.Analysis.Polynomials.RootFinding.Adequacy.GaussianRootSharpEvaluation
import IPRADerivations.Analysis.Polynomials.RootFinding.Adequacy.GaussianRootSharpDistance

/-!
# The source root-adequacy proposition with both sharp estimates

All clauses of source04 prop:root-adequacy are collected in one ordinary
iPRA sentence: the actual polynomial-value name, exact represented Member
equivalence, the primitive-recursive forward stage, and both sharp error
cuts at every root stage. The original supplied Z is retained. The
construction remains conditional on the explicit local monic RD contract.
The source's later stage-distance completion corollary is separate.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRootAdequacyTheorem

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRootAdequacy (inputContract)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def distanceValid (point : PR 2) (T x : PTm n) : Fm PTm n :=
  GaussianEuclideanDistanceName.fastScalar point T x ⋏
    .all (RationalArgmin.rationalLE (GaussianEuclideanDistanceName.fraction zero one)
      (GaussianEuclideanDistanceName.distanceSample point (Syn.shift T) (Syn.shift x) (var 0)))

ipra_subst distanceValid [Syn.subst_shift, Syn.shift_subst]

theorem distance_valid (point : PR 2) (T x : PTm n)
    (hCN : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN point x)
    (hT : Γ ⊢[PRAAx] le one (Foundations.SequenceComposition.length T)) : Γ ⊢[PRAAx] distanceValid point T x := by
  refine .andI (GaussianEuclideanDistanceName.fast_scalar point T x hCN hT) (.allI ?_)
  exact GaussianCoefficientNormOrder.zero_lower_of_nonnegative _
    (GaussianEuclideanDistanceName.sample_nonnegative point (Syn.shift T) (Syn.shift x) (var 0))

def stageEstimates (step a : PR 3) (point : PR 2) (N Z t x : PTm n) : Fm PTm n :=
  distanceValid point (GaussianRootRadius.roots step a N t x) x ⋏
  (GaussianEuclideanDistanceName.pointCN (GaussianRootSharpEvaluation.errorNameF step a point)
    (GaussianRootSharpEvaluation.errorNameData a N Z t x) ⋏
  (GaussianLinearDistanceName.scalarCN (GaussianLinearDistanceName.nameF point)
    (GaussianRootSharpDistance.rhsData step a N Z t x) ⋏
  (GaussianFastValueCut.radiusCut (GaussianRootSharpEvaluation.rawF step a point)
    (GaussianRootSharpEvaluation.modulus a N Z x) (GaussianRootSharpEvaluation.data N t x)
    (two*GaussianRootSchedule.coefficientConstant N Z) (GaussianRootFiniteEvaluation.denominator a N t x) ⋏
  GaussianScalarOrderCut.jointCut (GaussianPolynomialValueName.nameF a point) (GaussianLinearDistanceName.nameF point)
    (GaussianPolynomialValueName.nameData N (Z+one) x) (GaussianRootSharpDistance.rhsData step a N Z t x))))

ipra_subst stageEstimates [GaussianRootSharpEvaluation.errorNameData]

def conclusion (step a : PR 3) (point : PR 2) (N Z x : PTm n) : Fm PTm n :=
  GaussianEuclideanDistanceName.pointCN (GaussianPolynomialValueName.nameF a point)
    (GaussianPolynomialValueName.nameData N (Z+one) x) ⋏
  (Fm.iff (GaussianRootMembership.member step a point N x) (GaussianPolynomialValueName.nameZero a point N (Z+one) x) ⋏
  (.all (stageEstimates step a point (Syn.shift N) (Syn.shift Z) (var 0) (Syn.shift x)) ⋏
   .all (GaussianPolynomialValueName.nameZero a point (Syn.shift N) (Syn.shift Z+one) (Syn.shift x) ⟶
     GaussianRootMembership.stageCondition step a point (Syn.shift N) (Syn.shift x) (var 0)
       (GaussianRootApproximationWitness.stageIndex (Syn.shift N) (Syn.shift Z+one) (var 0)))))

ipra_subst conclusion [Fm.iff, Syn.subst_shift, Syn.shift_subst]

theorem estimates_at_stage (step a : PR 3) (point : PR 2) (N Z t x : PTm n)
    (h : Γ ⊢[PRAAx] inputContract step a point N Z x) : Γ ⊢[PRAAx] stageEstimates step a point N Z t x := by
  have hn := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))
  have pointData := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))
  refine .andI (distance_valid point _ _ (Prf.andE₁ pointData)
    (le_congr (.eqRefl _) (GaussianRootRadius.roots_length step a N t x).eqSymm hn)) ?_
  exact .andI (GaussianRootSharpEvaluation.error_name_fast _ _ _ _ _ _ _ h)
    (.andI (GaussianRootSharpDistance.rhs_name_fast _ _ _ _ _ _ _ h)
      (.andI (GaussianRootSharpEvaluation.sharp_evaluation_error _ _ _ _ _ _ _ h)
        (GaussianRootSharpDistance.sharp_distance_residual _ _ _ _ _ _ _ h)))

theorem all_stage_estimates (step a : PR 3) (point : PR 2) (N Z x : PTm n)
    (h : Γ ⊢[PRAAx] inputContract step a point N Z x) : Γ ⊢[PRAAx]
    .all (stageEstimates step a point (Syn.shift N) (Syn.shift Z) (var 0) (Syn.shift x)) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] inputContract step a point (Syn.shift N) (Syn.shift Z) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianRootAdequacy.subst_inputContract,Syn.shift] using h.shift
  exact estimates_at_stage step a point (Syn.shift N) (Syn.shift Z) (var 0) (Syn.shift x) hs

theorem all_forward_stages (step a : PR 3) (point : PR 2) (N Z x : PTm n)
    (h : Γ ⊢[PRAAx] inputContract step a point N Z x) : Γ ⊢[PRAAx]
    .all (GaussianPolynomialValueName.nameZero a point (Syn.shift N) (Syn.shift Z+one) (Syn.shift x) ⟶
      GaussianRootMembership.stageCondition step a point (Syn.shift N) (Syn.shift x) (var 0)
        (GaussianRootApproximationWitness.stageIndex (Syn.shift N) (Syn.shift Z+one) (var 0))) := by
  refine .allI (.impI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] inputContract step a point (Syn.shift N) (Syn.shift Z) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianRootAdequacy.subst_inputContract,Syn.shift] using h.shift
  exact GaussianRootAdequacy.primitive_root_stage step a point (Syn.shift N) (Syn.shift Z) (Syn.shift x) (var 0) hs.wk
    (GaussianPolynomialValueName.name_zero_to_value_zero _ _ _ _ _ Prf.hyp0)

theorem root_adequacy (step a : PR 3) (point : PR 2) (N Z x : PTm n)
    (h : Γ ⊢[PRAAx] inputContract step a point N Z x) : Γ ⊢[PRAAx] conclusion step a point N Z x :=
  .andI (GaussianRootAdequacy.polynomial_value_name _ _ _ _ _ _ h)
    (.andI (GaussianRootAdequacy.member_iff_computed_polynomial_zero _ _ _ _ _ _ h)
      (.andI (all_stage_estimates _ _ _ _ _ _ h) (all_forward_stages _ _ _ _ _ _ h)))

theorem root_adequacy_closed (step a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (inputContract step a point (var 0) (var 1) (var 2) ⟶ conclusion step a point (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (root_adequacy _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRootAdequacyTheorem
