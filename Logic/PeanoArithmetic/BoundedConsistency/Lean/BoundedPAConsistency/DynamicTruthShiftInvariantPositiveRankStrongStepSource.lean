import BoundedPAConsistency.DynamicTruthCrossLevelDerivedStrongStep
import BoundedPAConsistency.DynamicTruthShiftInvariantPositiveRankStrongStep
import BoundedPAConsistency.DynamicTruthShiftInvariantStrongStepSource
import BoundedPAConsistency.FinFunext

/-!
# Congruence-safe fixed-source wrapper for the positive-rank shift step

The generic constructor theorem works with the canonical meta-level function
`shift`, while the fixed source sentence exposes a relational `shiftGraph`
witness.  Functionality of the represented graph bridges those two
presentations.

The two truth predicates remain opaque source relations.  Their
coordinatewise equality congruence is therefore an explicit antecedent.
Completeness first quotients interpreted equality and invokes the semantic
constructor only in the resulting canonical expanded model.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantPositiveRankStrongStepSource

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.OrientedHierarchy
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.TermEvaluationTransport
open LeanProofs.BoundedPAConsistency.FixedLevelTruth
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelStrongStepSource
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceTemplate
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantStrongStepSource
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantPositiveRankStrongStep
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters
open LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateParameters
open LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateEqualityQuotient
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelDerivedStrongStep
open LeanProofs.BoundedPAConsistency.TwoPredicateSourceContextInductionKernel

/-- Unambiguous name for the shared two-predicate, three-parameter source
language. -/
abbrev ShiftSourceLanguage :=
  DynamicTruthCrossLevelSourceTemplate.SourceLanguage

/-! ## Focused semantics of the named-level cross field -/

section SourceSemantics

variable {X : Type*}
variable [sourceStructure : Structure ShiftSourceLanguage X]
variable [Nonempty X] [ORingStructure X]
variable [Structure.ORing ShiftSourceLanguage X]
variable [hPA : X↓[ℒₒᵣ] ⊧* Peano]

local instance : X↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-- Interpretation of one of the three named hierarchy levels. -/
private noncomputable def sourceNamedLevel (i : Fin 3) : X :=
  Structure.func (L := ShiftSourceLanguage)
    (Sum.inr (Sum.inr (Sum.inr (ParameterFunc.parameter i)))) ![]

@[simp] private theorem eval_levelTerm (i : Fin 3) (v : Fin n → X) :
    (levelTerm (n := n) i).valb (M := X) v = sourceNamedLevel i := by
  simp [levelTerm, namedParameterTerm, sourceNamedLevel, Matrix.empty_eq]

variable (hArithmeticReduct :
  sourceStructure.lMap (arithmeticHom 3 3 3) =
    LO.FirstOrder.Arithmetic.standardModel X)

/- The generic named-level record formula differs from the derived source
only in its two level terms.  Its recursive universal leaf is shared. -/
include hArithmeticReduct in
@[simp] private theorem eval_sourceCurrentSuccessorRecordValid
    (v : Fin 2 → X) :
    sourceCurrentSuccessorRecordValid.Evalb (M := X) v ↔
      SigmaRecordValid sourceCurrentRelation
        (sourceNamedLevel 1) (sourceNamedLevel 2) (v 0) (v 1) := by
  simp [sourceCurrentSuccessorRecordValid, sourceNamedLevel,
    SigmaRecordValid, RecordDomain, PositiveRecordBranches,
    eval_liftArithmeticFormula hArithmeticReduct,
    eval_apply₃,
    eval_currentUniversalRecordBranch hArithmeticReduct]
  aesop

include hArithmeticReduct in
@[simp] private theorem eval_sourceCurrentSuccessorTruth
    (v : Fin 3 → X) :
    sourceCurrentSuccessorTruth.Evalb (M := X) v ↔
      SuccessorTruth sourceCurrentRelation
        (sourceNamedLevel 1) (sourceNamedLevel 2)
        (v 0) (v 1) (v 2) := by
  simp [sourceCurrentSuccessorTruth, SuccessorTruth,
    eval_liftArithmeticFormula hArithmeticReduct,
    eval_apply₂,
    eval_sourceCurrentSuccessorRecordValid hArithmeticReduct]

include hArithmeticReduct in
@[simp] private theorem eval_sourceNextCrossLevelInvariant (p : X) :
    sourceNextCrossLevelInvariant.Evalb (M := X) ![p] ↔
      SuccessorCrossLaws sourceCurrentRelation
        (sourceNamedLevel 1) (sourceNamedLevel 2) p := by
  simp [sourceNextCrossLevelInvariant, sourceNextCrossLevelBody,
    sourceCurrentSigmaDomain, sourceCurrentPiDomain,
    sourceCurrentPiTruth, sourceNamedLevel,
    SuccessorCrossLaws, LowerPiTrue,
    eval_liftArithmeticFormula hArithmeticReduct,
    eval_apply₂, eval_currentAtom,
    eval_sourceCurrentSuccessorTruth hArithmeticReduct,
    DynamicTruthFormula.isSigmaCode_defined.iff,
    DynamicTruthFormula.isPiCode_defined.iff,
    neg.defined.iff, Semiformula.eval_rew, Function.comp_def]
  constructor
  · intro h bound free
    simpa only [] using h free bound
  · intro h free bound
    simpa only [] using h bound free

include hArithmeticReduct in
@[simp] private theorem eval_sourceNextCrossLevelInvariant'
    (v : Fin 1 → X) :
    sourceNextCrossLevelInvariant.Evalb (M := X) v ↔
      SuccessorCrossLaws sourceCurrentRelation
        (sourceNamedLevel 1) (sourceNamedLevel 2) (v 0) := by
  rw [Matrix.fun_eq_vec_one v]
  exact eval_sourceNextCrossLevelInvariant hArithmeticReduct (v 0)

include hArithmeticReduct in
@[simp] private theorem eval_sourceCurrentCrossLevelSentence :
    sourceCurrentCrossLevelSentence.Evalb (M := X) ![] ↔
      ∀ q : X, SuccessorCrossLaws sourceCurrentRelation
        (sourceNamedLevel 1) (sourceNamedLevel 2) q := by
  simp [sourceCurrentCrossLevelSentence,
    eval_sourceNextCrossLevelInvariant' hArithmeticReduct]

/- The unary shift target is exactly the semantic invariant consumed by the
constructor theorem.  Isolating this evaluation also fixes all five nested
valuation coordinates before the main completeness callback. -/
include hArithmeticReduct in
@[simp] private theorem eval_sourceNextShiftInvariantPredicate (p : X) :
    sourceNextShiftInvariantPredicate.Evalb (M := X) ![p] ↔
      ShiftInvariantAt
        (SuccessorTruth sourceCurrentRelation
          (sourceNamedLevel 1) (sourceNamedLevel 2))
        (sourceNamedLevel 1) p := by
  simp [sourceNextShiftInvariantPredicate,
    sourceNextShiftInvariantBody, sourceNextShiftedTruthWitness,
    sourceFreeTail, sourceBoundedDomainAt,
    ShiftInvariantAt, sourceNamedLevel,
    eval_liftArithmeticFormula hArithmeticReduct,
    eval_apply₂, eval_apply₃,
    eval_sourceCurrentSuccessorTruth hArithmeticReduct]
  constructor
  · intro h bound shifted free hfree hbounded
    exact h free shifted bound hfree hbounded
  · intro h free shifted bound hfree hbounded
    exact h bound shifted free hfree hbounded

include hArithmeticReduct in
@[simp] private theorem eval_sourceNextShiftInvariantPredicate'
    (v : Fin 1 → X) :
    sourceNextShiftInvariantPredicate.Evalb (M := X) v ↔
      ShiftInvariantAt
        (SuccessorTruth sourceCurrentRelation
          (sourceNamedLevel 1) (sourceNamedLevel 2))
        (sourceNamedLevel 1) (v 0) := by
  rw [Matrix.fun_eq_vec_one v]
  exact eval_sourceNextShiftInvariantPredicate hArithmeticReduct (v 0)

include hArithmeticReduct in
@[simp] private theorem eval_sourcePrefixGuard (v : Fin 2 → X) :
    DynamicTruthShiftInvariantStrongStepSource.sourcePrefixGuard.Evalb
        (M := X) v ↔ v 0 < v 1 := by
  have hguard :
      DynamicTruthShiftInvariantStrongStepSource.sourcePrefixGuard =
        liftArithmeticFormula
          (.rel Language.LT.lt
            ![(#0 : ClosedSemiterm ℒₒᵣ 2),
              (#1 : ClosedSemiterm ℒₒᵣ 2)]) := by
    simp [DynamicTruthShiftInvariantStrongStepSource.sourcePrefixGuard,
      liftArithmeticFormula, Function.comp_def]
    exact funext_fin2 rfl rfl
  rw [hguard]
  rw [eval_liftArithmeticFormula hArithmeticReduct]
  simp

include hArithmeticReduct in
@[simp] private theorem eval_sourceStrongPrefix (p : X) :
    DynamicTruthShiftInvariantStrongStepSource.sourceStrongPrefix.Evalb
        (M := X) ![p] ↔
      ∀ q : X, q < p →
        ShiftInvariantAt
          (SuccessorTruth sourceCurrentRelation
            (sourceNamedLevel 1) (sourceNamedLevel 2))
          (sourceNamedLevel 1) q := by
  simp [DynamicTruthShiftInvariantStrongStepSource.sourceStrongPrefix,
    Semiformula.eval_substs, Function.comp_def,
    eval_sourcePrefixGuard hArithmeticReduct,
    eval_sourceNextShiftInvariantPredicate' hArithmeticReduct]

end SourceSemantics

/-- Both coordinatewise congruence laws omitted by lifted PA. -/
noncomputable def sourcePlaceholderCongruenceContext :
    Sentence ShiftSourceLanguage :=
  placeholderCongruenceContext 3 3 3

/-- Sound source obligation for the shift constructor step. -/
noncomputable def sourceCongruentStrongStepSentence :
    Sentence ShiftSourceLanguage :=
  Arrow.arrow sourcePlaceholderCongruenceContext
    DynamicTruthShiftInvariantStrongStepSource.sourceStrongStepSentence

set_option maxHeartbeats 2000000 in
/-- The complete constructor-wise shift step after equality quotienting.

The sole adapter replaces each relational shift witness by the unique
canonical value of `shift`; the remaining constructor calculation is the
audited generic `SuccessorTruth.shift_strongStep`. -/
noncomputable def sourceCongruentStrongStepProof :
    twoPredicateParameterPeano 3 3 3 ⊢!
      sourceCongruentStrongStepSentence := by
  simpa [sourceCongruentStrongStepSentence,
    sourcePlaceholderCongruenceContext] using
    (complete_underPlaceholderCongruence
      DynamicTruthShiftInvariantStrongStepSource.sourceStrongStepSentence
      (fun X ↦ by
        intro _ _ _ _
        have hArithmeticReduct :=
          DynamicTruthCrossLevelDerivedStrongStep.sourceArithmeticReduct_eq_standardModel
            (X := X)
        have hArithmeticPA : X↓[ℒₒᵣ] ⊧* Peano := by
          constructor
          intro sigma hsigma
          rw [← hArithmeticReduct]
          exact Semiformula.models_lMap.mp <|
            (inferInstance : X↓[ShiftSourceLanguage] ⊧*
              twoPredicateParameterPeano 3 3 3).models _
                ⟨sigma, hsigma, rfl⟩
        letI : X↓[ℒₒᵣ] ⊧* Peano := hArithmeticPA
        letI : X↓[ℒₒᵣ] ⊧* ISigma 1 :=
          models_of_subtheory hArithmeticPA
        simp [models_iff,
          DynamicTruthShiftInvariantStrongStepSource.sourceStrongStepSentence]
        intro hcontext p hprefix
        have hcontext' := hcontext
        simp [sourceAvailableContext] at hcontext'
        have hcross :=
          (eval_sourceCurrentCrossLevelSentence
            hArithmeticReduct).mp hcontext'.2
        exact
          (eval_sourceNextShiftInvariantPredicate
            hArithmeticReduct p).mpr <|
            SuccessorTruth.shift_strongStep hcross <|
              (eval_sourceStrongPrefix hArithmeticReduct p).mp hprefix))

end LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantPositiveRankStrongStepSource
