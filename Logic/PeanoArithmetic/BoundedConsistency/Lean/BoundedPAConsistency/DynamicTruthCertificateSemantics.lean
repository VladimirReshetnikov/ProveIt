import BoundedPAConsistency.DynamicTruthCrossLevelFormula
import BoundedPAConsistency.DynamicTruthShiftInvariantFormula
import BoundedPAConsistency.DynamicTruthSubstitutionInvariantFormula
import BoundedPAConsistency.DynamicTruthAxiomSoundnessFormula
import BoundedPAConsistency.DynamicTruthTemplateSemantics
import BoundedPAConsistency.DynamicTruthShiftInvariantPositiveRankStrongStep
import BoundedPAConsistency.DynamicTruthSubstitutionInvariantPositiveRankStrongStep
import BoundedPAConsistency.FinFunext

/-!
# Semantics of the dynamic truth-certificate source fields

The certificate compiler stores fixed source sentences for cross-level
coherence, free-variable shift, simultaneous substitution, and PA-axiom
soundness.  This module records their interpretations in one canonical
expanded source model.  Keeping these reductions public avoids duplicating
large binder calculations in the final restricted-soundness source proof.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthCertificateSemantics

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.FixedLevelTruth
open LeanProofs.BoundedPAConsistency.OrientedHierarchy
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelStrongStepSource
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantPositiveRankStrongStep
open LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantPositiveRankStrongStep
open LeanProofs.BoundedPAConsistency.DynamicTruthTemplateFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthTemplateSemantics

private abbrev L := DynamicTruthTemplateFormula.SourceLanguage

variable {M : Type*}
variable [sourceStructure : Structure L M]
variable [Nonempty M] [ORingStructure M]
variable [hPA : M↓[ℒₒᵣ] ⊧* Peano]

local instance : M↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

variable (hArithmeticReduct :
  sourceStructure.lMap (ModelCodedPredicateParameters.arithmeticHom 3 2) =
    LO.FirstOrder.Arithmetic.standardModel M)

@[simp] theorem eval_parameterTerm
    (i : Fin 2) (v : Fin n → M) :
    (parameterTerm (n := n) i).valb (M := M) v = level i := by
  simp [parameterTerm, level, Matrix.empty_eq]

/-! ## Cross-level coherence -/

include hArithmeticReduct in
@[simp] theorem eval_sourceSigmaDomain (v : Fin 3 → M) :
    DynamicTruthCrossLevelFormula.sourceSigmaDomain.Evalb (M := M) v ↔
      IsSigmaCode ℒₒᵣ (level 0) (v 2) := by
  simp [DynamicTruthCrossLevelFormula.sourceSigmaDomain,
    eval_apply₂, eval_liftArithmeticFormula hArithmeticReduct,
    eval_parameterTerm]

include hArithmeticReduct in
@[simp] theorem eval_sourcePiDomain (v : Fin 3 → M) :
    DynamicTruthCrossLevelFormula.sourcePiDomain.Evalb (M := M) v ↔
      IsPiCode ℒₒᵣ (level 0) (v 2) := by
  simp [DynamicTruthCrossLevelFormula.sourcePiDomain,
    eval_apply₂, eval_liftArithmeticFormula hArithmeticReduct,
    eval_parameterTerm]

include hArithmeticReduct in
@[simp] theorem eval_sourceLowerPiTruth (v : Fin 3 → M) :
    DynamicTruthCrossLevelFormula.sourceLowerPiTruth.Evalb (M := M) v ↔
      LowerPiTrue lowerRelation (level 0) (v 0) (v 1) (v 2) := by
  simp [DynamicTruthCrossLevelFormula.sourceLowerPiTruth,
    LowerPiTrue, eval_sourcePiDomain hArithmeticReduct,
    eval_liftArithmeticFormula hArithmeticReduct, eval_lowerAtom]

include hArithmeticReduct in
@[simp] theorem eval_sourceCrossLevelBody (v : Fin 3 → M) :
    DynamicTruthCrossLevelFormula.sourceCrossLevelBody.Evalb (M := M) v ↔
      ((IsSigmaCode ℒₒᵣ (level 0) (v 2) →
          (SuccessorTruth lowerRelation (level 0) (level 1)
              (v 0) (v 1) (v 2) ↔
            lowerRelation (v 0) (v 1) (v 2))) ∧
        (IsPiCode ℒₒᵣ (level 0) (v 2) →
          (SuccessorTruth lowerRelation (level 0) (level 1)
              (v 0) (v 1) (v 2) ↔
            LowerPiTrue lowerRelation (level 0)
              (v 0) (v 1) (v 2)))) := by
  simp [DynamicTruthCrossLevelFormula.sourceCrossLevelBody,
    eval_sourceSigmaDomain hArithmeticReduct,
    eval_sourcePiDomain hArithmeticReduct,
    eval_successorTruthFormula hArithmeticReduct,
    eval_lowerAtom,
    eval_sourceLowerPiTruth hArithmeticReduct]

include hArithmeticReduct in
@[simp] theorem eval_sourceCrossLevelSentence :
    DynamicTruthCrossLevelFormula.sourceCrossLevelSentence.Evalb
        (M := M) ![] ↔
      ∀ p : M, SuccessorCrossLaws
        lowerRelation (level 0) (level 1) p := by
  simp [DynamicTruthCrossLevelFormula.sourceCrossLevelSentence,
    DynamicTruthCrossLevelFormula.sourceCrossLevelPredicate,
    SuccessorCrossLaws,
    eval_sourceCrossLevelBody hArithmeticReduct]
  constructor
  · intro h p bound free
    exact h p free bound
  · intro h p free bound
    exact h p bound free

/-! ## Free-variable shift invariance -/

include hArithmeticReduct in
@[simp] theorem eval_sourceFreeTail (v : Fin 4 → M) :
    DynamicTruthShiftInvariantFormula.sourceFreeTail.Evalb (M := M) v ↔
      TermEvaluationTransport.IsFreeTail (v 1) (v 2) := by
  simp [DynamicTruthShiftInvariantFormula.sourceFreeTail,
    eval_apply₂, eval_liftArithmeticFormula hArithmeticReduct,
    DynamicTruthShiftInvariantFormula.eval_isFreeTailDef]

include hArithmeticReduct in
@[simp] theorem eval_sourceShiftBoundedDomain (v : Fin 4 → M) :
    DynamicTruthShiftInvariantFormula.sourceBoundedDomain.Evalb
        (M := M) v ↔
      QuantifierBoundedCode ℒₒᵣ (level 0) (v 3) := by
  simp [DynamicTruthShiftInvariantFormula.sourceBoundedDomain,
    eval_apply₂, eval_liftArithmeticFormula hArithmeticReduct,
    eval_parameterTerm]

include hArithmeticReduct in
@[simp] theorem eval_sourceShiftedTruthWitness (v : Fin 4 → M) :
    DynamicTruthShiftInvariantFormula.sourceShiftedTruthWitness.Evalb
        (M := M) v ↔
      (SuccessorTruth lowerRelation (level 0) (level 1)
          (v 0) (v 1) (shift ℒₒᵣ (v 3)) ↔
        SuccessorTruth lowerRelation (level 0) (level 1)
          (v 0) (v 2) (v 3)) := by
  simp [DynamicTruthShiftInvariantFormula.sourceShiftedTruthWitness,
    eval_apply₂, eval_apply₃,
    eval_liftArithmeticFormula hArithmeticReduct,
    eval_successorTruthFormula hArithmeticReduct]

include hArithmeticReduct in
@[simp] theorem eval_sourceShiftInvariantBody (v : Fin 4 → M) :
    DynamicTruthShiftInvariantFormula.sourceShiftInvariantBody.Evalb
        (M := M) v ↔
      (TermEvaluationTransport.IsFreeTail (v 1) (v 2) →
        QuantifierBoundedCode ℒₒᵣ (level 0) (v 3) →
        (SuccessorTruth lowerRelation (level 0) (level 1)
            (v 0) (v 1) (shift ℒₒᵣ (v 3)) ↔
          SuccessorTruth lowerRelation (level 0) (level 1)
            (v 0) (v 2) (v 3))) := by
  simp [DynamicTruthShiftInvariantFormula.sourceShiftInvariantBody,
    eval_sourceFreeTail hArithmeticReduct,
    eval_sourceShiftBoundedDomain hArithmeticReduct,
    eval_sourceShiftedTruthWitness hArithmeticReduct]

include hArithmeticReduct in
@[simp] theorem eval_sourceShiftInvariantSentence :
    DynamicTruthShiftInvariantFormula.sourceShiftInvariantSentence.Evalb
        (M := M) ![] ↔
      ∀ p : M, ShiftInvariantAt
        (SuccessorTruth lowerRelation (level 0) (level 1))
        (level 0) p := by
  simp [DynamicTruthShiftInvariantFormula.sourceShiftInvariantSentence,
    DynamicTruthShiftInvariantFormula.sourceShiftInvariantPredicate,
    ShiftInvariantAt,
    eval_sourceShiftInvariantBody hArithmeticReduct]
  constructor
  · intro h p bound shifted free
    exact h p free shifted bound
  · intro h p free shifted bound
    exact h p bound shifted free

/-! ## Simultaneous-substitution invariance -/

@[simp] theorem eval_apply₅
    (p : Semisentence L 5)
    (t₀ t₁ t₂ t₃ t₄ : ClosedSemiterm L n)
    (v : Fin n → M) :
    (DynamicTruthSubstitutionInvariantFormula.apply₅
        p t₀ t₁ t₂ t₃ t₄).Evalb (M := M) v ↔
      p.Evalb (M := M)
        ![t₀.valb (M := M) v, t₁.valb (M := M) v,
          t₂.valb (M := M) v, t₃.valb (M := M) v,
          t₄.valb (M := M) v] := by
  simp [DynamicTruthSubstitutionInvariantFormula.apply₅,
    Semiformula.eval_substs, Function.comp_def]
  apply iff_of_eq
  congr 2
  exact funext_fin5 rfl rfl rfl rfl rfl

include hArithmeticReduct in
@[simp] theorem eval_sourceSubstitutionInvariantPredicate (p : M) :
    DynamicTruthSubstitutionInvariantFormula.sourceSubstitutionInvariantPredicate.Evalb
        (M := M) ![p] ↔
      SubstitutionInvariantAt
        (SuccessorTruth lowerRelation (level 0) (level 1))
        (level 0) p := by
  simp [
    DynamicTruthSubstitutionInvariantFormula.sourceSubstitutionInvariantPredicate,
    DynamicTruthSubstitutionInvariantFormula.sourceSubstitutionInvariantBody,
    DynamicTruthSubstitutionInvariantFormula.sourceSemitermVector,
    DynamicTruthSubstitutionInvariantFormula.sourceBoundLength,
    DynamicTruthSubstitutionInvariantFormula.sourceSubstitutionEnvironment,
    DynamicTruthSubstitutionInvariantFormula.sourceSemiformula,
    DynamicTruthSubstitutionInvariantFormula.sourceBoundedDomain,
    DynamicTruthSubstitutionInvariantFormula.sourceSubstitutedTruthWitness,
    DynamicTruthTemplateFormula.parameterTerm,
    SubstitutionInvariantAt, lowerRelation, level,
    eval_liftArithmeticFormula hArithmeticReduct,
    eval_apply₂, eval_apply₃, eval_apply₅,
    eval_successorTruthFormula hArithmeticReduct,
    DynamicTruthSubstitutionInvariantFormula.isSubstitutionEnvironment_defined.iff,
    lh_defined.iff, IsSemitermVec.defined.iff,
    IsSemiformula.defined.iff, subst.defined.iff,
    (QuantifierBoundedCode.defined ℒₒᵣ (V := M)).iff]

include hArithmeticReduct in
@[simp] theorem eval_sourceSubstitutionInvariantPredicate'
    (v : Fin 1 → M) :
    DynamicTruthSubstitutionInvariantFormula.sourceSubstitutionInvariantPredicate.Evalb
        (M := M) v ↔
      SubstitutionInvariantAt
        (SuccessorTruth lowerRelation (level 0) (level 1))
        (level 0) (v 0) := by
  rw [Matrix.fun_eq_vec_one v]
  exact eval_sourceSubstitutionInvariantPredicate hArithmeticReduct (v 0)

include hArithmeticReduct in
@[simp] theorem eval_sourceSubstitutionInvariantSentence :
    DynamicTruthSubstitutionInvariantFormula.sourceSubstitutionInvariantSentence.Evalb
        (M := M) ![] ↔
      ∀ p : M, SubstitutionInvariantAt
        (SuccessorTruth lowerRelation (level 0) (level 1))
        (level 0) p := by
  simp [DynamicTruthSubstitutionInvariantFormula.sourceSubstitutionInvariantSentence,
    eval_sourceSubstitutionInvariantPredicate' hArithmeticReduct]

/-! ## PA-axiom soundness -/

@[simp] theorem eval_apply₁
    (p : Semisentence L 1) (t : ClosedSemiterm L n)
    (v : Fin n → M) :
    (DynamicTruthAxiomSoundnessFormula.apply₁ p t).Evalb (M := M) v ↔
      p.Evalb (M := M) ![t.valb (M := M) v] := by
  simp [DynamicTruthAxiomSoundnessFormula.apply₁,
    Semiformula.eval_substs, Function.comp_def]
  apply iff_of_eq
  congr 2
  funext i
  exact Fin.eq_zero i ▸ rfl

include hArithmeticReduct in
@[simp] theorem eval_sourceAxiomZeroTerm (v : Fin n → M) :
    (DynamicTruthAxiomSoundnessFormula.sourceZeroTerm :
        ClosedSemiterm L n).valb (M := M) v = 0 := by
  rw [DynamicTruthAxiomSoundnessFormula.sourceZeroTerm]
  calc
    _ = FirstOrder.Semiterm.val (s := sourceStructure.lMap
          (ModelCodedPredicateParameters.arithmeticHom 3 2))
        v Empty.elim (‘0’ : ArithmeticSemiterm Empty n) := by
      exact Semiterm.val_lMap
        (ModelCodedPredicateParameters.arithmeticHom 3 2)
        sourceStructure v Empty.elim
    _ = FirstOrder.Semiterm.val
        (s := LO.FirstOrder.Arithmetic.standardModel M)
        v Empty.elim (‘0’ : ArithmeticSemiterm Empty n) := by
      rw [hArithmeticReduct]
    _ = 0 := by simp

include hArithmeticReduct in
set_option maxRecDepth 8000 in
@[simp] theorem eval_sourceAxiomSoundnessPredicate (p : M) :
    DynamicTruthAxiomSoundnessFormula.sourceAxiomSoundnessPredicate.Evalb
        (M := M) ![p] ↔
      (p ∈ (Peano : Theory ℒₒᵣ).Δ₁Class →
        QuantifierBoundedCode ℒₒᵣ (level 0) p →
        ∀ free : M, Arithmetic.Seq free →
          SuccessorTruth lowerRelation (level 0) (level 1)
            0 free p) := by
  simp [DynamicTruthAxiomSoundnessFormula.sourceAxiomSoundnessPredicate,
    DynamicTruthAxiomSoundnessFormula.sourceAxiomSoundnessBody,
    DynamicTruthAxiomSoundnessFormula.sourceRecognizedPAAxiom,
    DynamicTruthAxiomSoundnessFormula.sourceAxiomBoundedDomain,
    DynamicTruthAxiomSoundnessFormula.sourceFreeSequence,
    DynamicTruthTemplateFormula.parameterTerm,
    eval_apply₁, eval_apply₂, eval_apply₃,
    eval_liftArithmeticFormula hArithmeticReduct,
    eval_successorTruthFormula hArithmeticReduct,
    eval_sourceAxiomZeroTerm hArithmeticReduct,
    level]
  constructor
  · intro h hp hbounded free hfree
    exact h free hp hbounded hfree
  · intro h free hp hbounded hfree
    exact h hp hbounded free hfree

include hArithmeticReduct in
@[simp] theorem eval_sourceAxiomSoundnessPredicate' (v : Fin 1 → M) :
    DynamicTruthAxiomSoundnessFormula.sourceAxiomSoundnessPredicate.Evalb
        (M := M) v ↔
      (v 0 ∈ (Peano : Theory ℒₒᵣ).Δ₁Class →
        QuantifierBoundedCode ℒₒᵣ (level 0) (v 0) →
        ∀ free : M, Arithmetic.Seq free →
          SuccessorTruth lowerRelation (level 0) (level 1)
            0 free (v 0)) := by
  rw [Matrix.fun_eq_vec_one v]
  exact eval_sourceAxiomSoundnessPredicate hArithmeticReduct (v 0)

include hArithmeticReduct in
@[simp] theorem eval_sourceAxiomSoundnessSentence :
    DynamicTruthAxiomSoundnessFormula.sourceAxiomSoundnessSentence.Evalb
        (M := M) ![] ↔
      ∀ p : M, p ∈ (Peano : Theory ℒₒᵣ).Δ₁Class →
        QuantifierBoundedCode ℒₒᵣ (level 0) p →
        ∀ free : M, Arithmetic.Seq free →
          SuccessorTruth lowerRelation (level 0) (level 1)
            0 free p := by
  simp [DynamicTruthAxiomSoundnessFormula.sourceAxiomSoundnessSentence,
    eval_sourceAxiomSoundnessPredicate' hArithmeticReduct]

end LeanProofs.BoundedPAConsistency.DynamicTruthCertificateSemantics
