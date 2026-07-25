import BoundedPAConsistency.DynamicTruthPredecessorFormula
import BoundedPAConsistency.DynamicTruthShiftInvariantStructuralSuccessor
import BoundedPAConsistency.DynamicTruthCertificateFieldFamily
import BoundedPAConsistency.DynamicTruthCrossLevelSourceSuccessor
import BoundedPAConsistency.StagedTruthCertificateProofCompiler
import BoundedPAConsistency.FinFunext
import Foundation.FirstOrder.Completeness

/-!
# Fixed-source strong-step interface for dynamic shift invariance

At recurrence index `n`, the previous certificate already says that
`truthFormula n` is invariant under shifting formula codes and free
environments.  The newly established cross-level field relates that current
predicate to the next successor predicate.  Both facts must remain visible
as ordinary source syntax: replacing either one by an opaque assumption
would prevent the structural formula argument from specializing it.

This file puts those two laws in the fixed two-predicate, three-level source
language already used by cross-level coherence.  It defines the exact
strong-induction prefix and target, proves literal specialization at every
possibly nonstandard recurrence index, and compiles the complete off-domain
branch.  The remaining valid-domain branch is exposed as a source-theory
proof obligation; supplying it yields the full strong-step proof consumed by
`ModelCodedStrongInduction`.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantStrongStepSource

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.OrientedHierarchy
open LeanProofs.BoundedPAConsistency.QuantifierFreeTruth
open LeanProofs.BoundedPAConsistency.QuantifierFreeTarski
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthPredecessorFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantStructuralSuccessor
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceTemplate
open LeanProofs.BoundedPAConsistency.DynamicTruthAugmentedLocalOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthCertificateFieldFamily
open LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateParameters
open LeanProofs.BoundedPAConsistency.PrimitiveRecursiveTruthCertificate
open LeanProofs.BoundedPAConsistency.StagedTruthCertificateProofCompiler
open LeanProofs.BoundedPAConsistency.TruthCertificateContextProjection

/-! ## The previous shift law in the cross-level source language -/

/-- Free-environment tail relation in the local four-variable context
`(bound, shifted, free, formula)`. -/
noncomputable def sourceFreeTail : Semisentence SourceLanguage 4 :=
  apply₂ (liftArithmeticFormula isFreeTailDef.val) (#1) (#2)

/-- Bounded-code guard at a selected named hierarchy level. -/
noncomputable def sourceBoundedDomainAt (level : Fin 3) :
    Semisentence SourceLanguage 4 :=
  apply₂
    (liftArithmeticFormula (quantifierBoundedCodeDef ℒₒᵣ).val)
    (levelTerm level) (#3)

/-- A represented shifted formula code together with truth equivalence for
the current predicate placeholder. -/
noncomputable def sourceCurrentShiftedTruthWitness :
    Semisentence SourceLanguage 4 :=
  ∃⁰
    (apply₂ (liftArithmeticFormula (shiftGraph ℒₒᵣ)) (#0) (#4) ⋏
      LogicalConnective.iff
        (currentAtom (#1) (#2) (#0))
        (currentAtom (#1) (#3) (#4)))

/-- Pointwise shift invariance of the current predicate at the old named
level. -/
noncomputable def sourcePriorShiftInvariantBody :
    Semisentence SourceLanguage 4 :=
  Arrow.arrow (sourceFreeTail ⋏ sourceBoundedDomainAt 0)
    sourceCurrentShiftedTruthWitness

/-- Unary formula-code predicate for the previous shift law. -/
noncomputable def sourcePriorShiftInvariantPredicate :
    Semisentence SourceLanguage 1 :=
  ∀⁰ ∀⁰ ∀⁰ sourcePriorShiftInvariantBody

/-- The previous certificate field retained as a closed source formula. -/
noncomputable def sourcePriorShiftInvariantSentence :
    Sentence SourceLanguage :=
  ∀⁰ sourcePriorShiftInvariantPredicate

/-! ## The next shift-invariance target -/

/-- Shift witness for the successor truth predicate constructed from the
current placeholder at the current and next named levels. -/
noncomputable def sourceNextShiftedTruthWitness :
    Semisentence SourceLanguage 4 :=
  ∃⁰
    (apply₂ (liftArithmeticFormula (shiftGraph ℒₒᵣ)) (#0) (#4) ⋏
      LogicalConnective.iff
        (apply₃ sourceCurrentSuccessorTruth (#1) (#2) (#0))
        (apply₃ sourceCurrentSuccessorTruth (#1) (#3) (#4)))

/-- Pointwise next-level shift invariance. -/
noncomputable def sourceNextShiftInvariantBody :
    Semisentence SourceLanguage 4 :=
  Arrow.arrow (sourceFreeTail ⋏ sourceBoundedDomainAt 1)
    sourceNextShiftedTruthWitness

/-- The unary target predicate used by strong induction on formula codes. -/
noncomputable def sourceNextShiftInvariantPredicate :
    Semisentence SourceLanguage 1 :=
  ∀⁰ ∀⁰ ∀⁰ sourceNextShiftInvariantBody

/-- The current cross-level law is the second ordinary antecedent. -/
noncomputable def sourceCurrentCrossLevelSentence :
    Sentence SourceLanguage :=
  ∀⁰ sourceNextCrossLevelInvariant

/-- Exact source context available immediately before the shift stage. -/
noncomputable def sourceAvailableContext : Sentence SourceLanguage :=
  sourcePriorShiftInvariantSentence ⋏ sourceCurrentCrossLevelSentence

/-! ## Strong-induction prefix and source obligations -/

/-- Arithmetic guard `y < x` under the prefix quantifier. -/
noncomputable def sourcePrefixGuard : Semisentence SourceLanguage 2 :=
  .rel (Sum.inl (Language.LT.lt : (ℒₒᵣ).Rel 2))
    ![(#0 : ClosedSemiterm SourceLanguage 2),
      (#1 : ClosedSemiterm SourceLanguage 2)]

/-- `forall y < x, nextShiftInvariantPredicate(y)`.  This is the same
prefix shape used by the generic model-coded strong-induction adapter. -/
noncomputable def sourceStrongPrefix : Semisentence SourceLanguage 1 :=
  ∀⁰[sourcePrefixGuard]
    (sourceNextShiftInvariantPredicate/[(#0 :
      ClosedSemiterm SourceLanguage 2)])

/-- The complete fixed-source strong-step theorem required before invoking
the generic represented PA induction adapter. -/
noncomputable def sourceStrongStepSentence : Sentence SourceLanguage :=
  Arrow.arrow sourceAvailableContext
    (∀⁰ Arrow.arrow sourceStrongPrefix
      sourceNextShiftInvariantPredicate)

/-- The unquantified bounded-code domain used for the strong-step split. -/
noncomputable def sourceNextBoundedDomain :
    Semisentence SourceLanguage 1 :=
  apply₂
    (liftArithmeticFormula (quantifierBoundedCodeDef ℒₒᵣ).val)
    (levelTerm 1) (#0)

/-! ### Fixed arithmetic support for the rank-zero constructor family -/

/-- Arithmetic support used by the rank-zero source branch.  Its variables
are `(oldLevel, currentLevel, formula)`.  The existential witness is the
represented shift of the formula, together with exactly the old boundedness
and current Sigma-domain facts needed to use the two source antecedents. -/
noncomputable def arithmeticQuantifierFreeShiftSupportBody :
    ArithmeticSemisentence 3 :=
  Arrow.arrow
    (DynamicTruthFormula.standardApply₂
      (quantifierBoundedCodeDef ℒₒᵣ).val
      (‘0’ : ArithmeticSemiterm Empty 3) (#0))
    (∃⁰
      (DynamicTruthFormula.standardApply₂
          (shiftGraph ℒₒᵣ).val (#0) (#1) ⋏
        (DynamicTruthFormula.standardApply₂
            (quantifierBoundedCodeDef ℒₒᵣ).val (#3) (#1) ⋏
          (DynamicTruthFormula.standardApply₂
              (quantifierBoundedCodeDef ℒₒᵣ).val (#3) (#0) ⋏
            (DynamicTruthFormula.standardApply₂
                isSigmaCodeDef.val (#2) (#1) ⋏
              DynamicTruthFormula.standardApply₂
                isSigmaCodeDef.val (#2) (#0))))))

/-- Universal closure of `arithmeticQuantifierFreeShiftSupportBody`. -/
noncomputable def arithmeticQuantifierFreeShiftSupportSentence :
    ArithmeticSentence :=
  ∀⁰ ∀⁰ ∀⁰ arithmeticQuantifierFreeShiftSupportBody

set_option maxHeartbeats 800000 in
/-- PA proves the rank-zero shift support uniformly for arbitrary (including
nonstandard) old and current hierarchy levels. -/
noncomputable def arithmeticQuantifierFreeShiftSupportProof :
    Peano ⊢! arithmeticQuantifierFreeShiftSupportSentence :=
  (LO.FirstOrder.Arithmetic.complete.{0} Peano _ <| by
    intro M _ hM
    letI : M↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hM
    simp [models_iff, arithmeticQuantifierFreeShiftSupportSentence,
      arithmeticQuantifierFreeShiftSupportBody,
      DynamicTruthFormula.standardApply₂]
    intro oldLevel currentLevel p hp
    have hpqf : IsQuantifierFreeCode p := by
      simpa [IsQuantifierFreeCode] using hp
    have hshiftqf : IsQuantifierFreeCode (shift ℒₒᵣ p) :=
      (QuantifierBoundedCode.shift_iff hpqf.1).mpr hpqf
    have hpRanks := isQuantifierFreeCode_iff.mp hpqf
    have hshiftRanks := isQuantifierFreeCode_iff.mp hshiftqf
    simp [QuantifierBoundedCode, IsSigmaCode,
      hpRanks.1, hpRanks.2.1, hpRanks.2.2,
      hshiftRanks.1, hshiftRanks.2.1, hshiftRanks.2.2]).get

/-- Lift the arithmetic support theorem into the two-predicate source
language.  It remains independent of both predicate interpretations. -/
noncomputable def liftedArithmeticQuantifierFreeShiftSupportProof :
    twoPredicateParameterPeano 3 3 3 ⊢!
      arithmeticQuantifierFreeShiftSupportSentence.lMap
        (arithmeticHom 3 3 3) :=
  (Theory.Proof.small_complete <|
    lMap_models_lMap (Theory.Proof.sound
      (show Peano ⊢ arithmeticQuantifierFreeShiftSupportSentence from
        ⟨arithmeticQuantifierFreeShiftSupportProof⟩))).get

/-- Relational companion to the support theorem.  Unlike the existential
support above, this sentence applies to *any* witness accepted by
`shiftGraph`; this is what lets us use the witness supplied by the previous
shift-invariance field without appealing to meta-level graph functionality. -/
noncomputable def arithmeticQuantifierFreeShiftClosureBody :
    ArithmeticSemisentence 4 :=
  Arrow.arrow
    (DynamicTruthFormula.standardApply₂
        (quantifierBoundedCodeDef ℒₒᵣ).val
        (‘0’ : ArithmeticSemiterm Empty 4) (#1) ⋏
      DynamicTruthFormula.standardApply₂
        (shiftGraph ℒₒᵣ).val (#0) (#1))
    (DynamicTruthFormula.standardApply₂
        (quantifierBoundedCodeDef ℒₒᵣ).val (#3) (#1) ⋏
      (DynamicTruthFormula.standardApply₂
          (quantifierBoundedCodeDef ℒₒᵣ).val (#3) (#0) ⋏
        (DynamicTruthFormula.standardApply₂
            isSigmaCodeDef.val (#2) (#1) ⋏
          DynamicTruthFormula.standardApply₂
            isSigmaCodeDef.val (#2) (#0))))

noncomputable def arithmeticQuantifierFreeShiftClosureSentence :
    ArithmeticSentence :=
  ∀⁰ ∀⁰ ∀⁰ ∀⁰ arithmeticQuantifierFreeShiftClosureBody

set_option maxHeartbeats 800000 in
noncomputable def arithmeticQuantifierFreeShiftClosureProof :
    Peano ⊢! arithmeticQuantifierFreeShiftClosureSentence :=
  (LO.FirstOrder.Arithmetic.complete.{0} Peano _ <| by
    intro M _ hM
    letI : M↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hM
    simp [models_iff, arithmeticQuantifierFreeShiftClosureSentence,
      arithmeticQuantifierFreeShiftClosureBody,
      DynamicTruthFormula.standardApply₂]
    intro oldLevel currentLevel p hp
    have hpqf : IsQuantifierFreeCode p := by
      simpa [IsQuantifierFreeCode] using hp
    have hshiftqf : IsQuantifierFreeCode (shift ℒₒᵣ p) :=
      (QuantifierBoundedCode.shift_iff hpqf.1).mpr hpqf
    have hpRanks := isQuantifierFreeCode_iff.mp hpqf
    have hshiftRanks := isQuantifierFreeCode_iff.mp hshiftqf
    simp [QuantifierBoundedCode, IsSigmaCode,
      hpRanks.1, hpRanks.2.1, hpRanks.2.2,
      hshiftRanks.1, hshiftRanks.2.1, hshiftRanks.2.2]).get

noncomputable def liftedArithmeticQuantifierFreeShiftClosureProof :
    twoPredicateParameterPeano 3 3 3 ⊢!
      arithmeticQuantifierFreeShiftClosureSentence.lMap
        (arithmeticHom 3 3 3) :=
  (Theory.Proof.small_complete <|
    lMap_models_lMap (Theory.Proof.sound
      (show Peano ⊢ arithmeticQuantifierFreeShiftClosureSentence from
        ⟨arithmeticQuantifierFreeShiftClosureProof⟩))).get

/-- The bounded-domain test depends only on the formula code.  This explicit
semantic alignment avoids relying on simplifier normalization across the
three quantifiers in `sourceNextShiftInvariantPredicate`. -/
private theorem eval_sourceBoundedDomainAt_one_iff
    {M : Type*} [Structure SourceLanguage M]
    (p bound shifted free : M) :
    (Semiformula.Eval ![bound, shifted, free, p] Empty.elim)
        (sourceBoundedDomainAt 1) ↔
      (Semiformula.Eval ![p] Empty.elim) sourceNextBoundedDomain := by
  simp [sourceBoundedDomainAt, sourceNextBoundedDomain,
    DynamicTruthCrossLevelSourceTemplate.apply₂,
    DynamicTruthCrossLevelSourceTemplate.levelTerm,
    TwoPredicateSourceContextInductionKernel.namedParameterTerm]

/-- Valid-domain part of the strong step.  This is the remaining
constructor-wise structural theorem. -/
noncomputable def sourceValidDomainStrongStepSentence :
    Sentence SourceLanguage :=
  Arrow.arrow sourceAvailableContext
    (∀⁰ Arrow.arrow sourceStrongPrefix
      (Arrow.arrow sourceNextBoundedDomain
        sourceNextShiftInvariantPredicate))

/-- Complementary off-domain part. -/
noncomputable def sourceOffDomainStrongStepSentence :
    Sentence SourceLanguage :=
  Arrow.arrow sourceAvailableContext
    (∀⁰ Arrow.arrow sourceStrongPrefix
      (Arrow.arrow (∼sourceNextBoundedDomain)
        sourceNextShiftInvariantPredicate))

/-! ### The quantifier-free constructor family -/

/-- Rank-zero formula-code guard, with only the induction variable free.
This covers the atomic and Boolean constructors in one represented family. -/
noncomputable def sourceQuantifierFreeDomain :
    Semisentence SourceLanguage 1 :=
  apply₂
    (liftArithmeticFormula (quantifierBoundedCodeDef ℒₒᵣ).val)
    (DynamicTruthCrossLevelSourceSuccessor.sourceArithmeticZero (n := 1))
    (#0)

/-- The rank-zero part of the valid-domain strong step.  It keeps the exact
source context and strong prefix even though the constructor calculation
does not need the latter. -/
noncomputable def sourceQuantifierFreeStrongStepSentence :
    Sentence SourceLanguage :=
  Arrow.arrow sourceAvailableContext
    (∀⁰ Arrow.arrow sourceStrongPrefix
      (Arrow.arrow sourceQuantifierFreeDomain
        sourceNextShiftInvariantPredicate))

set_option maxHeartbeats 800000 in
noncomputable def sourceQuantifierFreeStrongStepProof :
    twoPredicateParameterPeano 3 3 3 ⊢!
      sourceQuantifierFreeStrongStepSentence :=
  (Theory.Proof.small_complete <| consequence_iff.mpr fun _ ↦ by
    simp [models_iff, sourceQuantifierFreeStrongStepSentence,
      sourceAvailableContext, sourcePriorShiftInvariantSentence,
      sourcePriorShiftInvariantPredicate, sourcePriorShiftInvariantBody,
      sourceCurrentShiftedTruthWitness,
      sourceCurrentCrossLevelSentence, sourceNextCrossLevelInvariant,
      sourceNextCrossLevelBody, sourceCurrentSigmaDomain,
      sourceNextShiftInvariantPredicate, sourceNextShiftInvariantBody,
      sourceNextShiftedTruthWitness, sourceFreeTail,
      sourceBoundedDomainAt, sourceQuantifierFreeDomain,
      DynamicTruthCrossLevelSourceTemplate.apply₂,
      DynamicTruthCrossLevelSourceTemplate.apply₃,
      DynamicTruthCrossLevelSourceTemplate.liftArithmeticFormula,
      DynamicTruthCrossLevelSourceTemplate.currentAtom,
      DynamicTruthCrossLevelSourceSuccessor.sourceArithmeticZero,
      Semiformula.eval_rew, Semiformula.eval_lMap,
      Function.comp_def]
    intro ambient _structure _models hprior hcross p _prefix hqf
    letI : Nonempty _ := ⟨ambient⟩
    have hsupport := models_of_provable _models
      (show twoPredicateParameterPeano 3 3 3 ⊢
          arithmeticQuantifierFreeShiftSupportSentence.lMap
            (arithmeticHom 3 3 3) from
        ⟨liftedArithmeticQuantifierFreeShiftSupportProof⟩)
    simp [models_iff, arithmeticQuantifierFreeShiftSupportSentence,
      arithmeticQuantifierFreeShiftSupportBody,
      DynamicTruthFormula.standardApply₂] at hsupport
    have hclosure := models_of_provable _models
      (show twoPredicateParameterPeano 3 3 3 ⊢
          arithmeticQuantifierFreeShiftClosureSentence.lMap
            (arithmeticHom 3 3 3) from
        ⟨liftedArithmeticQuantifierFreeShiftClosureProof⟩)
    simp [models_iff, arithmeticQuantifierFreeShiftClosureSentence,
      arithmeticQuantifierFreeShiftClosureBody,
      DynamicTruthFormula.standardApply₂] at hclosure
    let oldLevel :=
      (levelTerm (n := 0) (0 : Fin 3)).val (fun _ ↦ p) Empty.elim
    let currentLevel :=
      (levelTerm (n := 0) (1 : Fin 3)).val (fun _ ↦ p) Empty.elim
    have hs := hsupport oldLevel currentLevel p (by
      rw [Semiformula.eval_lMap, Semiformula.eval_rew]
      have hb :
          (FirstOrder.Semiterm.val
                (s := _structure.lMap (arithmeticHom 3 3 3))
                ![p, currentLevel, oldLevel] Empty.elim ∘
              (Rew.subst
                ![(‘0’ : ArithmeticSemiterm Empty 3),
                  (#0 : ArithmeticSemiterm Empty 3)]) ∘
              FirstOrder.Semiterm.bvar) =
            (fun i ↦ FirstOrder.Semiterm.val
              (s := _structure) ![p] Empty.elim
              (![DynamicTruthCrossLevelSourceSuccessor.sourceArithmeticZero
                    (n := 1),
                  (#0 : ClosedSemiterm SourceLanguage 1)] i)) := by
        refine funext_fin2 ?_ ?_
        · simp [Function.comp_def,
            DynamicTruthCrossLevelSourceSuccessor.sourceArithmeticZero,
            FirstOrder.Semiterm.val_lMap]
          congr 1
          funext j
          exact j.elim0
        · simp [Function.comp_def]
      have hf :
          (FirstOrder.Semiterm.val
                (s := _structure.lMap (arithmeticHom 3 3 3))
                ![p, currentLevel, oldLevel] Empty.elim ∘
              (Rew.subst
                ![(‘0’ : ArithmeticSemiterm Empty 3),
                  (#0 : ArithmeticSemiterm Empty 3)]) ∘
              FirstOrder.Semiterm.fvar) = Empty.elim := by
        funext i
        exact Empty.elim i
      simpa only [hb, hf,
        DynamicTruthCrossLevelSourceSuccessor.sourceArithmeticZero] using
        hqf)
    rcases hs with
      ⟨canonicalShift, _canonicalGraph, hpOld, _canonicalOld,
        hpSigma, _canonicalSigma⟩
    rw [Semiformula.eval_lMap, Semiformula.eval_rew] at hpOld hpSigma
    intro free shifted bound htail _hbounded
    rcases hprior p free shifted bound htail (by
      have hb :
          (fun i ↦ FirstOrder.Semiterm.val
              (s := _structure)
              ![bound, shifted, free, p] Empty.elim
              (![levelTerm (n := 4) (0 : Fin 3),
                  (#3 : ClosedSemiterm SourceLanguage 4)] i)) =
            (FirstOrder.Semiterm.val
                (s := _structure.lMap (arithmeticHom 3 3 3))
                ![canonicalShift, p, currentLevel, oldLevel] Empty.elim ∘
              (Rew.subst
                ![(#3 : ArithmeticSemiterm Empty 4),
                  (#1 : ArithmeticSemiterm Empty 4)]) ∘
              FirstOrder.Semiterm.bvar) := by
        refine funext_fin2 ?_ ?_
        · simp [oldLevel, levelTerm,
          TwoPredicateSourceContextInductionKernel.namedParameterTerm]
        · simp
      have hf :
          (FirstOrder.Semiterm.val
                (s := _structure.lMap (arithmeticHom 3 3 3))
                ![canonicalShift, p, currentLevel, oldLevel] Empty.elim ∘
              (Rew.subst
                ![(#3 : ArithmeticSemiterm Empty 4),
                  (#1 : ArithmeticSemiterm Empty 4)]) ∘
              FirstOrder.Semiterm.fvar) = Empty.elim := by
        funext i
        exact Empty.elim i
      simpa only [hb, hf] using hpOld) with
      ⟨q, hqGraph, hcurrent⟩
    have hqFacts := hclosure oldLevel currentLevel p q (by
      rw [Semiformula.eval_lMap, Semiformula.eval_rew]
      have hb :
          (FirstOrder.Semiterm.val
                (s := _structure.lMap (arithmeticHom 3 3 3))
                ![q, p, currentLevel, oldLevel] Empty.elim ∘
              (Rew.subst
                ![(‘0’ : ArithmeticSemiterm Empty 4),
                  (#1 : ArithmeticSemiterm Empty 4)]) ∘
              FirstOrder.Semiterm.bvar) =
            (fun i ↦ FirstOrder.Semiterm.val
              (s := _structure) ![p] Empty.elim
              (![DynamicTruthCrossLevelSourceSuccessor.sourceArithmeticZero
                    (n := 1),
                  (#0 : ClosedSemiterm SourceLanguage 1)] i)) := by
        refine funext_fin2 ?_ ?_
        · simp [Function.comp_def,
            DynamicTruthCrossLevelSourceSuccessor.sourceArithmeticZero,
            FirstOrder.Semiterm.val_lMap]
          congr 1
          funext j
          exact j.elim0
        · simp [Function.comp_def]
      have hf :
          (FirstOrder.Semiterm.val
                (s := _structure.lMap (arithmeticHom 3 3 3))
                ![q, p, currentLevel, oldLevel] Empty.elim ∘
              (Rew.subst
                ![(‘0’ : ArithmeticSemiterm Empty 4),
                  (#1 : ArithmeticSemiterm Empty 4)]) ∘
              FirstOrder.Semiterm.fvar) = Empty.elim := by
        funext i
        exact Empty.elim i
      simpa only [hb, hf,
        DynamicTruthCrossLevelSourceSuccessor.sourceArithmeticZero] using
        hqf) (by
      rw [Semiformula.eval_lMap, Semiformula.eval_rew]
      have hb :
          (FirstOrder.Semiterm.val
                (s := _structure.lMap (arithmeticHom 3 3 3))
                ![q, p, currentLevel, oldLevel] Empty.elim ∘
              (Rew.subst
                ![(#0 : ArithmeticSemiterm Empty 4),
                  (#1 : ArithmeticSemiterm Empty 4)]) ∘
              FirstOrder.Semiterm.bvar) =
            (fun i ↦ FirstOrder.Semiterm.val
              (s := _structure)
              ![q, bound, shifted, free, p] Empty.elim
              (![(#0 : ClosedSemiterm SourceLanguage 5),
                  (#4 : ClosedSemiterm SourceLanguage 5)] i)) := by
        refine funext_fin2 ?_ ?_
        · simp [Function.comp_def]
        · simp [Function.comp_def]
      have hf :
          (FirstOrder.Semiterm.val
                (s := _structure.lMap (arithmeticHom 3 3 3))
                ![q, p, currentLevel, oldLevel] Empty.elim ∘
              (Rew.subst
                ![(#0 : ArithmeticSemiterm Empty 4),
                  (#1 : ArithmeticSemiterm Empty 4)]) ∘
              FirstOrder.Semiterm.fvar) = Empty.elim := by
        funext i
        exact Empty.elim i
      simpa only [hb, hf] using hqGraph)
    have hqSigma := hqFacts.2.2.2
    rw [Semiformula.eval_lMap, Semiformula.eval_rew] at hqSigma
    have hcp := (hcross p free bound).1 (by
      have hb :
          (fun i ↦ FirstOrder.Semiterm.val
              (s := _structure)
              ![bound, free, p] Empty.elim
              (![levelTerm (n := 3) (1 : Fin 3),
                  (#2 : ClosedSemiterm SourceLanguage 3)] i)) =
            (FirstOrder.Semiterm.val
                (s := _structure.lMap (arithmeticHom 3 3 3))
                ![canonicalShift, p, currentLevel, oldLevel] Empty.elim ∘
              (Rew.subst
                ![(#2 : ArithmeticSemiterm Empty 4),
                  (#1 : ArithmeticSemiterm Empty 4)]) ∘
              FirstOrder.Semiterm.bvar) := by
        refine funext_fin2 ?_ ?_
        · simp [currentLevel, levelTerm,
          TwoPredicateSourceContextInductionKernel.namedParameterTerm]
        · simp
      have hf :
          (FirstOrder.Semiterm.val
                (s := _structure.lMap (arithmeticHom 3 3 3))
                ![canonicalShift, p, currentLevel, oldLevel] Empty.elim ∘
              (Rew.subst
                ![(#2 : ArithmeticSemiterm Empty 4),
                  (#1 : ArithmeticSemiterm Empty 4)]) ∘
              FirstOrder.Semiterm.fvar) = Empty.elim := by
        funext i
        exact Empty.elim i
      simpa only [hb, hf] using hpSigma)
    have hcq := (hcross q shifted bound).1 (by
      have hb :
          (fun i ↦ FirstOrder.Semiterm.val
              (s := _structure)
              ![bound, shifted, q] Empty.elim
              (![levelTerm (n := 3) (1 : Fin 3),
                  (#2 : ClosedSemiterm SourceLanguage 3)] i)) =
            (FirstOrder.Semiterm.val
                (s := _structure.lMap (arithmeticHom 3 3 3))
                ![q, p, currentLevel, oldLevel] Empty.elim ∘
              (Rew.subst
                ![(#2 : ArithmeticSemiterm Empty 4),
                  (#0 : ArithmeticSemiterm Empty 4)]) ∘
              FirstOrder.Semiterm.bvar) := by
        refine funext_fin2 ?_ ?_
        · simp [currentLevel, levelTerm,
          TwoPredicateSourceContextInductionKernel.namedParameterTerm]
        · simp
      have hf :
          (FirstOrder.Semiterm.val
                (s := _structure.lMap (arithmeticHom 3 3 3))
                ![q, p, currentLevel, oldLevel] Empty.elim ∘
              (Rew.subst
                ![(#2 : ArithmeticSemiterm Empty 4),
                  (#0 : ArithmeticSemiterm Empty 4)]) ∘
              FirstOrder.Semiterm.fvar) = Empty.elim := by
        funext i
        exact Empty.elim i
      simpa only [hb, hf] using hqSigma)
    have hcurrentToSuccessor := hcurrent.trans (by
      simpa [TwoPredicateSourceContextInductionKernel.secondAtom] using
        hcp.symm)
    refine ⟨q, hqGraph, ?_⟩
    have hshiftedEnv :
        (fun i ↦ FirstOrder.Semiterm.val
          (s := _structure)
          ![q, bound, shifted, free, p] Empty.elim
          (![(#1 : ClosedSemiterm SourceLanguage 5),
              (#2 : ClosedSemiterm SourceLanguage 5),
              (#0 : ClosedSemiterm SourceLanguage 5)] i)) =
          ![bound, shifted, q] := by
      refine funext_fin3 ?_ ?_ ?_ <;> simp
    have hfreeEnv :
        (fun i ↦ FirstOrder.Semiterm.val
          (s := _structure)
          ![q, bound, shifted, free, p] Empty.elim
          (![(#1 : ClosedSemiterm SourceLanguage 5),
              (#3 : ClosedSemiterm SourceLanguage 5),
              (#4 : ClosedSemiterm SourceLanguage 5)] i)) =
          ![bound, free, p] := by
      refine funext_fin3 ?_ ?_ ?_ <;> simp
    simpa only [hshiftedEnv, hfreeEnv] using hcq.trans (by
      simpa [TwoPredicateSourceContextInductionKernel.secondAtom] using
        hcurrentToSuccessor)).get

set_option maxHeartbeats 800000 in
/-- Outside the bounded formula domain, every instance of the target is
vacuous.  This is a genuine fixed lifted-PA proof retaining both the source
context and the strong prefix as antecedents. -/
noncomputable def sourceOffDomainStrongStepProof :
    twoPredicateParameterPeano 3 3 3 ⊢!
      sourceOffDomainStrongStepSentence :=
  (Theory.Proof.small_complete <| consequence_iff.mpr fun _ ↦ by
    simp [models_iff, sourceOffDomainStrongStepSentence,
      sourceStrongPrefix, sourceNextBoundedDomain,
      sourceNextShiftInvariantPredicate, sourceNextShiftInvariantBody,
      sourceBoundedDomainAt]
    intro ambient _structure _models _context p _prefix houtside
      bound shifted free _tail hbounded
    exfalso
    apply houtside
    exact (eval_sourceBoundedDomainAt_one_iff
      p free shifted bound).mp hbounded).get

/-- A proof of the valid-domain branch completes the exact source strong
step.  No semantic premise or new theory axiom is introduced: the field is
itself a derivation in the original fixed lifted-PA source theory. -/
structure SourceValidDomainStep where
  proof : twoPredicateParameterPeano 3 3 3 ⊢!
    sourceValidDomainStrongStepSentence

set_option maxHeartbeats 800000 in
/-- Recombine valid and off-domain branches by fixed first-order reasoning. -/
noncomputable def SourceValidDomainStep.proveStrongStep
    (step : SourceValidDomainStep) :
    twoPredicateParameterPeano 3 3 3 ⊢! sourceStrongStepSentence :=
  (Theory.Proof.small_complete <| consequence_iff.mpr fun _ ↦ by
    intro _ambient _structure hmodels
    have hvalid := models_of_provable hmodels
      (show twoPredicateParameterPeano 3 3 3 ⊢
          sourceValidDomainStrongStepSentence from ⟨step.proof⟩)
    have hoff := models_of_provable hmodels
      (show twoPredicateParameterPeano 3 3 3 ⊢
          sourceOffDomainStrongStepSentence from
        ⟨sourceOffDomainStrongStepProof⟩)
    simp [models_iff, sourceValidDomainStrongStepSentence,
      sourceOffDomainStrongStepSentence, sourceStrongStepSentence] at hvalid hoff
    simp [models_iff, sourceStrongStepSentence]
    intro hcontext p hprefix
    by_cases hdomain :
        (Semiformula.Eval ![p] Empty.elim) sourceNextBoundedDomain
    · exact hvalid hcontext p hprefix hdomain
    · exact hoff hcontext p hprefix hdomain).get

/-! ## Exact specialization into the represented orbit -/

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- Typed form of the two source antecedents. -/
noncomputable def availableContextFormula
    (current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (oldLevel currentLevel nextLevel : V) :
    Bootstrapping.Formula V ℒₒᵣ :=
  upperShiftInvariantFormula current oldLevel ⋏
    crossLevelFormula current currentLevel nextLevel

/-- Literal specialization of the complete source antecedent. -/
@[simp] theorem translate_sourceAvailableContext
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (levels : Fin 3 → V) :
    translateFormula predecessor current levels
        (Rewriting.emb sourceAvailableContext) =
      availableContextFormula current (levels 0) (levels 1) (levels 2) := by
  simp [sourceAvailableContext, sourcePriorShiftInvariantSentence,
    sourcePriorShiftInvariantPredicate, sourcePriorShiftInvariantBody,
    sourceCurrentShiftedTruthWitness, sourceFreeTail,
    sourceBoundedDomainAt, sourceCurrentCrossLevelSentence,
    availableContextFormula, upperShiftInvariantFormula,
    freeTailFormula, boundedDomainFormula, shiftedTruthWitnessFormula,
    DynamicTruthFormula.apply₃,
    ModelCodedTwoPredicateParameters.translateFormula,
    ModelCodedTwoPredicateParameters.translateTerm,
    Bootstrapping.Semiformula.imp_def, LogicalConnective.iff,
    crossLevelFormula]
  constructor
  · have hsneg :
        translateFormula predecessor current levels
            (Semiformula.neg
              ((Rewriting.app Rew.emb) sourceFreeTail ⋏
                (Rewriting.app Rew.emb) (sourceBoundedDomainAt 0))) =
          ∼translateFormula predecessor current levels
            ((Rewriting.app Rew.emb) sourceFreeTail ⋏
              (Rewriting.app Rew.emb) (sourceBoundedDomainAt 0)) := by
        simpa only [Semiformula.neg_eq] using
          (translateFormula_neg predecessor current levels
            ((Rewriting.app Rew.emb) sourceFreeTail ⋏
              (Rewriting.app Rew.emb) (sourceBoundedDomainAt 0)))
    simp only [sourceFreeTail, sourceBoundedDomainAt] at hsneg
    rw [hsneg]
    simp [sourceFreeTail, sourceBoundedDomainAt,
      ModelCodedTwoPredicateParameters.translateFormula,
      ModelCodedTwoPredicateParameters.translateTerm]
  · constructor
    · have hsneg :
          translateFormula predecessor current levels
              (Semiformula.neg
                ((Rewriting.app Rew.emb)
                  (currentAtom
                    (#1 : ClosedSemiterm SourceLanguage 5) (#2) (#0)))) =
            ∼translateFormula predecessor current levels
              ((Rewriting.app Rew.emb)
                (currentAtom
                  (#1 : ClosedSemiterm SourceLanguage 5) (#2) (#0))) := by
          simpa only [Semiformula.neg_eq] using
            (translateFormula_neg predecessor current levels
              ((Rewriting.app Rew.emb)
                (currentAtom
                  (#1 : ClosedSemiterm SourceLanguage 5) (#2) (#0))))
      rw [hsneg]
      simp [DynamicTruthFormula.apply₃,
        ModelCodedTwoPredicateParameters.translateFormula,
        ModelCodedTwoPredicateParameters.translateTerm]
    · have hsneg :
          translateFormula predecessor current levels
              (Semiformula.neg
                ((Rewriting.app Rew.emb)
                  (currentAtom
                    (#1 : ClosedSemiterm SourceLanguage 5) (#3) (#4)))) =
            ∼translateFormula predecessor current levels
              ((Rewriting.app Rew.emb)
                (currentAtom
                  (#1 : ClosedSemiterm SourceLanguage 5) (#3) (#4))) := by
          simpa only [Semiformula.neg_eq] using
            (translateFormula_neg predecessor current levels
              ((Rewriting.app Rew.emb)
                (currentAtom
                  (#1 : ClosedSemiterm SourceLanguage 5) (#3) (#4))))
      rw [hsneg]
      simp [DynamicTruthFormula.apply₃,
        ModelCodedTwoPredicateParameters.translateFormula,
        ModelCodedTwoPredicateParameters.translateTerm]

/-- Literal specialization of the unary next-level target. -/
@[simp] theorem translate_sourceNextShiftInvariantPredicate
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (levels : Fin 3 → V) :
    translateFormula predecessor current levels
        (Rewriting.emb sourceNextShiftInvariantPredicate) =
      shiftInvariantPredicateFormula current (levels 1) (levels 2) := by
  simp [sourceNextShiftInvariantPredicate, sourceNextShiftInvariantBody,
    sourceNextShiftedTruthWitness, sourceFreeTail,
    sourceBoundedDomainAt, shiftInvariantPredicateFormula,
    shiftInvariantBodyFormula, freeTailFormula, boundedDomainFormula,
    shiftedTruthWitnessFormula, DynamicTruthFormula.apply₃,
    ModelCodedTwoPredicateParameters.translateFormula,
    ModelCodedTwoPredicateParameters.translateTerm,
    Bootstrapping.Semiformula.imp_def, LogicalConnective.iff]
  constructor
  · have hsneg :
        translateFormula predecessor current levels
            (Semiformula.neg
              ((Rewriting.app Rew.emb) sourceFreeTail ⋏
                (Rewriting.app Rew.emb) (sourceBoundedDomainAt 1))) =
          ∼translateFormula predecessor current levels
            ((Rewriting.app Rew.emb) sourceFreeTail ⋏
              (Rewriting.app Rew.emb) (sourceBoundedDomainAt 1)) := by
        simpa only [Semiformula.neg_eq] using
          (translateFormula_neg predecessor current levels
            ((Rewriting.app Rew.emb) sourceFreeTail ⋏
              (Rewriting.app Rew.emb) (sourceBoundedDomainAt 1)))
    simp only [sourceFreeTail, sourceBoundedDomainAt] at hsneg
    rw [hsneg]
    simp [sourceFreeTail, sourceBoundedDomainAt,
      ModelCodedTwoPredicateParameters.translateFormula,
      ModelCodedTwoPredicateParameters.translateTerm]
  · constructor
    · have hsneg :
          translateFormula predecessor current levels
              (Semiformula.neg
                ((Rewriting.app Rew.emb)
                  (apply₃ sourceCurrentSuccessorTruth
                    (#1 : ClosedSemiterm SourceLanguage 5) (#2) (#0)))) =
            ∼translateFormula predecessor current levels
              ((Rewriting.app Rew.emb)
                (apply₃ sourceCurrentSuccessorTruth
                  (#1 : ClosedSemiterm SourceLanguage 5) (#2) (#0))) := by
          simpa only [Semiformula.neg_eq] using
            (translateFormula_neg predecessor current levels
              ((Rewriting.app Rew.emb)
                (apply₃ sourceCurrentSuccessorTruth
                  (#1 : ClosedSemiterm SourceLanguage 5) (#2) (#0))))
      rw [hsneg]
      simp [DynamicTruthFormula.apply₃,
        ModelCodedTwoPredicateParameters.translateFormula,
        ModelCodedTwoPredicateParameters.translateTerm]
    · have hsneg :
          translateFormula predecessor current levels
              (Semiformula.neg
                ((Rewriting.app Rew.emb)
                  (apply₃ sourceCurrentSuccessorTruth
                    (#1 : ClosedSemiterm SourceLanguage 5) (#3) (#4)))) =
            ∼translateFormula predecessor current levels
              ((Rewriting.app Rew.emb)
                (apply₃ sourceCurrentSuccessorTruth
                  (#1 : ClosedSemiterm SourceLanguage 5) (#3) (#4))) := by
          simpa only [Semiformula.neg_eq] using
            (translateFormula_neg predecessor current levels
              ((Rewriting.app Rew.emb)
                (apply₃ sourceCurrentSuccessorTruth
                  (#1 : ClosedSemiterm SourceLanguage 5) (#3) (#4))))
      rw [hsneg]
      simp [DynamicTruthFormula.apply₃,
        ModelCodedTwoPredicateParameters.translateFormula,
        ModelCodedTwoPredicateParameters.translateTerm]

/-- Uniform predecessor view of the already established shift field. -/
@[simp] theorem upperShiftInvariantFormula_previous_orbit (n : V) :
    upperShiftInvariantFormula (truthFormula n) n =
      modelIndexedShiftInvariantFormula n := by
  rcases zero_or_succ n with rfl | ⟨k, rfl⟩
  · simpa only [modelIndexedShiftInvariantFormula_zero] using
      (baseShiftInvariantFormula_eq_upper (V := V)).symm
  · simpa only [modelIndexedShiftInvariantFormula_succ] using
      (orbitSuccessorShiftInvariantFormula_upper k).symm

/-- At every model index, the source antecedent is exactly the previous
shift field conjoined with the newly established cross field. -/
@[simp] theorem translate_sourceAvailableContext_orbit (n : V) :
    translateFormula (predecessorTruthFormula n) (truthFormula n)
        ![n, n + 1, n + 1 + 1]
        (Rewriting.emb sourceAvailableContext) =
      (modelIndexedShiftInvariantFormula n ⋏
        orbitSuccessorCrossLevelFormula n) := by
  rw [translate_sourceAvailableContext]
  simp [availableContextFormula, orbitSuccessorCrossLevelFormula]

/-- The source target specializes to the exact predicate already installed
by `DynamicTruthShiftInvariantStructuralSuccessor`. -/
@[simp] theorem translate_sourceNextShiftInvariantPredicate_orbit
    [V↓[ℒₒᵣ] ⊧* Peano] (n : V) :
    translateFormula (predecessorTruthFormula n) (truthFormula n)
        ![n, n + 1, n + 1 + 1]
        (Rewriting.emb sourceNextShiftInvariantPredicate) =
      nextShiftInvariantPredicate n := by
  rw [translate_sourceNextShiftInvariantPredicate]
  rfl

/-- Orbit-specialized name for the two-field source antecedent. -/
noncomputable def orbitAvailableContext (n : V) :
    Bootstrapping.Formula V ℒₒᵣ :=
  modelIndexedShiftInvariantFormula n ⋏
    orbitSuccessorCrossLevelFormula n

variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

/-- The exact production `crossContext` proves the smaller fixed-source
antecedent: project the preceding certificate's shift field and the newly
proved cross field, while retaining the augmented local field in the staged
context. -/
noncomputable def proveOrbitAvailableFromAugmentedCrossContext (n : V) :
    Peano.internalize V ⊢!
      crossContext
          ((compiledDynamicTruthCertificateFamily (V := V)).fields n)
          (DynamicTruthQuantifierFreeAnchor.orbitCompiledLocalBundleWithQuantifierFreeIntroduction n)
          (orbitSuccessorCrossLevelFormula n) 🡒
        orbitAvailableContext n := by
  unfold crossContext localContext orbitAvailableContext
  exact Entailment.CK_of_C_of_C
    (Entailment.C_trans
      (Entailment.C_trans Entailment.and₁ Entailment.and₁)
      (TruthCertificateFields.proveShiftInvariant
        (T := Peano.internalize V)
        ((compiledDynamicTruthCertificateFamily (V := V)).fields n)))
    Entailment.and₂

end LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantStrongStepSource
