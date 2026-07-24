import BoundedPAConsistency.DynamicTruthAxiomSoundnessInterfaceSemantic
import BoundedPAConsistency.DynamicTruthCertificateSemantics
import BoundedPAConsistency.DynamicTruthLowerExistentialInterface
import BoundedPAConsistency.DynamicTruthPAMinusAxioms
import BoundedPAConsistency.DynamicTruthSemanticInductionCompilation
import BoundedPAConsistency.ModelCodedPredicateEqualityQuotient
import Foundation.FirstOrder.Completeness

/-!
# Fixed-source step for dynamic PA-axiom soundness

The staged successor certificate proves soundness of PA's represented axiom
recognizer after the new local, cross-level, shift, and substitution laws
have been installed.  The semantic argument is already complete: given the
Tarski laws of the new successor, its substitution field, and the three
model-induction interfaces, every recognized bounded axiom is true.

This module expresses that argument once, in the common one-predicate,
two-parameter source language.  Two of the three induction interfaces are
not laws of the certificate but ordinary successor induction for a closed
unary predicate.  They therefore appear in the source context as literal
induction axioms for the two packed predicates fixed below; after
specialization each is discharged by PA's represented induction recognizer,
exactly as for the semantic-induction interface.

The lower predicate's existential law is an explicit context conjunct as
well.  It is the one fact about the *previous* orbit member that the
universal Tarski clause of the new successor needs, and it is unavailable at
the base of the orbit, where the whole field is proved by ordinary standard
syntax instead.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessStrongStepSource

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.AbstractSoundness
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessInterfaceSemantic
open LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessSemantic
open LeanProofs.BoundedPAConsistency.DynamicTruthCertificateSemantics
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelStrongStepSource
open LeanProofs.BoundedPAConsistency.DynamicTruthLowerExistentialInterface
open LeanProofs.BoundedPAConsistency.DynamicTruthLowerExistentialLawsFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthPAMinusAxioms
open LeanProofs.BoundedPAConsistency.DynamicTruthSemanticInductionSource
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantPositiveRankStrongStep
open LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantPositiveRankStrongStep
open LeanProofs.BoundedPAConsistency.DynamicTruthSuccessorLaws
open LeanProofs.BoundedPAConsistency.DynamicTruthTemplateFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthTemplateSemantics
open LeanProofs.BoundedPAConsistency.FixedLevelTruth
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateEqualityQuotient
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters

private abbrev L := DynamicTruthTemplateFormula.SourceLanguage

/-! ## Small arithmetic constructors in the source language -/

/-- An arithmetic equation between two source terms. -/
noncomputable def sourceEquals {n : ℕ}
    (t u : ClosedSemiterm L n) : Semisentence L n :=
  .rel (Sum.inl (Language.Eq.eq : (ℒₒᵣ).Rel 2)) ![t, u]

/-- The arithmetic sum of two source terms. -/
def sourceAdd {n : ℕ} (t u : ClosedSemiterm L n) : ClosedSemiterm L n :=
  .func (Sum.inl (Language.Add.add : (ℒₒᵣ).Func 2)) ![t, u]

/-- The second named level is the arithmetic successor of the first.  At
specialization this becomes a reflexive equation between typed numerals. -/
noncomputable def sourceLevelAdjacency : Sentence L :=
  sourceEquals (parameterTerm 1) sourceLowerLevelSuccessor

/-! ## The generic closed induction axiom -/

/-- Ordinary successor induction for a closed unary source predicate.

Only closed predicates are used below, so no universal closure is needed;
after specialization this is literally the induction body accepted by PA's
represented recognizer. -/
noncomputable def sourceInductionAxiom (P : Semisentence L 1) : Sentence L :=
  Arrow.arrow (P/[sourceZero])
    (Arrow.arrow
      (∀⁰ Arrow.arrow
        (P/[(#0 : ClosedSemiterm L 1)])
        (P/[sourceSucc (#0)]))
      (∀⁰ P/[(#0 : ClosedSemiterm L 1)]))

/-! ## Packed predicate for free-environment independence -/

/-- The parameter-packed free-independence invariant applied to an arbitrary
source term.

Beneath the three binders the visible variables are `(free, bound, formula)`
and the induction variable is the explicitly shifted argument. -/
noncomputable def sourceFreeIndependenceAt {n : ℕ}
    (x : ClosedSemiterm L n) : Semisentence L n :=
  ∀⁰ ∀⁰ ∀⁰
    Arrow.arrow
      ((apply₂ (liftArithmeticFormula (quantifierBoundedCodeDef ℒₒᵣ).val)
            (parameterTerm 0) (#2) ⋏
          apply₂ (liftArithmeticFormula (shiftGraph ℒₒᵣ)) (#2) (#2)) ⋏
        (DynamicTruthAxiomSoundnessFormula.apply₁
            (liftArithmeticFormula seqDef.val) (#0) ⋏
          apply₂ (liftArithmeticFormula lhDef.val)
            (Rew.bShift (Rew.bShift (Rew.bShift x))) (#0)))
      (LogicalConnective.iff
        (apply₃ successorTruthFormula (#1) (#0) (#2))
        (apply₃ successorTruthFormula (#1) sourceZero (#2)))

/-- The unary predicate submitted to represented induction. -/
noncomputable def sourceFreeIndependencePredicate : Semisentence L 1 :=
  sourceFreeIndependenceAt (#0)

/-! ## Packed predicate for universal-closure introduction -/

/-- The parameter-packed closure invariant applied to an arbitrary source
term.

Beneath the four binders the visible variables are `(base, free, body,
length)`; beneath the represented `qqAlls` witness they shift by one. -/
noncomputable def sourceClosureAt {n : ℕ}
    (x : ClosedSemiterm L n) : Semisentence L n :=
  ∀⁰ ∀⁰ ∀⁰ ∀⁰
    (∃⁰
      (apply₃ (liftArithmeticFormula qqAllsDef.val)
          (#0) (#3) (Rew.bShift (Rew.bShift (Rew.bShift
            (Rew.bShift (Rew.bShift x))))) ⋏
        Arrow.arrow
          (apply₂ (liftArithmeticFormula (quantifierBoundedCodeDef ℒₒᵣ).val)
              (parameterTerm 0) (#0) ⋏
            ((∀⁰ Arrow.arrow
                (DynamicTruthAxiomSoundnessFormula.apply₁
                    (liftArithmeticFormula seqDef.val) (#0) ⋏
                  apply₂ (liftArithmeticFormula lhDef.val) (#5) (#0))
                (apply₃ successorTruthFormula (#0) (#3) (#4))) ⋏
              (DynamicTruthAxiomSoundnessFormula.apply₁
                  (liftArithmeticFormula seqDef.val) (#1) ⋏
                (∃⁰
                  (apply₂ (liftArithmeticFormula lhDef.val) (#0) (#2) ⋏
                    sourceEquals
                      (sourceAdd (#0)
                        (Rew.bShift (Rew.bShift (Rew.bShift
                          (Rew.bShift (Rew.bShift (Rew.bShift x)))))))
                      (#5))))))
          (apply₃ successorTruthFormula (#1) (#2) (#0))))

/-- The unary predicate submitted to represented induction. -/
noncomputable def sourceClosurePredicate : Semisentence L 1 :=
  sourceClosureAt (#0)

/-! ## The complete source context and step -/

/-- Every premise consumed by the semantic axiom-soundness theorem.

The first two conjuncts concern the previous orbit member and the adjacency
of the two named levels; the next three are certificate fields already
installed by the staged compiler; the last three are induction interfaces,
one of which is itself a fixed source sentence while the other two are
ordinary induction axioms for the packed predicates above. -/
noncomputable def sourceAxiomSoundnessLawContext : Sentence L :=
  sourceLevelAdjacency ⋏
    (sourceLowerExistentialLawsSentence ⋏
      (DynamicTruthCrossLevelFormula.sourceCrossLevelSentence ⋏
        (DynamicTruthShiftInvariantFormula.sourceShiftInvariantSentence ⋏
          (DynamicTruthSubstitutionInvariantFormula.sourceSubstitutionInvariantSentence ⋏
            (sourceSemanticInductionSentence ⋏
              (sourceInductionAxiom sourceFreeIndependencePredicate ⋏
                sourceInductionAxiom sourceClosurePredicate))))))

/-- Context-relative soundness of the represented PA-axiom recognizer. -/
noncomputable def sourceAxiomSoundnessStepSentence : Sentence L :=
  sourceAxiomSoundnessLawContext 🡒 sourceAxiomSoundnessSentence

/-- Equality-safe form submitted to source completeness. -/
noncomputable def sourceCongruentAxiomSoundnessStepSentence : Sentence L :=
  placeholderCongruenceSentence 3 2 🡒 sourceAxiomSoundnessStepSentence

/-! ## Semantics of the new source components -/

section Semantics

variable {M : Type*}
variable [sourceStructure : Structure L M]
variable [Nonempty M] [ORingStructure M]
variable [hPA : M↓[ℒₒᵣ] ⊧* Peano]

local instance : M↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

variable (hArithmeticReduct :
  sourceStructure.lMap (arithmeticHom 3 2) =
    LO.FirstOrder.Arithmetic.standardModel M)

omit [Nonempty M] hPA in
include hArithmeticReduct in
/-- Read equality in the distinguished arithmetic summand from the reduct
equation.  An arbitrary expanded source prestructure need not interpret its
equality symbol canonically. -/
private theorem source_eq_iff (a b : M) :
    Structure.rel (L := L)
      (Sum.inl (Language.Eq.eq : (ℒₒᵣ).Rel 2)) ![a, b] ↔ a = b := by
  have h := congrArg
    (fun s : Structure ℒₒᵣ M ↦
      @Structure.rel ℒₒᵣ M s 2 Language.Eq.eq ![a, b])
    hArithmeticReduct
  simpa using h

omit [Nonempty M] hPA in
include hArithmeticReduct in
private theorem source_one_eq :
    Structure.func (L := L)
      (Sum.inl (Language.One.one : (ℒₒᵣ).Func 0)) ![] = (1 : M) := by
  have h := congrArg
    (fun s : Structure ℒₒᵣ M ↦
      @Structure.func ℒₒᵣ M s 0 Language.One.one ![])
    hArithmeticReduct
  simpa using h

omit [Nonempty M] hPA in
include hArithmeticReduct in
private theorem source_add_eq (a b : M) :
    Structure.func (L := L)
      (Sum.inl (Language.Add.add : (ℒₒᵣ).Func 2)) ![a, b] = a + b := by
  have h := congrArg
    (fun s : Structure ℒₒᵣ M ↦
      @Structure.func ℒₒᵣ M s 2 Language.Add.add ![a, b])
    hArithmeticReduct
  simpa using h

omit [Nonempty M] hPA in
include hArithmeticReduct in
@[simp] theorem eval_sourceEquals {n : ℕ}
    (t u : ClosedSemiterm L n) (v : Fin n → M) :
    (sourceEquals t u).Evalb (M := M) v ↔
      t.valb (M := M) v = u.valb (M := M) v := by
  have hshape :
      (sourceEquals t u).Evalb (M := M) v ↔
        Structure.rel (L := L) (Sum.inl (Language.Eq.eq : (ℒₒᵣ).Rel 2))
          ![t.valb (M := M) v, u.valb (M := M) v] := by
    apply iff_of_eq
    change Structure.rel _ (fun i ↦
        FirstOrder.Semiterm.val v Empty.elim (![t, u] i)) = _
    congr 1
    exact funext_fin2 rfl rfl
  rw [hshape, source_eq_iff hArithmeticReduct]

omit [Nonempty M] hPA in
include hArithmeticReduct in
@[simp] theorem eval_sourceAdd {n : ℕ}
    (t u : ClosedSemiterm L n) (v : Fin n → M) :
    (sourceAdd t u).valb (M := M) v =
      t.valb (M := M) v + u.valb (M := M) v := by
  have hshape :
      (sourceAdd t u).valb (M := M) v =
        Structure.func (L := L) (Sum.inl (Language.Add.add : (ℒₒᵣ).Func 2))
          ![t.valb (M := M) v, u.valb (M := M) v] := by
    change Structure.func _ (fun i ↦
        FirstOrder.Semiterm.val v Empty.elim (![t, u] i)) = _
    congr 1
    exact funext_fin2 rfl rfl
  rw [hshape, source_add_eq hArithmeticReduct]

omit [Nonempty M] hPA in
include hArithmeticReduct in
@[simp] theorem eval_sourceLevelAdjacency :
    sourceLevelAdjacency.Evalb (M := M) ![] ↔
      DynamicTruthTemplateSemantics.level (M := M) 1 =
        DynamicTruthTemplateSemantics.level (M := M) 0 + 1 := by
  simp [sourceLevelAdjacency, sourceLowerLevelSuccessor,
    DynamicTruthLowerExistentialLawsFormula.sourceOne,
    parameterTerm, DynamicTruthTemplateSemantics.level,
    eval_sourceEquals hArithmeticReduct,
    source_add_eq hArithmeticReduct,
    source_one_eq hArithmeticReduct]

include hArithmeticReduct in
/-- One generic step of the source induction axiom.  Keeping the predicate
abstract prevents its large body from being normalized twice. -/
@[simp] theorem eval_sourceInductionAxiom (P : Semisentence L 1) :
    (sourceInductionAxiom P).Evalb (M := M) ![] ↔
      (P.Evalb (M := M) ![(0 : M)] →
        (∀ x : M, P.Evalb (M := M) ![x] → P.Evalb (M := M) ![x + 1]) →
        ∀ x : M, P.Evalb (M := M) ![x]) := by
  simp [sourceInductionAxiom, Semiformula.eval_substs, Function.comp_def,
    eval_sourceZero hArithmeticReduct, eval_sourceSucc hArithmeticReduct,
    Matrix.constant_eq_singleton]

include hArithmeticReduct in
@[simp] theorem eval_sourceFreeIndependenceAt {n : ℕ}
    (x : ClosedSemiterm L n) (v : Fin n → M) :
    (sourceFreeIndependenceAt x).Evalb (M := M) v ↔
      FreeIndependenceInvariant (DynamicTruthTemplateSemantics.level 0)
        (SuccessorTruth lowerRelation
          (DynamicTruthTemplateSemantics.level 0)
          (DynamicTruthTemplateSemantics.level 1))
        (x.valb (M := M) v) := by
  simp [sourceFreeIndependenceAt, FreeIndependenceInvariant,
    DynamicTruthCertificateSemantics.eval_apply₁,
    DynamicTruthTemplateSemantics.eval_apply₂,
    DynamicTruthTemplateSemantics.eval_apply₃,
    DynamicTruthTemplateSemantics.eval_liftArithmeticFormula
      hArithmeticReduct,
    DynamicTruthTemplateSemantics.eval_successorTruthFormula
      hArithmeticReduct,
    eval_sourceZero hArithmeticReduct,
    FirstOrder.Semiterm.val_bShift,
    (QuantifierBoundedCode.defined ℒₒᵣ (V := M)).iff,
    lh_defined.iff, shift.defined.iff]
  constructor
  · intro h p bound free hbounded hshiftFixed hfree hlen
    exact h p bound free hbounded hshiftFixed.symm hfree hlen.symm
  · intro h p bound free hbounded hshiftFixed hfree hlen
    exact h p bound free hbounded hshiftFixed.symm hfree hlen.symm

include hArithmeticReduct in
@[simp] theorem eval_sourceClosureAt {n : ℕ}
    (x : ClosedSemiterm L n) (v : Fin n → M) :
    (sourceClosureAt x).Evalb (M := M) v ↔
      ClosureInvariant (DynamicTruthTemplateSemantics.level 0)
        (SuccessorTruth lowerRelation
          (DynamicTruthTemplateSemantics.level 0)
          (DynamicTruthTemplateSemantics.level 1))
        (x.valb (M := M) v) := by
  simp [sourceClosureAt, ClosureInvariant,
    DynamicTruthCertificateSemantics.eval_apply₁,
    DynamicTruthTemplateSemantics.eval_apply₂,
    DynamicTruthTemplateSemantics.eval_apply₃,
    DynamicTruthTemplateSemantics.eval_liftArithmeticFormula
      hArithmeticReduct,
    DynamicTruthTemplateSemantics.eval_successorTruthFormula
      hArithmeticReduct,
    eval_sourceEquals hArithmeticReduct,
    eval_sourceAdd hArithmeticReduct,
    FirstOrder.Semiterm.val_bShift,
    (QuantifierBoundedCode.defined ℒₒᵣ (V := M)).iff,
    lh_defined.iff, qqAlls_defined.iff]
  constructor
  · intro h m b free base hbounded hbody hbase hlen
    exact h m b free base hbounded
      (fun base' hbase' hlen' ↦ hbody base' hbase' hlen'.symm) hbase hlen
  · intro h m b free base hbounded hbody hbase hlen
    exact h m b free base hbounded
      (fun base' hbase' hlen' ↦ hbody base' hbase' hlen'.symm) hbase hlen

end Semantics

/-! ## The fixed source derivation -/

set_option maxHeartbeats 1600000 in
/-- The complete semantic argument is compiled once, for the fixed source
language.  Completeness is applied only after quotienting the placeholder by
the explicit congruence antecedent; in the resulting canonical model the
source arithmetic reduct is the standard arithmetic structure, so the two
packed induction axioms really deliver the model-induction interfaces used by
dynamic PA-axiom soundness. -/
noncomputable def sourceCongruentAxiomSoundnessStepProof :
    parameterTemplatePeano 3 2 ⊢!
      sourceCongruentAxiomSoundnessStepSentence := by
  simpa [sourceCongruentAxiomSoundnessStepSentence] using
    (complete_underPlaceholderCongruence
      sourceAxiomSoundnessStepSentence
      (fun X ↦ by
        intro _ _ _ _
        have hArithmeticReduct :=
          DynamicTruthTemplateSemantics.arithmeticReduct_eq_standardModel
            (M := X)
        have hArithmeticPA : X↓[ℒₒᵣ] ⊧* Peano := by
          constructor
          intro sigma hsigma
          rw [← hArithmeticReduct]
          exact Semiformula.models_lMap.mp <|
            (inferInstance : X↓[L] ⊧*
              parameterTemplatePeano 3 2).models _
                ⟨sigma, hsigma, rfl⟩
        letI : X↓[ℒₒᵣ] ⊧* Peano := hArithmeticPA
        letI : X↓[ℒₒᵣ] ⊧* ISigma 1 :=
          models_of_subtheory hArithmeticPA
        simp [models_iff, sourceAxiomSoundnessStepSentence,
          sourceAxiomSoundnessLawContext,
          sourceFreeIndependencePredicate, sourceClosurePredicate,
          eval_sourceLevelAdjacency hArithmeticReduct,
          eval_sourceInductionAxiom hArithmeticReduct,
          eval_sourceFreeIndependenceAt hArithmeticReduct,
          eval_sourceClosureAt hArithmeticReduct,
          DynamicTruthLowerExistentialInterface.eval_sourceLowerExistentialLawsSentence
            hArithmeticReduct,
          DynamicTruthCertificateSemantics.eval_sourceCrossLevelSentence
            hArithmeticReduct,
          DynamicTruthCertificateSemantics.eval_sourceShiftInvariantSentence
            hArithmeticReduct,
          DynamicTruthCertificateSemantics.eval_sourceSubstitutionInvariantSentence
            hArithmeticReduct,
          DynamicTruthCertificateSemantics.eval_sourceAxiomSoundnessSentence
            hArithmeticReduct,
          DynamicTruthSemanticInductionSource.eval_sourceSemanticInductionSentence
            hArithmeticReduct]
        intro hnext hlowerExs hcross hshift hsubstitution hsemanticInduction
          hinductionFree hinductionClosure
        have laws := nextTruth_laws_of_lower_exs
          hnext hcross hlowerExs hshift hsubstitution
        have hfreeIndependent :
            FreeEnvironmentIndependence
              (DynamicTruthTemplateSemantics.level 0)
              (SuccessorTruth lowerRelation
                (DynamicTruthTemplateSemantics.level 0)
                (DynamicTruthTemplateSemantics.level 1)) :=
          freeEnvironmentIndependence_of_invariant
            (hinductionFree freeIndependenceInvariant_zero
              (fun _ ih ↦ freeIndependenceInvariant_succ hshift ih))
        have hclosure :
            UniversalClosureIntroduction
              (DynamicTruthTemplateSemantics.level 0)
              (SuccessorTruth lowerRelation
                (DynamicTruthTemplateSemantics.level 0)
                (DynamicTruthTemplateSemantics.level 1)) :=
          universalClosureIntroduction_of_invariant
            (hinductionClosure closureInvariant_zero
              (fun _ ih ↦ closureInvariant_succ laws ih))
        intro p hp hbounded free hfree
        exact successorTruth_of_mem_pa_delta1Class laws hsubstitution
          hsemanticInduction hfreeIndependent hclosure hp
          (OrientedHierarchy.quantifierBoundedCode_iff_sigma_or_pi.mpr
            hbounded)
          hfree))

end LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessStrongStepSource
