import BoundedPAConsistency.DynamicTruthCrossLevelDerivedStrongStepSource
import BoundedPAConsistency.ModelCodedTwoPredicateEqualityQuotient
import BoundedPAConsistency.FinFunext

/-!
# Congruence-safe derived-level cross-level strong step

The two truth predicates in the fixed source language are opaque relation
symbols.  Lifted PA does not by itself say that those symbols respect the
source equality relation, so completeness cannot soundly identify source
equality with Lean equality in an arbitrary expanded prestructure.

This module keeps the two missing `relExt` axioms visible as one antecedent.
`complete_underPlaceholderCongruence` quotients an arbitrary model by its
interpreted equality and then replaces it by an elementarily equivalent
canonical model.  Only in that canonical model do we apply the semantic
constructor theorem.  The production specialization must subsequently
discharge the two congruence instances for the represented truth formulas.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelDerivedStrongStep

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.OrientedHierarchy
open LeanProofs.BoundedPAConsistency.QuantifierFreeTruth
open LeanProofs.BoundedPAConsistency.FixedLevelTruth
open LeanProofs.BoundedPAConsistency.FixedLevelTruthCertificate
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceTemplate
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceSuccessor
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelStrongStepSource
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelDerivedStrongStepSource
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateTemplate
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters
open LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateParameters
open LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateEqualityQuotient
open LeanProofs.BoundedPAConsistency.TwoPredicateSourceContextInductionKernel

/-- A local unambiguous name for the two-predicate source language.  Several
imported template namespaces also export a declaration named
`SourceLanguage`, so using the short name here can make Lean elaborate
semantic helper statements against the wrong expanded language. -/
abbrev CrossLevelSourceLanguage :=
  DynamicTruthCrossLevelSourceTemplate.SourceLanguage

/-! ## Canonical arithmetic reduct -/

/-- The quotient callback supplies a canonical expanded `ORing` structure.
Its arithmetic summand is therefore the standard arithmetic structure on
the same carrier.  We record the equation explicitly because the PA model
transport below is through the language map, not through typeclass
conversion. -/
theorem sourceArithmeticReduct_eq_standardModel
    {X : Type*} [ORingStructure X]
    [sourceStructure : Structure CrossLevelSourceLanguage X]
    [Structure.ORing CrossLevelSourceLanguage X] :
    sourceStructure.lMap (arithmeticHom 3 3 3) =
      LO.FirstOrder.Arithmetic.standardModel X := by
  letI : Structure ℒₒᵣ X :=
    sourceStructure.lMap (arithmeticHom 3 3 3)
  letI : Structure.ORing ℒₒᵣ X := {
    zero := by
      calc
        (@Semiterm.Operator.Zero.zero ℒₒᵣ _).val ![] =
            (@Semiterm.Operator.Zero.zero CrossLevelSourceLanguage _).val ![] := by
          simp only [Semiterm.Operator.val,
            Semiterm.Operator.Zero.term_eq, Semiterm.val_func]
          congr 1
          funext i
          exact i.elim0
        _ = (0 : X) :=
          Structure.Zero.zero (L := CrossLevelSourceLanguage) (M := X)
    one := by
      calc
        (@Semiterm.Operator.One.one ℒₒᵣ _).val ![] =
            (@Semiterm.Operator.One.one CrossLevelSourceLanguage _).val ![] := by
          simp only [Semiterm.Operator.val,
            Semiterm.Operator.One.term_eq, Semiterm.val_func]
          congr 1
          funext i
          exact i.elim0
        _ = (1 : X) :=
          Structure.One.one (L := CrossLevelSourceLanguage) (M := X)
    add := by
      intro a b
      change Structure.func (L := CrossLevelSourceLanguage)
        (Sum.inl Language.Add.add) ![a, b] = a + b
      exact Structure.Add.add (L := CrossLevelSourceLanguage) (M := X) a b
    mul := by
      intro a b
      change Structure.func (L := CrossLevelSourceLanguage)
        (Sum.inl Language.Mul.mul) ![a, b] = a * b
      exact Structure.Mul.mul (L := CrossLevelSourceLanguage) (M := X) a b
    eq := by
      intro a b
      change Structure.rel (L := CrossLevelSourceLanguage)
        (Sum.inl Language.Eq.eq) ![a, b] ↔ a = b
      exact Structure.Eq.eq (L := CrossLevelSourceLanguage) (M := X) a b
    lt := by
      intro a b
      change Structure.rel (L := CrossLevelSourceLanguage)
        (Sum.inl Language.LT.lt) ![a, b] ↔ a < b
      exact Structure.LT.lt (L := CrossLevelSourceLanguage) (M := X) a b
  }
  exact LO.FirstOrder.Arithmetic.standardModel_unique X
    (sourceStructure.lMap (arithmeticHom 3 3 3))

/-- Evaluation of an arithmetical formula lifted into the two-predicate
source language.  Keeping this as a rewrite lemma avoids expanding the
mapped formula before the arithmetic-reduct equation can be used. -/
@[simp] theorem eval_liftArithmeticFormula
    {X : Type*} [ORingStructure X]
    [sourceStructure : Structure CrossLevelSourceLanguage X]
    (hArithmeticReduct :
      sourceStructure.lMap (arithmeticHom 3 3 3) =
        LO.FirstOrder.Arithmetic.standardModel X)
    (p : ArithmeticSemisentence n) (v : Fin n → X) :
    (liftArithmeticFormula p).Evalb (M := X) v ↔
      p.Evalb (M := X) v := by
  rw [liftArithmeticFormula, Semiformula.eval_lMap]
  exact iff_of_eq <| congrArg
    (fun s : Structure ℒₒᵣ X ↦
      Semiformula.Eval (s := s) v Empty.elim p)
    hArithmeticReduct

/-! ## Focused source semantics -/

section SourceSemantics

variable {X : Type*}
variable [sourceStructure : Structure CrossLevelSourceLanguage X]
variable [Nonempty X] [ORingStructure X]
variable [Structure.ORing CrossLevelSourceLanguage X]
variable [hPA : X↓[ℒₒᵣ] ⊧* Peano]

local instance : X↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-- Interpretation of the predecessor placeholder. -/
private def sourcePredecessorRelation (bound free p : X) : Prop :=
  Structure.rel (L := CrossLevelSourceLanguage)
    (Sum.inr (Sum.inl PlaceholderRel.predicate)) ![bound, free, p]

/-- Interpretation of the current placeholder. -/
def sourceCurrentRelation (bound free p : X) : Prop :=
  Structure.rel (L := CrossLevelSourceLanguage)
    (Sum.inr (Sum.inr (Sum.inl PlaceholderRel.predicate))) ![bound, free, p]

/-- Interpretation of the sole named level used by the derived source. -/
private noncomputable def sourceOldLevel : X :=
  Structure.func (L := CrossLevelSourceLanguage)
    (Sum.inr (Sum.inr (Sum.inr (ParameterFunc.parameter 0)))) ![]

variable (hArithmeticReduct :
  sourceStructure.lMap (arithmeticHom 3 3 3) =
    LO.FirstOrder.Arithmetic.standardModel X)

include hArithmeticReduct in
/-- Arithmetic function laws for the literal arithmetic summand are read
from the reduct equation, rather than from a potentially different
`Operator.Add` route through the expanded-language typeclass hierarchy. -/
private theorem source_one_eq :
    Structure.func (L := CrossLevelSourceLanguage) (M := X)
      (Sum.inl Language.One.one) ![] = (1 : X) := by
  have h := congrArg
    (fun s : Structure ℒₒᵣ X ↦
      @Structure.func ℒₒᵣ X s 0 Language.One.one ![])
    hArithmeticReduct
  simpa using h

include hArithmeticReduct in
private theorem source_add_eq (a b : X) :
    Structure.func (L := CrossLevelSourceLanguage) (M := X)
      (Sum.inl Language.Add.add) ![a, b] = a + b := by
  have h := congrArg
    (fun s : Structure ℒₒᵣ X ↦
      @Structure.func ℒₒᵣ X s 2 Language.Add.add ![a, b])
    hArithmeticReduct
  simpa using h

@[simp] private theorem eval_levelTerm_zero (v : Fin n → X) :
    (levelTerm (n := n) 0).valb (M := X) v = sourceOldLevel := by
  simp [levelTerm, namedParameterTerm, sourceOldLevel, Matrix.empty_eq]

include hArithmeticReduct in
@[simp] private theorem eval_sourceOne (v : Fin n → X) :
    (sourceOne : ClosedSemiterm CrossLevelSourceLanguage n).valb
        (M := X) v = 1 := by
  unfold sourceOne Semiterm.valb
  simp only [Semiterm.val_func]
  calc
    Structure.func (L := CrossLevelSourceLanguage) (M := X)
        (Sum.inl Language.One.one)
        (FirstOrder.Semiterm.val v Empty.elim ∘ ![]) =
      Structure.func (L := CrossLevelSourceLanguage) (M := X)
        (Sum.inl Language.One.one) ![] := by
          congr 1
          funext i
          exact i.elim0
    _ = 1 := source_one_eq hArithmeticReduct

include hArithmeticReduct in
@[simp] private theorem eval_sourceDerivedCurrentLevel (v : Fin n → X) :
    (sourceDerivedCurrentLevel : ClosedSemiterm CrossLevelSourceLanguage n).valb
        (M := X) v = sourceOldLevel + 1 := by
  calc
    _ = Structure.func (L := CrossLevelSourceLanguage) (M := X)
        (Sum.inl Language.Add.add)
        ![(levelTerm (n := n) 0).valb (M := X) v,
          (sourceOne : ClosedSemiterm CrossLevelSourceLanguage n).valb
            (M := X) v] := by
      simp [sourceDerivedCurrentLevel, Semiterm.valb,
        Semiterm.val_func, Matrix.fun_eq_vec_two]
    _ = (levelTerm (n := n) 0).valb (M := X) v +
        (sourceOne : ClosedSemiterm CrossLevelSourceLanguage n).valb
          (M := X) v := source_add_eq hArithmeticReduct _ _
    _ = sourceOldLevel + 1 := by
      rw [eval_levelTerm_zero, eval_sourceOne hArithmeticReduct]

include hArithmeticReduct in
@[simp] private theorem eval_sourceDerivedNextLevel (v : Fin n → X) :
    (sourceDerivedNextLevel : ClosedSemiterm CrossLevelSourceLanguage n).valb
        (M := X) v = sourceOldLevel + 1 + 1 := by
  calc
    _ = Structure.func (L := CrossLevelSourceLanguage) (M := X)
        (Sum.inl Language.Add.add)
        ![(sourceDerivedCurrentLevel :
              ClosedSemiterm CrossLevelSourceLanguage n).valb (M := X) v,
          (sourceOne : ClosedSemiterm CrossLevelSourceLanguage n).valb
            (M := X) v] := by
      simp [sourceDerivedNextLevel, Semiterm.valb,
        Semiterm.val_func, Matrix.fun_eq_vec_two]
    _ = (sourceDerivedCurrentLevel :
            ClosedSemiterm CrossLevelSourceLanguage n).valb (M := X) v +
        (sourceOne : ClosedSemiterm CrossLevelSourceLanguage n).valb
          (M := X) v := source_add_eq hArithmeticReduct _ _
    _ = sourceOldLevel + 1 + 1 := by
      rw [eval_sourceDerivedCurrentLevel hArithmeticReduct,
        eval_sourceOne hArithmeticReduct]

@[simp] theorem eval_apply₃
    (p : Semisentence CrossLevelSourceLanguage 3)
    (t₀ t₁ t₂ : ClosedSemiterm CrossLevelSourceLanguage n)
    (v : Fin n → X) :
    (DynamicTruthCrossLevelSourceTemplate.apply₃ p t₀ t₁ t₂).Evalb
        (M := X) v ↔
      p.Evalb (M := X)
        ![t₀.valb (M := X) v, t₁.valb (M := X) v,
          t₂.valb (M := X) v] := by
  simp [DynamicTruthCrossLevelSourceTemplate.apply₃,
    Semiformula.eval_substs, Function.comp_def]
  apply iff_of_eq
  congr 2
  exact funext_fin3 rfl rfl rfl

@[simp] theorem eval_apply₂
    (p : Semisentence CrossLevelSourceLanguage 2)
    (t₀ t₁ : ClosedSemiterm CrossLevelSourceLanguage n)
    (v : Fin n → X) :
    (DynamicTruthCrossLevelSourceTemplate.apply₂ p t₀ t₁).Evalb
        (M := X) v ↔
      p.Evalb (M := X)
        ![t₀.valb (M := X) v, t₁.valb (M := X) v] := by
  simp [DynamicTruthCrossLevelSourceTemplate.apply₂,
    Semiformula.eval_substs, Function.comp_def]
  apply iff_of_eq
  congr 2
  exact funext_fin2 rfl rfl

@[simp] private theorem eval_predecessorAtom
    (t₀ t₁ t₂ : ClosedSemiterm CrossLevelSourceLanguage n)
    (v : Fin n → X) :
    (predecessorAtom t₀ t₁ t₂).Evalb (M := X) v ↔
      sourcePredecessorRelation
        (t₀.valb (M := X) v) (t₁.valb (M := X) v)
        (t₂.valb (M := X) v) := by
  change Structure.rel _ (fun i ↦
      FirstOrder.Semiterm.val v Empty.elim (![t₀, t₁, t₂] i)) ↔
    Structure.rel _
      ![t₀.valb (M := X) v, t₁.valb (M := X) v,
        t₂.valb (M := X) v]
  apply iff_of_eq
  congr 1
  exact funext_fin3 rfl rfl rfl

@[simp] theorem eval_currentAtom
    (t₀ t₁ t₂ : ClosedSemiterm CrossLevelSourceLanguage n)
    (v : Fin n → X) :
    (currentAtom t₀ t₁ t₂).Evalb (M := X) v ↔
      sourceCurrentRelation
        (t₀.valb (M := X) v) (t₁.valb (M := X) v)
        (t₂.valb (M := X) v) := by
  change Structure.rel _ (fun i ↦
      FirstOrder.Semiterm.val v Empty.elim (![t₀, t₁, t₂] i)) ↔
    Structure.rel _
      ![t₀.valb (M := X) v, t₁.valb (M := X) v,
        t₂.valb (M := X) v]
  apply iff_of_eq
  congr 1
  exact funext_fin3 rfl rfl rfl

include hArithmeticReduct in
@[simp] private theorem eval_predecessorUniversalRecordBranch
    (v : Fin 3 → X) :
    sourcePredecessorUniversalRecordBranch.Evalb (M := X) v ↔
      ∃ q < recordFormula (v 2),
        recordFormula (v 2) = ^∀ q ∧
          LowerPiTrue sourcePredecessorRelation (v 0)
            (recordBound (v 2)) (recordFree (v 2))
            (recordFormula (v 2)) := by
  simp [sourcePredecessorUniversalRecordBranch,
    sourcePredecessorRelation, LowerPiTrue, UniversalRecordPrefix,
    eval_liftArithmeticFormula hArithmeticReduct,
    eval_predecessorAtom]
  aesop

include hArithmeticReduct in
@[simp] theorem eval_currentUniversalRecordBranch
    (v : Fin 3 → X) :
    sourceCurrentUniversalRecordBranch.Evalb (M := X) v ↔
      ∃ q < recordFormula (v 2),
        recordFormula (v 2) = ^∀ q ∧
          LowerPiTrue sourceCurrentRelation (v 0)
            (recordBound (v 2)) (recordFree (v 2))
            (recordFormula (v 2)) := by
  simp [sourceCurrentUniversalRecordBranch,
    sourceCurrentRelation, LowerPiTrue, UniversalRecordPrefix,
    eval_liftArithmeticFormula hArithmeticReduct,
    eval_currentAtom]
  aesop

include hArithmeticReduct in
@[simp] private theorem eval_derivedPredecessorSuccessorRecordValid
    (v : Fin 2 → X) :
    sourceDerivedPredecessorSuccessorRecordValid.Evalb (M := X) v ↔
      SigmaRecordValid sourcePredecessorRelation sourceOldLevel
        (sourceOldLevel + 1) (v 0) (v 1) := by
  simp [sourceDerivedPredecessorSuccessorRecordValid,
    sourceOldLevel,
    SigmaRecordValid, RecordDomain, PositiveRecordBranches,
    eval_liftArithmeticFormula hArithmeticReduct,
    eval_apply₃, eval_predecessorUniversalRecordBranch hArithmeticReduct]
  aesop

include hArithmeticReduct in
@[simp] private theorem eval_derivedCurrentSuccessorRecordValid
    (v : Fin 2 → X) :
    sourceDerivedCurrentSuccessorRecordValid.Evalb (M := X) v ↔
      SigmaRecordValid sourceCurrentRelation (sourceOldLevel + 1)
        (sourceOldLevel + 1 + 1) (v 0) (v 1) := by
  simp [sourceDerivedCurrentSuccessorRecordValid,
    sourceOldLevel,
    SigmaRecordValid, RecordDomain, PositiveRecordBranches,
    eval_liftArithmeticFormula hArithmeticReduct,
    eval_apply₃, eval_currentUniversalRecordBranch hArithmeticReduct]
  aesop

include hArithmeticReduct in
@[simp] private theorem eval_derivedPredecessorSuccessorTruth
    (v : Fin 3 → X) :
    sourceDerivedPredecessorSuccessorTruth.Evalb (M := X) v ↔
      SuccessorTruth sourcePredecessorRelation sourceOldLevel
        (sourceOldLevel + 1) (v 0) (v 1) (v 2) := by
  simp [sourceDerivedPredecessorSuccessorTruth, SuccessorTruth,
    eval_liftArithmeticFormula hArithmeticReduct,
    eval_apply₂,
    eval_derivedPredecessorSuccessorRecordValid hArithmeticReduct]

include hArithmeticReduct in
@[simp] private theorem eval_derivedCurrentSuccessorTruth
    (v : Fin 3 → X) :
    sourceDerivedCurrentSuccessorTruth.Evalb (M := X) v ↔
      SuccessorTruth sourceCurrentRelation (sourceOldLevel + 1)
        (sourceOldLevel + 1 + 1) (v 0) (v 1) (v 2) := by
  simp [sourceDerivedCurrentSuccessorTruth, SuccessorTruth,
    eval_liftArithmeticFormula hArithmeticReduct,
    eval_apply₂,
    eval_derivedCurrentSuccessorRecordValid hArithmeticReduct]

/- The closed prior field has exactly the semantic interface expected by the
constructor theorem.  This focused normalization is also where the
represented negation witness is put back into `(bound, free, neg q)` order. -/
include hArithmeticReduct in
@[simp] private theorem eval_sourcePriorCrossLevelContext :
    sourcePriorCrossLevelContext.Evalb (M := X) ![] ↔
      ∀ q : X,
        PriorCrossLaws sourcePredecessorRelation sourceCurrentRelation
          sourceOldLevel q := by
  simp [sourcePriorCrossLevelContext, sourcePriorCrossLevelPredicate,
    sourcePriorCrossLevelBody, sourcePriorSigmaDomain,
    sourcePriorPiDomain, sourcePredecessorPiTruth,
    sourcePredecessorRelation, sourceCurrentRelation, sourceOldLevel,
    PriorCrossLaws, LowerPiTrue,
    eval_liftArithmeticFormula hArithmeticReduct,
    eval_apply₂, eval_predecessorAtom, eval_currentAtom,
    DynamicTruthFormula.isSigmaCode_defined.iff,
    DynamicTruthFormula.isPiCode_defined.iff,
    neg.defined.iff, Semiformula.eval_rew, Function.comp_def]
  aesop

/- The explicit quantifier-free premise is the constructor theorem's atomic
introduction hypothesis for the successor of the current relation. -/
include hArithmeticReduct in
@[simp] private theorem eval_sourceDerivedTargetQuantifierFreeIntroduction :
    sourceDerivedTargetQuantifierFreeIntroduction.Evalb (M := X) ![] ↔
      ∀ bound free q : X,
        QFTrue bound free q →
          SuccessorTruth sourceCurrentRelation (sourceOldLevel + 1)
            (sourceOldLevel + 1 + 1) bound free q := by
  simp [sourceDerivedTargetQuantifierFreeIntroduction,
    sourceDerivedTargetQuantifierFreeIntroductionBody,
    sourceQuantifierFreeTruth,
    eval_liftArithmeticFormula hArithmeticReduct, eval_apply₃,
    eval_derivedCurrentSuccessorTruth hArithmeticReduct]
  aesop

/- The current placeholder is not arbitrary: the source premise defines it
as the successor truth relation constructed from the predecessor. -/
include hArithmeticReduct in
@[simp] private theorem eval_sourceDerivedCurrentDefinition :
    sourceDerivedCurrentDefinition.Evalb (M := X) ![] ↔
      ∀ bound free q : X,
        sourceCurrentRelation bound free q ↔
          SuccessorTruth sourcePredecessorRelation sourceOldLevel
            (sourceOldLevel + 1) bound free q := by
  simp [sourceDerivedCurrentDefinition,
    sourceDerivedCurrentDefinitionBody,
    eval_currentAtom,
    eval_derivedPredecessorSuccessorTruth hArithmeticReduct]
  aesop

/- Evaluation of one next-level invariant at a concrete code. -/
include hArithmeticReduct in
@[simp] private theorem eval_sourceDerivedNextCrossLevelInvariant (p : X) :
    sourceDerivedNextCrossLevelInvariant.Evalb (M := X) ![p] ↔
      SuccessorCrossLaws sourceCurrentRelation (sourceOldLevel + 1)
        (sourceOldLevel + 1 + 1) p := by
  simp [sourceDerivedNextCrossLevelInvariant,
    sourceDerivedNextCrossLevelBody,
    sourceDerivedCurrentSigmaDomain, sourceDerivedCurrentPiDomain,
    sourceDerivedCurrentPiTruth,
    sourceCurrentRelation, sourceOldLevel,
    SuccessorCrossLaws, LowerPiTrue,
    eval_liftArithmeticFormula hArithmeticReduct, eval_apply₂,
    eval_currentAtom,
    eval_sourceDerivedCurrentLevel hArithmeticReduct,
    eval_derivedCurrentSuccessorTruth hArithmeticReduct,
    DynamicTruthFormula.isSigmaCode_defined.iff,
    DynamicTruthFormula.isPiCode_defined.iff,
    neg.defined.iff, Semiformula.eval_rew, Function.comp_def]
  constructor
  · intro h bound free
    simpa only [] using h free bound
  · intro h free bound
    simpa only [] using h bound free

include hArithmeticReduct in
@[simp] private theorem eval_sourceDerivedNextCrossLevelInvariant'
    (v : Fin 1 → X) :
    sourceDerivedNextCrossLevelInvariant.Evalb (M := X) v ↔
      SuccessorCrossLaws sourceCurrentRelation (sourceOldLevel + 1)
        (sourceOldLevel + 1 + 1) (v 0) := by
  rw [Matrix.fun_eq_vec_one v]
  exact eval_sourceDerivedNextCrossLevelInvariant hArithmeticReduct (v 0)

include hArithmeticReduct in
@[simp] private theorem eval_sourceStrongPrefixGuard (v : Fin 2 → X) :
    sourceStrongPrefixGuard.Evalb (M := X) v ↔ v 0 < v 1 := by
  have hguard :
      sourceStrongPrefixGuard =
        liftArithmeticFormula
          (.rel Language.LT.lt
            ![(#0 : ClosedSemiterm ℒₒᵣ 2),
              (#1 : ClosedSemiterm ℒₒᵣ 2)]) := by
    simp [sourceStrongPrefixGuard, liftArithmeticFormula,
      Function.comp_def]
    exact funext_fin2 rfl rfl
  rw [hguard]
  rw [eval_liftArithmeticFormula hArithmeticReduct]
  simp

/- Evaluation of the represented strong-induction prefix. -/
include hArithmeticReduct in
@[simp] private theorem eval_sourceDerivedStrongPrefix (p : X) :
    sourceDerivedStrongPrefix.Evalb (M := X) ![p] ↔
      ∀ q : X, q < p →
        SuccessorCrossLaws sourceCurrentRelation (sourceOldLevel + 1)
          (sourceOldLevel + 1 + 1) q := by
  simp [sourceDerivedStrongPrefix, Semiformula.eval_substs,
    Function.comp_def,
    eval_sourceStrongPrefixGuard hArithmeticReduct,
    eval_sourceDerivedNextCrossLevelInvariant' hArithmeticReduct]

end SourceSemantics

/-! ## Explicit equality boundary -/

/-- The two coordinatewise congruence axioms omitted by lifted PA. -/
noncomputable def sourcePlaceholderCongruenceContext :
    Sentence CrossLevelSourceLanguage :=
  placeholderCongruenceContext 3 3 3

/-- The sound source obligation: the constructor step follows once both
opaque truth predicates respect interpreted equality. -/
noncomputable def sourceCongruentDerivedStrongStepSentence :
    Sentence CrossLevelSourceLanguage :=
  Arrow.arrow sourcePlaceholderCongruenceContext
    sourceDerivedStrongStepSentence

set_option maxHeartbeats 2000000 in
/-- Complete eight-constructor strong step, proved after equality quotienting.

The current and next hierarchy levels are literal successor terms in
`sourceDerivedStrongStepSentence`; consequently the two level equations
needed by `successorCrossLaws_strongStep` are reflexive in the canonical
model. -/
noncomputable def sourceCongruentDerivedStrongStepProof :
    twoPredicateParameterPeano 3 3 3 ⊢!
      sourceCongruentDerivedStrongStepSentence := by
  simpa [sourceCongruentDerivedStrongStepSentence,
    sourcePlaceholderCongruenceContext] using
    (complete_underPlaceholderCongruence
      sourceDerivedStrongStepSentence
      (fun X ↦ by
        intro _ _ _ _
        have hArithmeticReduct :=
          sourceArithmeticReduct_eq_standardModel (X := X)
        have hArithmeticPA : X↓[ℒₒᵣ] ⊧* Peano := by
          constructor
          intro sigma hsigma
          rw [← hArithmeticReduct]
          exact Semiformula.models_lMap.mp <|
            (inferInstance : X↓[CrossLevelSourceLanguage] ⊧*
              twoPredicateParameterPeano 3 3 3).models _
                ⟨sigma, hsigma, rfl⟩
        letI : X↓[ℒₒᵣ] ⊧* Peano := hArithmeticPA
        letI : X↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hArithmeticPA
        simp [models_iff, sourceDerivedStrongStepSentence]
        intro hpremises p hprefix
        have hpremises' := hpremises
        simp [sourceDerivedStrongStepPremises] at hpremises'
        exact
          (eval_sourceDerivedNextCrossLevelInvariant
            hArithmeticReduct p).mpr <|
            successorCrossLaws_strongStep rfl rfl
              ((eval_sourcePriorCrossLevelContext
                hArithmeticReduct).mp hpremises'.1.1)
              ((eval_sourceDerivedCurrentDefinition
                hArithmeticReduct).mp hpremises'.2)
              ((eval_sourceDerivedTargetQuantifierFreeIntroduction
                hArithmeticReduct).mp hpremises'.1.2)
              ((eval_sourceDerivedStrongPrefix
                hArithmeticReduct p).mp hprefix)))

end LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelDerivedStrongStep
