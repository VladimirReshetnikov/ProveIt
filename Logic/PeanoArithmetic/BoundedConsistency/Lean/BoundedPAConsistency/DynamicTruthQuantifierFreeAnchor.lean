import BoundedPAConsistency.DynamicTruthCompiledLocalBundle
import BoundedPAConsistency.DynamicTruthCrossLevelSourceSuccessor
import BoundedPAConsistency.FinFunext
import Foundation.FirstOrder.Completeness

/-!
# The quantifier-free anchor for a dynamic truth successor

The three compiled local laws are eliminators: they project an accepted
certificate, validate one of its members, and decode a universal leaf.  They
do not construct a certificate from a true quantifier-free leaf.  This module
isolates that missing positive constructor law and proves it from the fixed
source definition of `successorTruthFormula`.

We also give the typed formula corresponding exactly to the anchor exposed by
`DynamicTruthCrossLevelSourceSuccessor`.  The constructor law is kept
separate from the full biconditional: its reverse direction is the
quantifier-free soundness argument performed by structural formula induction,
whereas the positive direction is the genuinely missing local introduction
rule.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthQuantifierFreeAnchor

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.OrientedHierarchy
open LeanProofs.BoundedPAConsistency.QuantifierFreeTruth
open LeanProofs.BoundedPAConsistency.QuantifierFreeTarski
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthCompiledLocalBundle
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceSuccessor
open LeanProofs.BoundedPAConsistency.DynamicTruthTemplateFormula
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters
open LeanProofs.BoundedPAConsistency.FixedLevelTruth

/-! ## The arithmetic singleton-certificate fact -/

/-- Four-place ordinary application used to retain the original three truth
arguments while carrying the arbitrary upper level as a fourth variable. -/
noncomputable def arithmeticApply₄ {n : ℕ}
    (S : ArithmeticSemisentence 4)
    (t₀ t₁ t₂ t₃ : ClosedSemiterm ℒₒᵣ n) :
    ArithmeticSemisentence n :=
  S ⇜ ![t₀, t₁, t₂, t₃]

/-- Lower-independent successor certificate data.  Its four variables are
`(bound, free, formula, upperLevel)`.  Every member is required to satisfy
only the fixed record-domain and positive-branch predicates, so no predicate
placeholder occurs here. -/
noncomputable def arithmeticPositiveSuccessorTruthBody :
    ArithmeticSemisentence 4 :=
  DynamicTruthFormula.standardApply₃ qfTruthDef.val (#0) (#1) (#2) 🡒
    ∃⁰
      (arithmeticApply₄ hasTruthStateDef.val (#0) (#1) (#2) (#3) ⋏
        (∀⁰
          (DynamicTruthFormula.standardApply₂ hfsMemDef.val (#0) (#1) 🡒
            (DynamicTruthFormula.standardApply₃ recordDomainDef.val
                (#5) (#1) (#0) ⋏
              DynamicTruthFormula.standardApply₂
                positiveRecordBranchesDef.val (#1) (#0)))))

/-- PA proves uniformly in the arbitrary upper level that every true
quantifier-free formula has the lower-independent singleton certificate. -/
noncomputable def arithmeticPositiveSuccessorTruthSentence :
    ArithmeticSentence :=
  ∀⁰ ∀⁰ ∀⁰ ∀⁰ arithmeticPositiveSuccessorTruthBody

/-- The singleton-certificate construction in outer PA. -/
noncomputable def arithmeticPositiveSuccessorTruthProof :
    Peano ⊢! arithmeticPositiveSuccessorTruthSentence :=
  (LO.FirstOrder.Arithmetic.complete.{0} Peano _ <| by
    intro M _ hM
    letI : M↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hM
    simp [models_iff, arithmeticPositiveSuccessorTruthSentence,
      arithmeticPositiveSuccessorTruthBody,
      arithmeticApply₄,
      DynamicTruthFormula.standardApply₂,
      DynamicTruthFormula.standardApply₃]
    intro upperLevel p free bound hqf
    let r : M := truthRecord bound free p 0
    let C : M := insert r ∅
    have hr : r ∈ C := by simp [C]
    refine ⟨C, ⟨0, ?_, hr⟩, ?_⟩
    · simpa [r, truthRecord] using (lt_of_mem_rng hr)
    · intro r' hr'
      have hrr : r' = r := by simpa [C] using hr'
      subst r'
      have hqfCode := isQuantifierFreeCode_iff.mp hqf.1
      constructor
      · simp only [RecordDomain, r, recordFormula_truthRecord]
        exact ⟨hqfCode.1, by simp [hqfCode.2.1]⟩
      · exact Or.inl (by simpa [r] using hqf)).get

/-- Lift the arithmetic singleton-certificate theorem into the fixed source
language. -/
noncomputable def liftedArithmeticPositiveSuccessorTruthProof :
    parameterTemplatePeano 3 2 ⊢!
      arithmeticPositiveSuccessorTruthSentence.lMap
        (arithmeticHom 3 2) :=
  (Theory.Proof.small_complete <|
    lMap_models_lMap (Theory.Proof.sound
      (show Peano ⊢ arithmeticPositiveSuccessorTruthSentence from
        ⟨arithmeticPositiveSuccessorTruthProof⟩))).get

/-! ## The missing constructor-local source law -/

/-- Canonical quantifier-free truth in the one-predicate successor source
language. -/
noncomputable def sourceQuantifierFreeTruth :
    Semisentence DynamicTruthTemplateFormula.SourceLanguage 3 :=
  DynamicTruthTemplateFormula.apply₃
    (DynamicTruthTemplateFormula.liftArithmeticFormula qfTruthDef.val)
    (#0) (#1) (#2)

/-- The smallest missing positive law: a true quantifier-free leaf admits an
accepted successor certificate.  The arbitrary lower predicate and both
named hierarchy levels remain in the source language, but the construction
does not inspect the lower predicate. -/
noncomputable def sourceQuantifierFreeIntroductionBody :
    Semisentence DynamicTruthTemplateFormula.SourceLanguage 3 :=
  sourceQuantifierFreeTruth 🡒
    DynamicTruthTemplateFormula.successorTruthFormula

/-- Universal closure of quantifier-free leaf introduction. -/
noncomputable def sourceQuantifierFreeIntroductionSentence :
    Sentence DynamicTruthTemplateFormula.SourceLanguage :=
  ∀⁰ ∀⁰ ∀⁰ sourceQuantifierFreeIntroductionBody

/-- A fixed lifted-PA proof of quantifier-free leaf introduction. -/
noncomputable def sourceQuantifierFreeIntroductionProof :
    parameterTemplatePeano 3 2 ⊢!
      sourceQuantifierFreeIntroductionSentence :=
  (Theory.Proof.small_complete <| consequence_iff.mpr fun _ ↦ by
    intro ambient _structure hmodels
    have hpositive := models_of_provable hmodels
      (show parameterTemplatePeano 3 2 ⊢
          arithmeticPositiveSuccessorTruthSentence.lMap
            (arithmeticHom 3 2) from
        ⟨liftedArithmeticPositiveSuccessorTruthProof⟩)
    simp [models_iff, arithmeticPositiveSuccessorTruthSentence,
      arithmeticPositiveSuccessorTruthBody,
      arithmeticApply₄,
      DynamicTruthFormula.standardApply₂,
      DynamicTruthFormula.standardApply₃] at hpositive
    simp [models_iff, sourceQuantifierFreeIntroductionSentence,
      sourceQuantifierFreeIntroductionBody, sourceQuantifierFreeTruth,
      DynamicTruthTemplateFormula.successorTruthFormula,
      DynamicTruthTemplateFormula.successorRecordValid,
      DynamicTruthTemplateFormula.universalRecordBranch,
      DynamicTruthTemplateFormula.apply₂,
      DynamicTruthTemplateFormula.apply₃,
      DynamicTruthTemplateFormula.liftArithmeticFormula]
    intro p free bound hqf
    let upperLevel :=
      (parameterTerm (n := 0) (1 : Fin 2)).val
        (fun _ ↦ p) Empty.elim
    rcases hpositive upperLevel p free bound (by
      rw [Semiformula.eval_lMap, Semiformula.eval_rew]
      have h := Semiformula.eval_lMap.mp hqf
      have hb :
          (FirstOrder.Semiterm.val
              (s := _structure.lMap (arithmeticHom 3 2))
              ![bound, free, p, upperLevel] Empty.elim ∘
            (Rew.subst ![#0, #1, #2]) ∘
            FirstOrder.Semiterm.bvar) = ![bound, free, p] := by
        refine funext_fin3 ?_ ?_ ?_ <;> simp
      have hf :
          (FirstOrder.Semiterm.val
              (s := _structure.lMap (arithmeticHom 3 2))
              ![bound, free, p, upperLevel] Empty.elim ∘
            (Rew.subst ![#0, #1, #2]) ∘
            FirstOrder.Semiterm.fvar) = Empty.elim := by
        funext i
        exact Empty.elim i
      simpa only [hb, hf] using h) with
      ⟨C, hstate, hvalid⟩
    refine ⟨C, ?_, ?_⟩
    · rw [Semiformula.eval_lMap]
      have h := Semiformula.eval_lMap.mp hstate
      rw [Semiformula.eval_rew] at h
      have hb :
          (FirstOrder.Semiterm.val
              (s := _structure.lMap (arithmeticHom 3 2))
              ![C, bound, free, p, upperLevel] Empty.elim ∘
            (Rew.subst ![#0, #1, #2, #3]) ∘
            FirstOrder.Semiterm.bvar) = ![C, bound, free, p] := by
        refine funext_fin4 ?_ ?_ ?_ ?_ <;> simp
      have hf :
          (FirstOrder.Semiterm.val
              (s := _structure.lMap (arithmeticHom 3 2))
              ![C, bound, free, p, upperLevel] Empty.elim ∘
            (Rew.subst ![#0, #1, #2, #3]) ∘
            FirstOrder.Semiterm.fvar) = Empty.elim := by
        funext i
        exact Empty.elim i
      simpa only [hb, hf] using h
    intro r hr
    have hv := hvalid r (by
      rw [Semiformula.eval_lMap, Semiformula.eval_rew]
      have h := Semiformula.eval_lMap.mp hr
      have hb :
          (FirstOrder.Semiterm.val
              (s := _structure.lMap (arithmeticHom 3 2))
              ![r, C, bound, free, p, upperLevel] Empty.elim ∘
            (Rew.subst ![#0, #1]) ∘
            FirstOrder.Semiterm.bvar) = ![r, C] := by
        refine funext_fin2 ?_ ?_ <;> simp
      have hf :
          (FirstOrder.Semiterm.val
              (s := _structure.lMap (arithmeticHom 3 2))
              ![r, C, bound, free, p, upperLevel] Empty.elim ∘
            (Rew.subst ![#0, #1]) ∘
            FirstOrder.Semiterm.fvar) = Empty.elim := by
        funext i
        exact Empty.elim i
      simpa only [hb, hf] using h)
    constructor
    · rw [Semiformula.eval_lMap]
      have h := Semiformula.eval_lMap.mp hv.1
      rw [Semiformula.eval_rew] at h
      have hb :
          (FirstOrder.Semiterm.val
              (s := _structure.lMap (arithmeticHom 3 2))
              ![r, C, bound, free, p, upperLevel] Empty.elim ∘
            (Rew.subst ![#5, #1, #0]) ∘
            FirstOrder.Semiterm.bvar) =
              ![(parameterTerm (n := 2) (1 : Fin 2)).val
                  ![C, r] Empty.elim, C, r] := by
        refine funext_fin3 ?_ ?_ ?_
        · simp [upperLevel, parameterTerm]
        · simp
        · simp
      have hf :
          (FirstOrder.Semiterm.val
              (s := _structure.lMap (arithmeticHom 3 2))
              ![r, C, bound, free, p, upperLevel] Empty.elim ∘
            (Rew.subst ![#5, #1, #0]) ∘
            FirstOrder.Semiterm.fvar) = Empty.elim := by
        funext i
        exact Empty.elim i
      simpa only [hb, hf] using h
    · exact Or.inl (by
        rw [Semiformula.eval_lMap]
        have h := Semiformula.eval_lMap.mp hv.2
        rw [Semiformula.eval_rew] at h
        have hb :
            (FirstOrder.Semiterm.val
                (s := _structure.lMap (arithmeticHom 3 2))
                ![r, C, bound, free, p, upperLevel] Empty.elim ∘
              (Rew.subst ![#1, #0]) ∘
              FirstOrder.Semiterm.bvar) = ![C, r] := by
          refine funext_fin2 ?_ ?_ <;> simp
        have hf :
            (FirstOrder.Semiterm.val
                (s := _structure.lMap (arithmeticHom 3 2))
                ![r, C, bound, free, p, upperLevel] Empty.elim ∘
              (Rew.subst ![#1, #0]) ∘
              FirstOrder.Semiterm.fvar) = Empty.elim := by
          funext i
          exact Empty.elim i
        simpa only [hb, hf] using h)).get

/-! ## Exact typed specialization of the positive anchor -/

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- The canonical quantifier-free evaluator in typed arithmetic syntax. -/
noncomputable def quantifierFreeTruthFormula :
    Bootstrapping.Semiformula V ℒₒᵣ 3 :=
  (⌜qfTruthDef.val⌝ : Bootstrapping.Semiformula V ℒₒᵣ 3)

/-! ### The exact cross-level anchor syntax -/

/-- Typed counterpart of the zero-group code guard used by
`sourceMissingQuantifierFreeAnchor`. -/
noncomputable def crossLevelQuantifierFreeDomainFormula :
    Bootstrapping.Semiformula V ℒₒᵣ 3 :=
  (⌜(quantifierBoundedCodeDef ℒₒᵣ).val⌝ :
      Bootstrapping.Semiformula V ℒₒᵣ 2).subst
    ![Arithmetic.typedNumeral (0 : V),
      Semiterm.bvar (2 : Fin 3)]

/-- Typed body of the exact two-predicate source anchor. -/
noncomputable def crossLevelQuantifierFreeAnchorBodyFormula
    (current : Bootstrapping.Semiformula V ℒₒᵣ 3) :
    Bootstrapping.Semiformula V ℒₒᵣ 3 :=
  crossLevelQuantifierFreeDomainFormula 🡒
    (current 🡘 quantifierFreeTruthFormula)

/-- Typed universal closure of the exact anchor exposed by
`DynamicTruthCrossLevelSourceSuccessor`. -/
noncomputable def crossLevelQuantifierFreeAnchorFormula
    (current : Bootstrapping.Semiformula V ℒₒᵣ 3) :
    Bootstrapping.Formula V ℒₒᵣ :=
  ∀⁰ ∀⁰ ∀⁰ crossLevelQuantifierFreeAnchorBodyFormula current

/-- Translation of the source arithmetic zero used in the anchor guard. -/
@[simp] theorem translate_sourceArithmeticZero {n : ℕ}
    (levels : Fin 3 → V) :
    ModelCodedTwoPredicateParameters.translateTerm levels
        (Rew.emb
          (DynamicTruthCrossLevelSourceSuccessor.sourceArithmeticZero
            (n := n))) =
      Arithmetic.typedNumeral (0 : V) := by
  simp [DynamicTruthCrossLevelSourceSuccessor.sourceArithmeticZero]

/-- Exact specialization of the cross-level source guard. -/
@[simp] theorem translate_sourceQuantifierFreeDomain
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (levels : Fin 3 → V) :
    ModelCodedTwoPredicateParameters.translateFormula
        predecessor current levels
        (Rewriting.emb
          DynamicTruthCrossLevelSourceSuccessor.sourceQuantifierFreeDomain) =
      crossLevelQuantifierFreeDomainFormula := by
  simp [DynamicTruthCrossLevelSourceSuccessor.sourceQuantifierFreeDomain,
    crossLevelQuantifierFreeDomainFormula]
  congr 1

/-- Exact specialization of the canonical evaluator in the two-predicate
source language. -/
@[simp] theorem translate_crossLevelSourceQuantifierFreeTruth
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (levels : Fin 3 → V) :
    ModelCodedTwoPredicateParameters.translateFormula
        predecessor current levels
        (Rewriting.emb
          DynamicTruthCrossLevelSourceSuccessor.sourceQuantifierFreeTruth) =
      quantifierFreeTruthFormula := by
  simp only [
    DynamicTruthCrossLevelSourceSuccessor.sourceQuantifierFreeTruth,
    DynamicTruthCrossLevelSourceTemplate.translate_apply₃,
    DynamicTruthCrossLevelSourceTemplate.translate_liftArithmeticFormula,
    quantifierFreeTruthFormula]
  apply Bootstrapping.Semiformula.subst_eq_self
  intro i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
          cases i using Fin.cases with
          | zero => rfl
          | succ i => exact i.elim0

/-- The exact source anchor specializes to the typed guard and biconditional,
with the predecessor placeholder (correctly) absent from the result. -/
@[simp] theorem translate_sourceMissingQuantifierFreeAnchor
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (levels : Fin 3 → V) :
    ModelCodedTwoPredicateParameters.translateFormula
        predecessor current levels
        (Rewriting.emb
          DynamicTruthCrossLevelSourceSuccessor.sourceMissingQuantifierFreeAnchor) =
      crossLevelQuantifierFreeAnchorFormula current := by
  simp [DynamicTruthCrossLevelSourceSuccessor.sourceMissingQuantifierFreeAnchor,
    DynamicTruthCrossLevelSourceSuccessor.sourceMissingQuantifierFreeAnchorBody,
    crossLevelQuantifierFreeAnchorFormula,
    crossLevelQuantifierFreeAnchorBodyFormula,
    ModelCodedTwoPredicateParameters.translateFormula,
    Bootstrapping.Semiformula.imp_def,
    LogicalConnective.iff]
  have hcurrentSubst :
      current.subst
          ![Semiterm.bvar (0 : Fin 3), Semiterm.bvar (1 : Fin 3),
            Semiterm.bvar (2 : Fin 3)] = current := by
    apply Bootstrapping.Semiformula.subst_eq_self
    intro i
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
        cases i using Fin.cases with
        | zero => rfl
        | succ i =>
            cases i using Fin.cases with
            | zero => rfl
            | succ i => exact i.elim0
  have hdomain :
      ModelCodedTwoPredicateParameters.translateFormula
          predecessor current levels
          ((Rewriting.app Rew.emb)
            DynamicTruthCrossLevelSourceSuccessor.sourceQuantifierFreeDomain) =
        crossLevelQuantifierFreeDomainFormula := by
    change ModelCodedTwoPredicateParameters.translateFormula
        predecessor current levels
        (Rewriting.emb
          DynamicTruthCrossLevelSourceSuccessor.sourceQuantifierFreeDomain) = _
    exact translate_sourceQuantifierFreeDomain predecessor current levels
  have hcurrent :
      ModelCodedTwoPredicateParameters.translateFormula
          predecessor current levels
          ((Rewriting.app Rew.emb)
            (DynamicTruthCrossLevelSourceTemplate.currentAtom
              (#0) (#1) (#2))) = current := by
    change ModelCodedTwoPredicateParameters.translateFormula
        predecessor current levels
        (Rewriting.emb
          (DynamicTruthCrossLevelSourceTemplate.currentAtom
            (#0) (#1) (#2))) = _
    rw [DynamicTruthCrossLevelSourceTemplate.translate_currentAtom]
    simpa [ModelCodedTwoPredicateParameters.translateTerm] using
      hcurrentSubst
  have hqf :
      ModelCodedTwoPredicateParameters.translateFormula
          predecessor current levels
          ((Rewriting.app Rew.emb)
            DynamicTruthCrossLevelSourceSuccessor.sourceQuantifierFreeTruth) =
        quantifierFreeTruthFormula := by
    change ModelCodedTwoPredicateParameters.translateFormula
        predecessor current levels
        (Rewriting.emb
          DynamicTruthCrossLevelSourceSuccessor.sourceQuantifierFreeTruth) = _
    exact translate_crossLevelSourceQuantifierFreeTruth
      predecessor current levels
  constructor
  · calc
      _ = ∼ModelCodedTwoPredicateParameters.translateFormula
          predecessor current levels
          ((Rewriting.app Rew.emb)
            DynamicTruthCrossLevelSourceSuccessor.sourceQuantifierFreeDomain) := by
        simpa only [Semiformula.neg_eq] using
          (ModelCodedTwoPredicateParameters.translateFormula_neg
            predecessor current levels
            ((Rewriting.app Rew.emb)
              DynamicTruthCrossLevelSourceSuccessor.sourceQuantifierFreeDomain))
      _ = _ := congrArg (∼·) hdomain
  constructor
  · calc
      _ = ∼ModelCodedTwoPredicateParameters.translateFormula
          predecessor current levels
          ((Rewriting.app Rew.emb)
            (DynamicTruthCrossLevelSourceTemplate.currentAtom
              (#0) (#1) (#2))) := by
        simpa only [Semiformula.neg_eq] using
          (ModelCodedTwoPredicateParameters.translateFormula_neg
            predecessor current levels
            ((Rewriting.app Rew.emb)
              (DynamicTruthCrossLevelSourceTemplate.currentAtom
                (#0) (#1) (#2))))
      _ = _ := congrArg (∼·) hcurrent
  constructor
  · calc
      _ = ∼ModelCodedTwoPredicateParameters.translateFormula
          predecessor current levels
          ((Rewriting.app Rew.emb)
            DynamicTruthCrossLevelSourceSuccessor.sourceQuantifierFreeTruth) := by
        simpa only [Semiformula.neg_eq] using
          (ModelCodedTwoPredicateParameters.translateFormula_neg
            predecessor current levels
            ((Rewriting.app Rew.emb)
              DynamicTruthCrossLevelSourceSuccessor.sourceQuantifierFreeTruth))
      _ = _ := congrArg (∼·) hqf
  · simpa [ModelCodedTwoPredicateParameters.translateTerm] using
      hcurrentSubst

/-- The typed positive constructor law at arbitrary lower syntax and
arbitrary, possibly nonstandard, hierarchy levels. -/
noncomputable def quantifierFreeIntroductionFormula
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) : Bootstrapping.Formula V ℒₒᵣ :=
  ∀⁰ ∀⁰ ∀⁰
    (quantifierFreeTruthFormula 🡒
      DynamicTruthFormula.successorTruthFormula
        lower lowerLevel upperLevel)

/-- Specializing the fixed source sentence gives exactly the typed positive
quantifier-free constructor law. -/
@[simp] theorem translate_sourceQuantifierFreeIntroductionSentence
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    ModelCodedPredicateParameters.translateFormula
        lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceQuantifierFreeIntroductionSentence) =
      quantifierFreeIntroductionFormula lower lowerLevel upperLevel := by
  simp [sourceQuantifierFreeIntroductionSentence,
    sourceQuantifierFreeIntroductionBody,
    quantifierFreeIntroductionFormula, quantifierFreeTruthFormula,
    ModelCodedPredicateParameters.translateFormula,
    Bootstrapping.Semiformula.imp_def]
  calc
    _ = ∼ModelCodedPredicateParameters.translateFormula
        lower ![lowerLevel, upperLevel]
          ((Rewriting.app Rew.emb) sourceQuantifierFreeTruth) := by
      simpa only [Semiformula.neg_eq] using
        (ModelCodedPredicateParameters.translateFormula_neg
          lower ![lowerLevel, upperLevel]
          ((Rewriting.app Rew.emb) sourceQuantifierFreeTruth))
    _ = _ := by
      simp only [sourceQuantifierFreeTruth,
        DynamicTruthTemplateFormula.translate_apply₃,
        DynamicTruthTemplateFormula.translate_liftArithmeticFormula]
      congr 1
      apply Bootstrapping.Semiformula.subst_eq_self
      intro i
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
          cases i using Fin.cases with
          | zero => rfl
          | succ i =>
              cases i using Fin.cases with
              | zero => rfl
              | succ i => exact i.elim0

/-- Compile the fixed source proof at any model-coded lower predicate. -/
noncomputable def compiledQuantifierFreeIntroductionProof
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) (hlower : lower.shift = lower) :
    Peano.internalize V ⊢!
      quantifierFreeIntroductionFormula lower lowerLevel upperLevel := by
  simpa only [translate_sourceQuantifierFreeIntroductionSentence] using
    (compilePeanoTemplate lower ![lowerLevel, upperLevel] hlower
      sourceQuantifierFreeIntroductionProof)

set_option backward.isDefEq.respectTransparency false in
/-- Represented-proof form of the compiled positive anchor. -/
theorem compiledQuantifierFreeIntroductionProof_isPAProof
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) (hlower : lower.shift = lower) :
    Proof Peano
      (compiledQuantifierFreeIntroductionProof
        lower lowerLevel upperLevel hlower).val
      (quantifierFreeIntroductionFormula
        lower lowerLevel upperLevel).val := by
  simpa [Proof] using
    (compiledQuantifierFreeIntroductionProof
      lower lowerLevel upperLevel hlower).derivationOf

/-! ## Nonstandard-orbit instance -/

/-- The positive anchor with the consequent written literally as the next
member of the dynamic truth orbit. -/
noncomputable def orbitQuantifierFreeIntroductionFormula (n : V) :
    Bootstrapping.Formula V ℒₒᵣ :=
  ∀⁰ ∀⁰ ∀⁰
    (quantifierFreeTruthFormula 🡒 truthFormula (n + 1))

/-- PA proves the positive quantifier-free anchor at every model-coded orbit
index, including nonstandard indices. -/
noncomputable def orbitQuantifierFreeIntroductionProof (n : V) :
    Peano.internalize V ⊢! orbitQuantifierFreeIntroductionFormula n := by
  simpa only [orbitQuantifierFreeIntroductionFormula,
    quantifierFreeIntroductionFormula, truthFormula_succ] using
    (compiledQuantifierFreeIntroductionProof
      (truthFormula n) (n + 1) (n + 1 + 1) (truthFormula_shift n))

set_option backward.isDefEq.respectTransparency false in
/-- Represented-proof form of the orbit anchor. -/
theorem orbitQuantifierFreeIntroductionProof_isPAProof (n : V) :
    Proof Peano (orbitQuantifierFreeIntroductionProof n).val
      (orbitQuantifierFreeIntroductionFormula n).val := by
  simpa [Proof] using
    (orbitQuantifierFreeIntroductionProof n).derivationOf

/-! ## Minimal augmentation of the compiled local bundle -/

/-- The existing three eliminators together with the independently proved
quantifier-free constructor.  This definition lives here, rather than in the
production bundle, so downstream code can opt into the new law explicitly. -/
noncomputable def orbitCompiledLocalBundleWithQuantifierFreeIntroduction
    (n : V) : Bootstrapping.Formula V ℒₒᵣ :=
  orbitCompiledLocalBundle n ⋏ orbitQuantifierFreeIntroductionFormula n

/-- Exact proof-object assembly for the minimally augmented local bundle. -/
noncomputable def
    orbitCompiledLocalBundleWithQuantifierFreeIntroductionProof (n : V) :
    Peano.internalize V ⊢!
      orbitCompiledLocalBundleWithQuantifierFreeIntroduction n :=
  Entailment.K_intro (orbitCompiledLocalBundleProof n)
    (orbitQuantifierFreeIntroductionProof n)

set_option backward.isDefEq.respectTransparency false in
/-- Represented-proof form of the augmented bundle. -/
theorem orbitCompiledLocalBundleWithQuantifierFreeIntroductionProof_isPAProof
    (n : V) :
    Proof Peano
      (orbitCompiledLocalBundleWithQuantifierFreeIntroductionProof n).val
      (orbitCompiledLocalBundleWithQuantifierFreeIntroduction n).val := by
  simpa [Proof] using
    (orbitCompiledLocalBundleWithQuantifierFreeIntroductionProof n).derivationOf

/-! ### Representability of the augmented local field -/

set_option maxHeartbeats 800000 in
/-- The code of the positive quantifier-free constructor varies by a
Sigma-one graph.  Its only recursive input is the already represented orbit
formula at the successor index; the quantifier-free evaluator is fixed
syntax. -/
theorem orbitQuantifierFreeIntroductionFormulaCode_definable :
    HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ (orbitQuantifierFreeIntroductionFormula n).val) := by
  simp only [orbitQuantifierFreeIntroductionFormula,
    quantifierFreeTruthFormula, Semiformula.val_all,
    Semiformula.val_imp,
    LeanProofs.BoundedPAConsistency.DynamicTruthOrbit.truthFormula_val]
  definability

set_option maxHeartbeats 800000 in
/-- Consequently the complete four-law local field—three eliminators plus
the positive quantifier-free constructor—has a Sigma-one code graph suitable
for the recursive master-certificate family. -/
theorem
    orbitCompiledLocalBundleWithQuantifierFreeIntroductionCode_definable :
    HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦
        (orbitCompiledLocalBundleWithQuantifierFreeIntroduction n).val) := by
  letI : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ (orbitCompiledLocalBundle n).val) :=
    orbitCompiledLocalBundleCode_definable
  letI : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ (orbitQuantifierFreeIntroductionFormula n).val) :=
    orbitQuantifierFreeIntroductionFormulaCode_definable
  simp only [orbitCompiledLocalBundleWithQuantifierFreeIntroduction,
    Semiformula.val_and]
  definability

end LeanProofs.BoundedPAConsistency.DynamicTruthQuantifierFreeAnchor
