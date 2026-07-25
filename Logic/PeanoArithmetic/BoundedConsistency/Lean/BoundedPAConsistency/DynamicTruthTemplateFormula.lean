import BoundedPAConsistency.DynamicTruthFormula
import BoundedPAConsistency.ModelCodedPredicateParameters
import BoundedPAConsistency.FinFunext

/-!
# A source template for the dynamic truth-formula successor

The parameterized proof compiler works with ordinary proofs over a fixed
standard language.  This module spells the dynamic successor truth formula in
that source language: its lower truth predicate is the ternary placeholder,
and its lower/upper hierarchy levels are the two named constants.  The main
theorem proves that specialization is *syntactically equal* to
`DynamicTruthFormula.successorTruthFormula` for arbitrary model-coded lower
syntax and arbitrary (possibly nonstandard) model levels.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthTemplateFormula

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.FixedLevelTruth
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateTemplate
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters

/-- The fixed source language: a ternary predicate and two named constants. -/
abbrev SourceLanguage := parameterTemplateLanguage 3 2

/-- A named constant as a closed source term. -/
def parameterTerm (i : Fin 2) {n : ℕ} :
    ClosedSemiterm SourceLanguage n :=
  .func (Sum.inr (Sum.inr (.parameter i))) ![]

/-- Lift a fixed arithmetic formula into the source language. -/
noncomputable def liftArithmeticFormula {n : ℕ}
    (p : ArithmeticSemisentence n) : Semisentence SourceLanguage n :=
  p.lMap (arithmeticHom 3 2)

/-- Apply a closed source ternary formula to three closed source terms. -/
noncomputable def apply₃ {n : ℕ}
    (p : Semisentence SourceLanguage 3)
    (t₀ t₁ t₂ : ClosedSemiterm SourceLanguage n) :
    Semisentence SourceLanguage n :=
  p ⇜ ![t₀, t₁, t₂]

/-- Binary counterpart of `apply₃`. -/
noncomputable def apply₂ {n : ℕ}
    (p : Semisentence SourceLanguage 2)
    (t₀ t₁ : ClosedSemiterm SourceLanguage n) :
    Semisentence SourceLanguage n :=
  p ⇜ ![t₀, t₁]

/-- Apply the ternary lower-truth placeholder. -/
def lowerAtom {n : ℕ}
    (t₀ t₁ t₂ : ClosedSemiterm SourceLanguage n) :
    Semisentence SourceLanguage n :=
  .rel (Sum.inr (Sum.inl PlaceholderRel.predicate)) ![t₀, t₁, t₂]

/-- The universal-record branch with its call to the lower predicate left as
the source placeholder. -/
noncomputable def universalRecordBranch :
    Semisentence SourceLanguage 3 :=
  ∃⁰ ∃⁰ ∃⁰ ∃⁰ ∃⁰
    (liftArithmeticFormula universalRecordPrefixDef.val ⋏
      ∼(lowerAtom (#4) (#3) (#0)))

/-- Source formula for validity of one record.  Constant zero is the lower
level and constant one is the upper level. -/
noncomputable def successorRecordValid :
    Semisentence SourceLanguage 2 :=
  apply₃ (liftArithmeticFormula recordDomainDef.val)
      (parameterTerm 1) (#0) (#1) ⋏
    (liftArithmeticFormula positiveRecordBranchesDef.val ⋎
      apply₃ universalRecordBranch (parameterTerm 0) (#0) (#1))

/-- The complete fixed source formula for a successor partial-truth
predicate. -/
noncomputable def successorTruthFormula :
    Semisentence SourceLanguage 3 :=
  ∃⁰
    (liftArithmeticFormula hasTruthStateDef.val ⋏
      (∀⁰
        (apply₂ (liftArithmeticFormula hfsMemDef.val) (#0) (#1) 🡒
          apply₂ successorRecordValid (#1) (#0))))

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

@[simp] theorem translate_parameterTerm
    (parameters : Fin 2 → V) (i : Fin 2) :
    ModelCodedPredicateParameters.translateTerm parameters
        (Rew.emb (parameterTerm (n := n) i) :
          SyntacticSemiterm SourceLanguage n) =
      Arithmetic.typedNumeral (parameters i) := by
  rfl

@[simp] theorem translate_liftArithmeticFormula
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 2 → V)
    (p : ArithmeticSemisentence n) :
    ModelCodedPredicateParameters.translateFormula lower parameters
        (Rewriting.emb (liftArithmeticFormula p)) =
      (⌜p⌝ : Bootstrapping.Semiformula V ℒₒᵣ n) := by
  unfold liftArithmeticFormula
  rw [← FirstOrder.Semiformula.lMap_emb]
  simpa [Sentence.typed_quote_def] using
    (ModelCodedPredicateParameters.translateFormula_lMap_arithmetic
      lower parameters (Rewriting.emb p : ArithmeticSemiproposition n))

@[simp] theorem translate_apply₃
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 2 → V)
    (p : Semisentence SourceLanguage 3)
    (t₀ t₁ t₂ : ClosedSemiterm SourceLanguage n) :
    ModelCodedPredicateParameters.translateFormula lower parameters
        (Rewriting.emb (apply₃ p t₀ t₁ t₂)) =
      (ModelCodedPredicateParameters.translateFormula lower parameters
        (Rewriting.emb p)).subst
          ![ModelCodedPredicateParameters.translateTerm parameters
              (Rew.emb t₀ : SyntacticSemiterm SourceLanguage n),
            ModelCodedPredicateParameters.translateTerm parameters
              (Rew.emb t₁ : SyntacticSemiterm SourceLanguage n),
            ModelCodedPredicateParameters.translateTerm parameters
              (Rew.emb t₂ : SyntacticSemiterm SourceLanguage n)] := by
  rw [apply₃, Semiformula.coe_subst_eq_subst_coe,
    ModelCodedPredicateParameters.translateFormula_subst]
  congr 1
  exact funext_fin3 rfl rfl rfl

@[simp] theorem translate_apply₂
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 2 → V)
    (p : Semisentence SourceLanguage 2)
    (t₀ t₁ : ClosedSemiterm SourceLanguage n) :
    ModelCodedPredicateParameters.translateFormula lower parameters
        (Rewriting.emb (apply₂ p t₀ t₁)) =
      (ModelCodedPredicateParameters.translateFormula lower parameters
        (Rewriting.emb p)).subst
          ![ModelCodedPredicateParameters.translateTerm parameters
              (Rew.emb t₀ : SyntacticSemiterm SourceLanguage n),
            ModelCodedPredicateParameters.translateTerm parameters
              (Rew.emb t₁ : SyntacticSemiterm SourceLanguage n)] := by
  rw [apply₂, Semiformula.coe_subst_eq_subst_coe,
    ModelCodedPredicateParameters.translateFormula_subst]
  congr 1
  exact funext_fin2 rfl rfl

@[simp] theorem translate_neg_apply₂
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 2 → V)
    (p : Semisentence SourceLanguage 2)
    (t₀ t₁ : ClosedSemiterm SourceLanguage n) :
    ModelCodedPredicateParameters.translateFormula lower parameters
        (∼(Rewriting.emb (apply₂ p t₀ t₁))) =
      ∼((ModelCodedPredicateParameters.translateFormula lower parameters
          (Rewriting.emb p)).subst
        ![ModelCodedPredicateParameters.translateTerm parameters
            (Rew.emb t₀ : SyntacticSemiterm SourceLanguage n),
          ModelCodedPredicateParameters.translateTerm parameters
            (Rew.emb t₁ : SyntacticSemiterm SourceLanguage n)]) := by
  rw [ModelCodedPredicateParameters.translateFormula_neg,
    translate_apply₂]

@[simp] theorem translate_lowerAtom
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 2 → V)
    (t₀ t₁ t₂ : ClosedSemiterm SourceLanguage n) :
    ModelCodedPredicateParameters.translateFormula lower parameters
        (Rewriting.emb (lowerAtom t₀ t₁ t₂)) =
      lower.subst
        ![ModelCodedPredicateParameters.translateTerm parameters
            (Rew.emb t₀ : SyntacticSemiterm SourceLanguage n),
          ModelCodedPredicateParameters.translateTerm parameters
            (Rew.emb t₁ : SyntacticSemiterm SourceLanguage n),
          ModelCodedPredicateParameters.translateTerm parameters
            (Rew.emb t₂ : SyntacticSemiterm SourceLanguage n)] := by
  rfl

@[simp] theorem translate_imp
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 2 → V)
    (p q : Semiproposition SourceLanguage n) :
    ModelCodedPredicateParameters.translateFormula lower parameters
        (p 🡒 q) =
      (ModelCodedPredicateParameters.translateFormula lower parameters p 🡒
        ModelCodedPredicateParameters.translateFormula lower parameters q) := by
  change ModelCodedPredicateParameters.translateFormula lower parameters
      (∼p ⋎ q) =
    (∼ModelCodedPredicateParameters.translateFormula lower parameters p ⋎
      ModelCodedPredicateParameters.translateFormula lower parameters q)
  simp only [ModelCodedPredicateParameters.translateFormula]
  rw [ModelCodedPredicateParameters.translateFormula_neg]

@[simp] theorem translate_universalRecordBranch
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 2 → V) :
    ModelCodedPredicateParameters.translateFormula lower parameters
        (Rewriting.emb universalRecordBranch) =
      DynamicTruthFormula.universalRecordBranch lower := by
  simp [universalRecordBranch,
    ModelCodedPredicateParameters.translateFormula,
    ModelCodedPredicateParameters.translateTerm,
    DynamicTruthFormula.universalRecordBranch,
    DynamicTruthFormula.apply₃]

@[simp] theorem translate_successorRecordValid
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    ModelCodedPredicateParameters.translateFormula lower
        ![lowerLevel, upperLevel]
        (Rewriting.emb successorRecordValid) =
      DynamicTruthFormula.successorRecordValid
        lower lowerLevel upperLevel := by
  simp [successorRecordValid,
    ModelCodedPredicateParameters.translateFormula,
    ModelCodedPredicateParameters.translateTerm,
    DynamicTruthFormula.successorRecordValid]

/-- Specialization of the standard source template is exactly the dynamic
typed successor constructor.  No decoding or standardness assumption is
made about `lower`, `lowerLevel`, or `upperLevel`. -/
@[simp] theorem translate_successorTruthFormula
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb successorTruthFormula) =
      DynamicTruthFormula.successorTruthFormula
        lower lowerLevel upperLevel := by
  simp [successorTruthFormula,
    ModelCodedPredicateParameters.translateFormula,
    ModelCodedPredicateParameters.translateTerm,
    DynamicTruthFormula.successorTruthFormula,
    Bootstrapping.Semiformula.imp_def]
  let memberSource : Semisentence SourceLanguage 5 :=
    apply₂ (liftArithmeticFormula hfsMemDef.val) (#0) (#1)
  calc
    ModelCodedPredicateParameters.translateFormula lower
        ![lowerLevel, upperLevel] (∼(Rewriting.emb memberSource)) =
      ∼ModelCodedPredicateParameters.translateFormula lower
        ![lowerLevel, upperLevel] (Rewriting.emb memberSource) :=
      ModelCodedPredicateParameters.translateFormula_neg
        lower ![lowerLevel, upperLevel] (Rewriting.emb memberSource)
    _ = _ := by
      simp [memberSource,
        ModelCodedPredicateParameters.translateTerm]

end LeanProofs.BoundedPAConsistency.DynamicTruthTemplateFormula
