import BoundedPAConsistency.DynamicTruthAxiomSoundnessSemantic
import BoundedPAConsistency.DynamicTruthTemplateSemantics
import BoundedPAConsistency.FinFunext

/-!
# Fixed-source interface for semantic induction of dynamic truth

The semantic PA-axiom argument needs ordinary successor induction for the
predicate obtained by appending the induction variable to a coded bound
environment.  This module expresses that requirement as one closed sentence
in the common dynamic-truth source language.

Sequence extension is deliberately represented by `seqConsDef`; the source
syntax never treats the HFS constructor as an extra function symbol.  Thus
the sentence remains in arithmetic plus the one lower-truth placeholder and
the two named hierarchy levels.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthSemanticInductionSource

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessSemantic
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelStrongStepSource
open LeanProofs.BoundedPAConsistency.DynamicTruthTemplateFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthTemplateSemantics
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters

/-! ## Closed source syntax -/

/-- Simultaneously apply a four-variable source formula. -/
noncomputable def apply₄ {n : ℕ}
    (p : Semisentence SourceLanguage 4)
    (t₀ t₁ t₂ t₃ : ClosedSemiterm SourceLanguage n) :
    Semisentence SourceLanguage n :=
  p ⇜ ![t₀, t₁, t₂, t₃]

/-- Arithmetic zero in the expanded source language. -/
def sourceZero {n : ℕ} : ClosedSemiterm SourceLanguage n :=
  .func (Sum.inl (Language.Zero.zero : (ℒₒᵣ).Func 0)) ![]

/-- Arithmetic one in the expanded source language. -/
def sourceOne {n : ℕ} : ClosedSemiterm SourceLanguage n :=
  .func (Sum.inl (Language.One.one : (ℒₒᵣ).Func 0)) ![]

/-- The successor of an arbitrary source term. -/
def sourceSucc {n : ℕ} (t : ClosedSemiterm SourceLanguage n) :
    ClosedSemiterm SourceLanguage n :=
  .func (Sum.inl (Language.Add.add : (ℒₒᵣ).Func 2))
    ![t, sourceOne]

/-- Unary induction predicate with three parameters encoded as surrounding
bound variables.

The visible variables are ordered `(x, base, free, formula)`.  Beneath the
existential binder they become `(#1, #2, #3, #4)`, while `#0` is the graph
witness for `base ⁀' x`. -/
noncomputable def sourceExtendedTruthPredicate :
    Semisentence SourceLanguage 4 :=
  ∃⁰
    (apply₃ (liftArithmeticFormula seqConsDef.val) (#0) (#2) (#1) ⋏
      apply₃ DynamicTruthTemplateFormula.successorTruthFormula
        (#0) (#3) (#4))

/-- Apply the unary induction predicate while making its three fixed
parameters explicit. -/
noncomputable def sourceExtendedTruthAt {n : ℕ}
    (x base free formula : ClosedSemiterm SourceLanguage n) :
    Semisentence SourceLanguage n :=
  apply₄ sourceExtendedTruthPredicate x base free formula

/-- The induction implication for fixed `(base, free, formula)`.

At this arity those parameters are `#0`, `#1`, and `#2`.  Under either
universal quantifier the induction variable is `#0` and the parameters shift
to `#1`, `#2`, and `#3`. -/
noncomputable def sourceSemanticInductionBody :
    Semisentence SourceLanguage 3 :=
  Arrow.arrow
    (sourceExtendedTruthAt sourceZero (#0) (#1) (#2))
    (Arrow.arrow
      (∀⁰ Arrow.arrow
        (sourceExtendedTruthAt (#0) (#1) (#2) (#3))
        (sourceExtendedTruthAt (sourceSucc (#0)) (#1) (#2) (#3)))
      (∀⁰ sourceExtendedTruthAt (#0) (#1) (#2) (#3)))

/-- Closed assertion of semantic successor induction for every coded base
environment, free environment, and formula code. -/
noncomputable def sourceSemanticInductionSentence : Sentence SourceLanguage :=
  ∀⁰ ∀⁰ ∀⁰ sourceSemanticInductionBody

/-! ## Evaluation -/

variable {M : Type*}
variable [sourceStructure : Structure SourceLanguage M]
variable [Nonempty M] [ORingStructure M]
variable [hPA : M↓[ℒₒᵣ] ⊧* Peano]

local instance : M↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

variable (hArithmeticReduct :
  sourceStructure.lMap (arithmeticHom 3 2) =
    LO.FirstOrder.Arithmetic.standardModel M)

/-- Four-way simultaneous application has the expected environment. -/
@[simp] theorem eval_apply₄
    (p : Semisentence SourceLanguage 4)
    (t₀ t₁ t₂ t₃ : ClosedSemiterm SourceLanguage n)
    (v : Fin n → M) :
    (apply₄ p t₀ t₁ t₂ t₃).Evalb (M := M) v ↔
      p.Evalb (M := M)
        ![t₀.valb (M := M) v, t₁.valb (M := M) v,
          t₂.valb (M := M) v, t₃.valb (M := M) v] := by
  simp [apply₄, Semiformula.eval_substs, Function.comp_def]
  apply iff_of_eq
  congr 2
  exact funext_fin4 rfl rfl rfl rfl

include hArithmeticReduct in
/-- The represented graph witness is unique, so the source predicate reduces
to truth at the actual sequence extension. -/
@[simp] theorem eval_sourceExtendedTruthPredicate (v : Fin 4 → M) :
    sourceExtendedTruthPredicate.Evalb (M := M) v ↔
      SuccessorTruth lowerRelation (level 0) (level 1)
        (v 1 ⁀' v 0) (v 2) (v 3) := by
  simp [sourceExtendedTruthPredicate,
    eval_liftArithmeticFormula hArithmeticReduct,
    DynamicTruthTemplateSemantics.eval_apply₃,
    eval_successorTruthFormula hArithmeticReduct]

include hArithmeticReduct in
@[simp] theorem eval_sourceExtendedTruthAt
    (x base free formula : ClosedSemiterm SourceLanguage n)
    (v : Fin n → M) :
    (sourceExtendedTruthAt x base free formula).Evalb (M := M) v ↔
      SuccessorTruth lowerRelation (level 0) (level 1)
        (base.valb (M := M) v ⁀' x.valb (M := M) v)
        (free.valb (M := M) v) (formula.valb (M := M) v) := by
  simp [sourceExtendedTruthAt, eval_apply₄,
    eval_sourceExtendedTruthPredicate hArithmeticReduct]

/- These two small calculations use the reduct equation directly.  Merely
having an `ORingStructure M` does not force an arbitrary expanded source
structure to interpret its arithmetic summand canonically. -/
include hArithmeticReduct in
@[simp] theorem eval_sourceZero (v : Fin n → M) :
    sourceZero.valb (M := M) v = 0 := by
  have hzero := congrArg
    (fun s : Structure ℒₒᵣ M ↦
      @Structure.func ℒₒᵣ M s 0 Language.Zero.zero ![])
    hArithmeticReduct
  simpa [sourceZero] using hzero

include hArithmeticReduct in
@[simp] theorem eval_sourceOne (v : Fin n → M) :
    sourceOne.valb (M := M) v = 1 := by
  have hone := congrArg
    (fun s : Structure ℒₒᵣ M ↦
      @Structure.func ℒₒᵣ M s 0 Language.One.one ![])
    hArithmeticReduct
  simpa [sourceOne] using hone

include hArithmeticReduct in
@[simp] theorem eval_sourceSucc
    (t : ClosedSemiterm SourceLanguage n) (v : Fin n → M) :
    (sourceSucc t).valb (M := M) v = t.valb (M := M) v + 1 := by
  have hadd := congrArg
    (fun s : Structure ℒₒᵣ M ↦
      @Structure.func ℒₒᵣ M s 2 Language.Add.add
        ![t.valb (M := M) v, sourceOne.valb (M := M) v])
    hArithmeticReduct
  simpa [sourceSucc, eval_sourceOne hArithmeticReduct] using hadd

include hArithmeticReduct in
/-- Evaluation of the three-parameter body is exactly the corresponding
instance of semantic induction. -/
@[simp] theorem eval_sourceSemanticInductionBody (v : Fin 3 → M) :
    sourceSemanticInductionBody.Evalb (M := M) v ↔
      (SuccessorTruth lowerRelation (level 0) (level 1)
          (v 0 ⁀' 0) (v 1) (v 2) →
        (∀ x,
          SuccessorTruth lowerRelation (level 0) (level 1)
              (v 0 ⁀' x) (v 1) (v 2) →
            SuccessorTruth lowerRelation (level 0) (level 1)
              (v 0 ⁀' (x + 1)) (v 1) (v 2)) →
        ∀ x, SuccessorTruth lowerRelation (level 0) (level 1)
          (v 0 ⁀' x) (v 1) (v 2)) := by
  simp [sourceSemanticInductionBody,
    eval_sourceExtendedTruthAt hArithmeticReduct,
    eval_sourceZero hArithmeticReduct,
    eval_sourceSucc hArithmeticReduct]

include hArithmeticReduct in
/-- The closed fixed-source sentence realizes the first semantic interface
used by dynamic PA-axiom soundness. -/
theorem eval_sourceSemanticInductionSentence :
    sourceSemanticInductionSentence.Evalb (M := M) ![] ↔
      SemanticInduction
        (SuccessorTruth (M := M) lowerRelation (level 0) (level 1)) := by
  simp [sourceSemanticInductionSentence,
    SemanticInduction,
    eval_sourceSemanticInductionBody hArithmeticReduct]
  constructor
  · intro h base free formula
    exact h formula free base
  · intro h formula free base
    exact h

end LeanProofs.BoundedPAConsistency.DynamicTruthSemanticInductionSource
