import BoundedPAConsistency.DynamicTruthCrossLevelFormula
import BoundedPAConsistency.TwoPredicateSourceContextInductionKernel
import BoundedPAConsistency.FinFunext

/-!
# Structural source context for positive cross-level coherence

The positive cross-level step simultaneously mentions two arbitrary pieces of
model-coded syntax.  The first ternary predicate is the predecessor truth
predicate and the second is the current truth predicate.  Its source context
states the already established coherence law between those predicates.  Its
unary invariant states the next coherence law, between the current predicate
and the successor truth formula constructed from it.

This separation is important at a nonstandard orbit index: neither predicate
can be decoded into Lean syntax.  Both are therefore relation placeholders in
one fixed standard source language.  The three named constants are the old,
current, and next hierarchy levels.  The specialization theorems below are
literal formula equalities, so a later fixed PA proof may be compiled through
`TwoPredicateSourceContextInductionKernel` without a semantic cast or a
standardness assumption.

This module deliberately stops at the exact source interface.  Constructing
the zero and successor derivations required by `Template` entails the full
arithmetized structural-formula argument and is kept as the next proof layer.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceTemplate

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.FixedLevelTruth
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelFormula
open LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateParameters
open LeanProofs.BoundedPAConsistency.TwoPredicateSourceContextInductionKernel

/-! ## Fixed source syntax -/

/-- Two ternary relation placeholders and three named hierarchy levels. -/
abbrev SourceLanguage :=
  TwoPredicateSourceContextInductionKernel.Language 3 3 3

/-- A named source level: indices zero, one, and two denote the old, current,
and next levels, respectively. -/
def levelTerm (i : Fin 3) {n : ℕ} :
    ClosedSemiterm SourceLanguage n :=
  namedParameterTerm (arity₀ := 3) (arity₁ := 3) i

/-- Lift fixed arithmetic syntax into the two-predicate source language. -/
noncomputable def liftArithmeticFormula {n : ℕ}
    (p : ArithmeticSemisentence n) : Semisentence SourceLanguage n :=
  p.lMap (arithmeticHom 3 3 3)

/-- Apply a ternary closed source formula. -/
noncomputable def apply₃ {n : ℕ}
    (p : Semisentence SourceLanguage 3)
    (t₀ t₁ t₂ : ClosedSemiterm SourceLanguage n) :
    Semisentence SourceLanguage n :=
  p ⇜ ![t₀, t₁, t₂]

/-- Apply a binary closed source formula. -/
noncomputable def apply₂ {n : ℕ}
    (p : Semisentence SourceLanguage 2)
    (t₀ t₁ : ClosedSemiterm SourceLanguage n) :
    Semisentence SourceLanguage n :=
  p ⇜ ![t₀, t₁]

/-- Apply the predecessor truth placeholder. -/
def predecessorAtom {n : ℕ}
    (t₀ t₁ t₂ : ClosedSemiterm SourceLanguage n) :
    Semisentence SourceLanguage n :=
  firstAtom ![t₀, t₁, t₂]

/-- Apply the current truth placeholder. -/
def currentAtom {n : ℕ}
    (t₀ t₁ t₂ : ClosedSemiterm SourceLanguage n) :
    Semisentence SourceLanguage n :=
  secondAtom ![t₀, t₁, t₂]

/-! ### The prior coherence context -/

/-- Sigma domain at the old level (named constant zero). -/
noncomputable def sourcePriorSigmaDomain : Semisentence SourceLanguage 3 :=
  apply₂ (liftArithmeticFormula isSigmaCodeDef.val)
    (levelTerm 0) (#2)

/-- Pi domain at the old level. -/
noncomputable def sourcePriorPiDomain : Semisentence SourceLanguage 3 :=
  apply₂ (liftArithmeticFormula isPiCodeDef.val)
    (levelTerm 0) (#2)

/-- The predecessor's Pi presentation, using its Sigma presentation on the
explicitly represented negation code. -/
noncomputable def sourcePredecessorPiTruth :
    Semisentence SourceLanguage 3 :=
  sourcePriorPiDomain ⋏
    (∃⁰
      (liftArithmeticFormula
          ((negGraph ℒₒᵣ).val/[#0, #3]) ⋏
        ∼(predecessorAtom (#1) (#2) (#0))))

/-- One formula-code instance of the already established relation between
the current and predecessor truth predicates. -/
noncomputable def sourcePriorCrossLevelBody :
    Semisentence SourceLanguage 3 :=
  (sourcePriorSigmaDomain 🡒
      (currentAtom (#0) (#1) (#2) 🡘
        predecessorAtom (#0) (#1) (#2))) ⋏
    (sourcePriorPiDomain 🡒
      (currentAtom (#0) (#1) (#2) 🡘 sourcePredecessorPiTruth))

/-- The prior law for one formula code, universally quantified over the two
evaluation environments. -/
noncomputable def sourcePriorCrossLevelPredicate :
    Semisentence SourceLanguage 1 :=
  ∀⁰ ∀⁰ sourcePriorCrossLevelBody

/-- Closed structural context consumed by the positive induction step. -/
noncomputable def sourcePriorCrossLevelContext : Sentence SourceLanguage :=
  ∀⁰ sourcePriorCrossLevelPredicate

/-! ### The successor formula over the current placeholder -/

/-- Universal-record branch with the recursive call directed to the current
truth placeholder. -/
noncomputable def sourceCurrentUniversalRecordBranch :
    Semisentence SourceLanguage 3 :=
  ∃⁰ ∃⁰ ∃⁰ ∃⁰ ∃⁰
    (liftArithmeticFormula universalRecordPrefixDef.val ⋏
      ∼(currentAtom (#4) (#3) (#0)))

/-- Record validity for the successor of the current truth predicate. -/
noncomputable def sourceCurrentSuccessorRecordValid :
    Semisentence SourceLanguage 2 :=
  apply₃ (liftArithmeticFormula recordDomainDef.val)
      (levelTerm 2) (#0) (#1) ⋏
    (liftArithmeticFormula positiveRecordBranchesDef.val ⋎
      apply₃ sourceCurrentUniversalRecordBranch
        (levelTerm 1) (#0) (#1))

/-- The complete successor partial-truth predicate constructed from the
current placeholder at the current and next named levels. -/
noncomputable def sourceCurrentSuccessorTruth :
    Semisentence SourceLanguage 3 :=
  ∃⁰
    (liftArithmeticFormula hasTruthStateDef.val ⋏
      (∀⁰
        (apply₂ (liftArithmeticFormula hfsMemDef.val) (#0) (#1) 🡒
          apply₂ sourceCurrentSuccessorRecordValid (#1) (#0))))

/-! ### The next cross-level induction invariant -/

/-- Sigma domain at the current level (named constant one). -/
noncomputable def sourceCurrentSigmaDomain : Semisentence SourceLanguage 3 :=
  apply₂ (liftArithmeticFormula isSigmaCodeDef.val)
    (levelTerm 1) (#2)

/-- Pi domain at the current level. -/
noncomputable def sourceCurrentPiDomain : Semisentence SourceLanguage 3 :=
  apply₂ (liftArithmeticFormula isPiCodeDef.val)
    (levelTerm 1) (#2)

/-- The current predicate's Pi presentation. -/
noncomputable def sourceCurrentPiTruth : Semisentence SourceLanguage 3 :=
  sourceCurrentPiDomain ⋏
    (∃⁰
      (liftArithmeticFormula
          ((negGraph ℒₒᵣ).val/[#0, #3]) ⋏
        ∼(currentAtom (#1) (#2) (#0))))

/-- One formula-code instance of coherence between the current truth
predicate and the successor constructed from it. -/
noncomputable def sourceNextCrossLevelBody :
    Semisentence SourceLanguage 3 :=
  (sourceCurrentSigmaDomain 🡒
      (sourceCurrentSuccessorTruth 🡘
        currentAtom (#0) (#1) (#2))) ⋏
    (sourceCurrentPiDomain 🡒
      (sourceCurrentSuccessorTruth 🡘 sourceCurrentPiTruth))

/-- Unary source invariant expected by the structural induction kernel.  Its
free variable is the formula code; bound and free-variable environments are
universally quantified. -/
noncomputable def sourceNextCrossLevelInvariant :
    Semisentence SourceLanguage 1 :=
  ∀⁰ ∀⁰ sourceNextCrossLevelBody

/-! ## Exact specialization helpers -/

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

@[simp] theorem translate_levelTerm
    (levels : Fin 3 → V) (i : Fin 3) :
    translateTerm levels
        (Rew.emb (levelTerm (n := n) i) :
          SyntacticSemiterm SourceLanguage n) =
      Arithmetic.typedNumeral (levels i) := by
  simp [levelTerm]

/-- Applying a ternary typed formula to the three bound variables in their
native order is syntactically the identity. -/
@[simp] theorem subst_boundVariables₃
    (formula : Bootstrapping.Semiformula V ℒₒᵣ 3) :
    formula.subst
        ![Semiterm.bvar (0 : Fin 3), Semiterm.bvar (1 : Fin 3),
          Semiterm.bvar (2 : Fin 3)] =
      formula := by
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

@[simp] theorem translate_liftArithmeticFormula
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (levels : Fin 3 → V) (p : ArithmeticSemisentence n) :
    translateFormula predecessor current levels
        (Rewriting.emb (liftArithmeticFormula p)) =
      (⌜p⌝ : Bootstrapping.Semiformula V ℒₒᵣ n) := by
  unfold liftArithmeticFormula
  rw [← FirstOrder.Semiformula.lMap_emb]
  simpa [Sentence.typed_quote_def] using
    (translateFormula_lMap_arithmetic predecessor current levels
      (Rewriting.emb p : ArithmeticSemiproposition n))

@[simp] theorem translate_apply₃
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (levels : Fin 3 → V)
    (p : Semisentence SourceLanguage 3)
    (t₀ t₁ t₂ : ClosedSemiterm SourceLanguage n) :
    translateFormula predecessor current levels
        (Rewriting.emb (apply₃ p t₀ t₁ t₂)) =
      (translateFormula predecessor current levels
        (Rewriting.emb p)).subst
          ![translateTerm levels (Rew.emb t₀),
            translateTerm levels (Rew.emb t₁),
            translateTerm levels (Rew.emb t₂)] := by
  rw [apply₃, Semiformula.coe_subst_eq_subst_coe,
    translateFormula_subst]
  congr 1
  exact funext_fin3 rfl rfl rfl

@[simp] theorem translate_apply₂
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (levels : Fin 3 → V)
    (p : Semisentence SourceLanguage 2)
    (t₀ t₁ : ClosedSemiterm SourceLanguage n) :
    translateFormula predecessor current levels
        (Rewriting.emb (apply₂ p t₀ t₁)) =
      (translateFormula predecessor current levels
        (Rewriting.emb p)).subst
          ![translateTerm levels (Rew.emb t₀),
            translateTerm levels (Rew.emb t₁)] := by
  rw [apply₂, Semiformula.coe_subst_eq_subst_coe,
    translateFormula_subst]
  congr 1
  exact funext_fin2 rfl rfl

@[simp] theorem translate_predecessorAtom
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (levels : Fin 3 → V)
    (t₀ t₁ t₂ : ClosedSemiterm SourceLanguage n) :
    translateFormula predecessor current levels
        (Rewriting.emb (predecessorAtom t₀ t₁ t₂)) =
      predecessor.subst
        ![translateTerm levels (Rew.emb t₀),
          translateTerm levels (Rew.emb t₁),
          translateTerm levels (Rew.emb t₂)] := by
  rw [predecessorAtom, translateFormula_firstAtom]
  congr 1
  exact funext_fin3 rfl rfl rfl

@[simp] theorem translate_currentAtom
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (levels : Fin 3 → V)
    (t₀ t₁ t₂ : ClosedSemiterm SourceLanguage n) :
    translateFormula predecessor current levels
        (Rewriting.emb (currentAtom t₀ t₁ t₂)) =
      current.subst
        ![translateTerm levels (Rew.emb t₀),
          translateTerm levels (Rew.emb t₁),
          translateTerm levels (Rew.emb t₂)] := by
  rw [currentAtom, translateFormula_secondAtom]
  congr 1
  exact funext_fin3 rfl rfl rfl

/-! ## Typed prior context -/

/-- A direct cross-level body where both sides are supplied independently.
When `current` is the syntactic successor of `predecessor`, this is
definitionally the body from `DynamicTruthCrossLevelFormula`. -/
noncomputable def directCrossLevelBodyFormula
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (oldLevel : V) : Bootstrapping.Semiformula V ℒₒᵣ 3 :=
  (sigmaDomainFormula oldLevel 🡒 (current 🡘 predecessor)) ⋏
    (piDomainFormula oldLevel 🡒
      (current 🡘 lowerPiTruthFormula predecessor oldLevel))

/-- Universal closure of the direct prior-coherence body. -/
noncomputable def directCrossLevelFormula
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (oldLevel : V) : Bootstrapping.Formula V ℒₒᵣ :=
  ∀⁰ ∀⁰ ∀⁰
    directCrossLevelBodyFormula predecessor current oldLevel

@[simp] theorem translate_sourcePriorSigmaDomain
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (levels : Fin 3 → V) :
    translateFormula predecessor current levels
        (Rewriting.emb sourcePriorSigmaDomain) =
      sigmaDomainFormula (levels 0) := by
  simp [sourcePriorSigmaDomain, sigmaDomainFormula,
    ModelCodedTwoPredicateParameters.translateTerm]

@[simp] theorem translate_sourcePriorPiDomain
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (levels : Fin 3 → V) :
    translateFormula predecessor current levels
        (Rewriting.emb sourcePriorPiDomain) =
      piDomainFormula (levels 0) := by
  simp [sourcePriorPiDomain, piDomainFormula,
    ModelCodedTwoPredicateParameters.translateTerm]

@[simp] theorem translate_sourcePredecessorPiTruth
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (levels : Fin 3 → V) :
    translateFormula predecessor current levels
        (Rewriting.emb sourcePredecessorPiTruth) =
      lowerPiTruthFormula predecessor (levels 0) := by
  simp [sourcePredecessorPiTruth, lowerPiTruthFormula,
    translateFormula, translateTerm, DynamicTruthFormula.apply₃]

@[simp] theorem translate_sourcePriorCrossLevelBody
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (levels : Fin 3 → V) :
    translateFormula predecessor current levels
        (Rewriting.emb sourcePriorCrossLevelBody) =
      directCrossLevelBodyFormula predecessor current (levels 0) := by
  simp [sourcePriorCrossLevelBody, directCrossLevelBodyFormula,
    FirstOrder.Semiformula.iff_eq, translateFormula, translateTerm]
  constructor
  · have hsneg :
        translateFormula predecessor current levels
            (Semiformula.neg (Rewriting.emb sourcePriorSigmaDomain)) =
          ∼(sigmaDomainFormula (levels 0)) := by
      calc
        _ = ∼translateFormula predecessor current levels
            (Rewriting.emb sourcePriorSigmaDomain) := by
          simpa only [Semiformula.neg_eq] using
            (translateFormula_neg predecessor current levels
              (Rewriting.emb sourcePriorSigmaDomain))
        _ = _ := congrArg (∼·)
          (translate_sourcePriorSigmaDomain predecessor current levels)
    rw [hsneg]
    simp [Bootstrapping.Semiformula.imp_def, LogicalConnective.iff]
  · have hpneg :
        translateFormula predecessor current levels
            (Semiformula.neg (Rewriting.emb sourcePriorPiDomain)) =
          ∼(piDomainFormula (levels 0)) := by
      calc
        _ = ∼translateFormula predecessor current levels
            (Rewriting.emb sourcePriorPiDomain) := by
          simpa only [Semiformula.neg_eq] using
            (translateFormula_neg predecessor current levels
              (Rewriting.emb sourcePriorPiDomain))
        _ = _ := congrArg (∼·)
          (translate_sourcePriorPiDomain predecessor current levels)
    rw [hpneg]
    simp [Bootstrapping.Semiformula.imp_def, LogicalConnective.iff]

@[simp] theorem translate_sourcePriorCrossLevelContext
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (levels : Fin 3 → V) :
    translateFormula predecessor current levels
        (Rewriting.emb sourcePriorCrossLevelContext) =
      directCrossLevelFormula predecessor current (levels 0) := by
  simp [sourcePriorCrossLevelContext, sourcePriorCrossLevelPredicate,
    directCrossLevelFormula, translateFormula]

/-! ## Typed successor invariant -/

@[simp] theorem translate_sourceCurrentUniversalRecordBranch
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (levels : Fin 3 → V) :
    translateFormula predecessor current levels
        (Rewriting.emb sourceCurrentUniversalRecordBranch) =
      DynamicTruthFormula.universalRecordBranch current := by
  simp [sourceCurrentUniversalRecordBranch, translateFormula, translateTerm,
    DynamicTruthFormula.universalRecordBranch,
    DynamicTruthFormula.apply₃]

@[simp] theorem translate_sourceCurrentSuccessorRecordValid
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (levels : Fin 3 → V) :
    translateFormula predecessor current levels
        (Rewriting.emb sourceCurrentSuccessorRecordValid) =
      DynamicTruthFormula.successorRecordValid current
        (levels 1) (levels 2) := by
  simp [sourceCurrentSuccessorRecordValid, translateFormula, translateTerm,
    DynamicTruthFormula.successorRecordValid]

@[simp] theorem translate_sourceCurrentSuccessorTruth
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (levels : Fin 3 → V) :
    translateFormula predecessor current levels
        (Rewriting.emb sourceCurrentSuccessorTruth) =
      DynamicTruthFormula.successorTruthFormula current
        (levels 1) (levels 2) := by
  simp [sourceCurrentSuccessorTruth, translateFormula, translateTerm,
    DynamicTruthFormula.successorTruthFormula,
    Bootstrapping.Semiformula.imp_def]
  let memberSource : Semisentence SourceLanguage 5 :=
    apply₂ (liftArithmeticFormula hfsMemDef.val) (#0) (#1)
  calc
    translateFormula predecessor current levels
        (∼(Rewriting.emb memberSource)) =
      ∼translateFormula predecessor current levels
        (Rewriting.emb memberSource) :=
      translateFormula_neg predecessor current levels
        (Rewriting.emb memberSource)
    _ = _ := by simp [memberSource, translateTerm]

@[simp] theorem translate_sourceCurrentSigmaDomain
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (levels : Fin 3 → V) :
    translateFormula predecessor current levels
        (Rewriting.emb sourceCurrentSigmaDomain) =
      sigmaDomainFormula (levels 1) := by
  simp [sourceCurrentSigmaDomain, sigmaDomainFormula,
    ModelCodedTwoPredicateParameters.translateTerm]

@[simp] theorem translate_sourceCurrentPiDomain
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (levels : Fin 3 → V) :
    translateFormula predecessor current levels
        (Rewriting.emb sourceCurrentPiDomain) =
      piDomainFormula (levels 1) := by
  simp [sourceCurrentPiDomain, piDomainFormula,
    ModelCodedTwoPredicateParameters.translateTerm]

@[simp] theorem translate_sourceCurrentPiTruth
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (levels : Fin 3 → V) :
    translateFormula predecessor current levels
        (Rewriting.emb sourceCurrentPiTruth) =
      lowerPiTruthFormula current (levels 1) := by
  simp [sourceCurrentPiTruth, lowerPiTruthFormula,
    translateFormula, translateTerm, DynamicTruthFormula.apply₃]

@[simp] theorem translate_sourceNextCrossLevelBody
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (levels : Fin 3 → V) :
    translateFormula predecessor current levels
        (Rewriting.emb sourceNextCrossLevelBody) =
      crossLevelBodyFormula current (levels 1) (levels 2) := by
  simp [sourceNextCrossLevelBody, crossLevelBodyFormula,
    FirstOrder.Semiformula.iff_eq, translateFormula, translateTerm]
  constructor
  · have hsneg :
        translateFormula predecessor current levels
            (Semiformula.neg (Rewriting.emb sourceCurrentSigmaDomain)) =
          ∼(sigmaDomainFormula (levels 1)) := by
      calc
        _ = ∼translateFormula predecessor current levels
            (Rewriting.emb sourceCurrentSigmaDomain) := by
          simpa only [Semiformula.neg_eq] using
            (translateFormula_neg predecessor current levels
              (Rewriting.emb sourceCurrentSigmaDomain))
        _ = _ := congrArg (∼·)
          (translate_sourceCurrentSigmaDomain predecessor current levels)
    rw [hsneg]
    simp [Bootstrapping.Semiformula.imp_def, LogicalConnective.iff]
  · have hpneg :
        translateFormula predecessor current levels
            (Semiformula.neg (Rewriting.emb sourceCurrentPiDomain)) =
          ∼(piDomainFormula (levels 1)) := by
      calc
        _ = ∼translateFormula predecessor current levels
            (Rewriting.emb sourceCurrentPiDomain) := by
          simpa only [Semiformula.neg_eq] using
            (translateFormula_neg predecessor current levels
              (Rewriting.emb sourceCurrentPiDomain))
        _ = _ := congrArg (∼·)
          (translate_sourceCurrentPiDomain predecessor current levels)
    rw [hpneg]
    simp [Bootstrapping.Semiformula.imp_def, LogicalConnective.iff]

/-- The unary source invariant specializes exactly to the predicate expected
by the next cross-level `PAInductionKernel`. -/
@[simp] theorem translate_sourceNextCrossLevelInvariant
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (levels : Fin 3 → V) :
    translateFormula predecessor current levels
        (Rewriting.emb sourceNextCrossLevelInvariant) =
      crossLevelPredicateFormula current (levels 1) (levels 2) := by
  simp [sourceNextCrossLevelInvariant, crossLevelPredicateFormula,
    translateFormula]

/-- Universally closing the specialized unary invariant gives the complete
next cross-level field, exactly as required after `PAInductionKernel.compile`.
-/
@[simp] theorem translate_sourceNextCrossLevelInvariant_closure
    (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (levels : Fin 3 → V) :
    (∀⁰ translateFormula predecessor current levels
        (Rewriting.emb sourceNextCrossLevelInvariant)) =
      crossLevelFormula current (levels 1) (levels 2) := by
  rw [translate_sourceNextCrossLevelInvariant]
  rfl

/-! ## Alignment with the represented orbit -/

/-- Supplying the actual syntactic successor as `current` turns the direct
context into the existing cross-level field. -/
@[simp] theorem directCrossLevelFormula_successor
    (predecessor : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (oldLevel currentLevel : V) :
    directCrossLevelFormula predecessor
        (DynamicTruthFormula.successorTruthFormula predecessor
          oldLevel currentLevel)
        oldLevel =
      crossLevelFormula predecessor oldLevel currentLevel := by
  rfl

/-- The base structural context is literally the existing base cross-level
certificate field. -/
@[simp] theorem translate_sourcePriorCrossLevelContext_base :
    translateFormula (baseTruthFormula (V := V)) levelZeroTruthFormula
        ![(0 : V), (1 : V), (2 : V)]
        (Rewriting.emb sourcePriorCrossLevelContext) =
      baseCrossLevelFormula := by
  simp [levelZeroTruthFormula, baseCrossLevelFormula]

/-- At a positive orbit stage, specialization of the structural source
context is exactly the represented cross-level field already present in the
current certificate. -/
@[simp] theorem translate_sourcePriorCrossLevelContext_orbit (n : V) :
    translateFormula (truthFormula n) (truthFormula (n + 1))
        ![n + 1, n + 1 + 1, n + 1 + 1 + 1]
        (Rewriting.emb sourcePriorCrossLevelContext) =
      orbitSuccessorCrossLevelFormula n := by
  rw [translate_sourcePriorCrossLevelContext, truthFormula_succ]
  rfl

/-- The same positive specialization sends the unary invariant to the exact
predicate whose universal closure is the next orbit cross-level field. -/
@[simp] theorem translate_sourceNextCrossLevelInvariant_orbit (n : V) :
    translateFormula (truthFormula n) (truthFormula (n + 1))
        ![n + 1, n + 1 + 1, n + 1 + 1 + 1]
        (Rewriting.emb sourceNextCrossLevelInvariant) =
      crossLevelPredicateFormula (truthFormula (n + 1))
        (n + 1 + 1) (n + 1 + 1 + 1) := by
  simp

/-- After universal closure, the positive invariant is literally the next
represented orbit field rather than merely an equivalent formula. -/
@[simp] theorem translate_sourceNextCrossLevelInvariant_orbit_closure
    (n : V) :
    (∀⁰ translateFormula (truthFormula n) (truthFormula (n + 1))
        ![n + 1, n + 1 + 1, n + 1 + 1 + 1]
        (Rewriting.emb sourceNextCrossLevelInvariant)) =
      orbitSuccessorCrossLevelFormula (n + 1) := by
  rw [translate_sourceNextCrossLevelInvariant_closure]
  rfl

end LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceTemplate
