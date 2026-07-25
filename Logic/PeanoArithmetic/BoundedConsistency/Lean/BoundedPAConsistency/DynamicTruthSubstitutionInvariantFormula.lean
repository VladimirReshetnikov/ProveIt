import BoundedPAConsistency.DynamicTruthOrbit
import BoundedPAConsistency.DynamicTruthTemplateFormula
import BoundedPAConsistency.TermEvaluationTransport
import BoundedPAConsistency.FinFunext

/-!
# The model-coded simultaneous-substitution invariance field

Uniform truth certificates need a syntactic field saying that truth commutes
with simultaneous substitution.  At a nonstandard hierarchy stage neither
the formula nor its substituted result may be decoded externally.  The
substituted code is therefore exposed by the represented substsGraph.

The semantic substitution environment also receives a fixed arithmetic name
in this module.  Its displayed formula uses only stable named graph formulas
for HFS lookup, truncated subtraction, term-vector lookup, and term
evaluation.  The source truth law then lives in the fixed language with one
ternary predicate placeholder and two named hierarchy levels.

This file fixes the certificate syntax, proves literal specialization, and
represents the positive orbit's raw codes.  Construction of the PA induction
kernel proving the field is intentionally left to a later module.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantFormula

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthTemplateFormula
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters
open LeanProofs.BoundedPAConsistency.TermEvaluation
open LeanProofs.BoundedPAConsistency.TermEvaluationTransport

/-! ## Stable arithmetic syntax for substitution environments -/

/-- Stable Sigma-one syntax for IsSubstitutionEnvironment.

The free variables are ordered (bound, free, arity, terms, subBound).
For each substitution-vector position z, subDef computes the reversed
de Bruijn position in subBound, znthDef reads that position, nthDef reads the
z-th substituting term, and termValueGraph evaluates it in (bound, free).
All graph witnesses remain explicit in the formula. -/
noncomputable def isSubstitutionEnvironmentDef :
    HierarchySymbol.sigmaOne.Semisentence 5 := .mkSigma
  “bound free arity terms subBound.
    !(isUTermVec ℒₒᵣ).sigma arity terms ∧
    !seqDef bound ∧
    !seqDef free ∧
    !seqDef subBound ∧
    !lhDef arity subBound ∧
    ∀ z < arity,
      ∃ position, !subDef position arity (z + 1) ∧
      ∃ subValue, !znthDef subValue subBound position ∧
      ∃ term, !nthDef term terms z ∧
      ∃ value, !termValueGraph value bound free term ∧
        subValue = value”

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- The displayed arithmetic formula defines the semantic substitution
environment in every model of I Sigma 1. -/
instance isSubstitutionEnvironment_defined :
    HierarchySymbol.Defined (V := V)
      (fun v : Fin 5 → V ↦
        IsSubstitutionEnvironment
          (v 0) (v 1) (v 2) (v 3) (v 4))
      isSubstitutionEnvironmentDef := .mk fun v ↦ by
  simp [isSubstitutionEnvironmentDef, IsSubstitutionEnvironment,
    IsSubstitutionBound, boundPosition]
  intro _ _ _ _
  constructor
  · rintro ⟨hlen, hvalues⟩
    refine ⟨hlen.symm, ?_⟩
    intro z hz
    simpa [hlen] using hvalues z hz
  · rintro ⟨hlen, hvalues⟩
    refine ⟨hlen.symm, ?_⟩
    intro z hz
    simpa [hlen] using hvalues z hz

@[simp] theorem eval_isSubstitutionEnvironmentDef (v : Fin 5 → V) :
    isSubstitutionEnvironmentDef.val.Evalb v ↔
      IsSubstitutionEnvironment
        (v 0) (v 1) (v 2) (v 3) (v 4) :=
  isSubstitutionEnvironment_defined.iff

/-! ## Fixed source syntax -/

/-- Apply a five-place closed arithmetic formula in SourceLanguage. -/
noncomputable def apply₅ {n : ℕ}
    (p : Semisentence SourceLanguage 5)
    (t₀ t₁ t₂ t₃ t₄ : ClosedSemiterm SourceLanguage n) :
    Semisentence SourceLanguage n :=
  p ⇜ ![t₀, t₁, t₂, t₃, t₄]

/-- The substituting vector is an arity-long vector of terms with at most
termBound available bound variables.

The seven-variable body is ordered
(arity, bound, free, termBound, terms, subBound, formula). -/
noncomputable def sourceSemitermVector : Semisentence SourceLanguage 7 :=
  apply₃
    (liftArithmeticFormula (isSemitermVec ℒₒᵣ).sigma.val)
    (#0) (#3) (#4)

/-- The original bound environment has the depth permitted in the
substituting terms. -/
noncomputable def sourceBoundLength : Semisentence SourceLanguage 7 :=
  apply₂ (liftArithmeticFormula lhDef.val) (#3) (#1)

/-- Apply the stable substitution-environment formula. -/
noncomputable def sourceSubstitutionEnvironment :
    Semisentence SourceLanguage 7 :=
  apply₅ (liftArithmeticFormula isSubstitutionEnvironmentDef.val)
    (#1) (#2) (#0) (#4) (#5)

/-- The original code is an arity-semitformula. -/
noncomputable def sourceSemiformula : Semisentence SourceLanguage 7 :=
  apply₂
    (liftArithmeticFormula (isSemiformula ℒₒᵣ).sigma.val)
    (#0) (#6)

/-- The formula code lies in the hierarchy fragment one level below the
successor truth predicate. -/
noncomputable def sourceBoundedDomain : Semisentence SourceLanguage 7 :=
  apply₂
    (liftArithmeticFormula (quantifierBoundedCodeDef ℒₒᵣ).val)
    (parameterTerm 0) (#6)

/-- A represented substituted formula code together with the desired truth
equivalence.

Under the existential binder the new code is #0, the terms vector is #5,
and the original formula is #7.  The truth calls use bound environments #2
and #6 respectively, with the same free environment #3. -/
noncomputable def sourceSubstitutedTruthWitness :
    Semisentence SourceLanguage 7 :=
  ∃⁰
    (apply₃ (liftArithmeticFormula (substsGraph ℒₒᵣ).val)
        (#0) (#5) (#7) ⋏
      LogicalConnective.iff
        (apply₃ successorTruthFormula (#2) (#3) (#0))
        (apply₃ successorTruthFormula (#6) (#3) (#7)))

/-- The complete simultaneous-substitution implication for fixed inputs. -/
noncomputable def sourceSubstitutionInvariantBody :
    Semisentence SourceLanguage 7 :=
  Arrow.arrow
    (sourceSemitermVector ⋏
      (sourceBoundLength ⋏
        (sourceSubstitutionEnvironment ⋏
          (sourceSemiformula ⋏ sourceBoundedDomain))))
    sourceSubstitutedTruthWitness

/-- Unary induction predicate: only the original formula code remains free. -/
noncomputable def sourceSubstitutionInvariantPredicate :
    Semisentence SourceLanguage 1 :=
  ∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ sourceSubstitutionInvariantBody

/-- Universally closed simultaneous-substitution certificate field. -/
noncomputable def sourceSubstitutionInvariantSentence :
    Sentence SourceLanguage :=
  ∀⁰ sourceSubstitutionInvariantPredicate

/-! ## Typed model-coded syntax -/

/-- Apply the named semiterm-vector predicate in the seven-variable
certificate context. -/
noncomputable def semitermVectorFormula :
    Bootstrapping.Semiformula V ℒₒᵣ 7 :=
  (⌜(isSemitermVec ℒₒᵣ).sigma.val⌝ :
      Bootstrapping.Semiformula V ℒₒᵣ 3).subst
    ![Semiterm.bvar (0 : Fin 7),
      Semiterm.bvar (3 : Fin 7),
      Semiterm.bvar (4 : Fin 7)]

/-- The graph assertion termBound = lh bound. -/
noncomputable def boundLengthFormula :
    Bootstrapping.Semiformula V ℒₒᵣ 7 :=
  (⌜lhDef.val⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).subst
    ![Semiterm.bvar (3 : Fin 7), Semiterm.bvar (1 : Fin 7)]

/-- Apply the stable named substitution-environment relation. -/
noncomputable def substitutionEnvironmentFormula :
    Bootstrapping.Semiformula V ℒₒᵣ 7 :=
  (⌜isSubstitutionEnvironmentDef.val⌝ :
      Bootstrapping.Semiformula V ℒₒᵣ 5).subst
    ![Semiterm.bvar (1 : Fin 7),
      Semiterm.bvar (2 : Fin 7),
      Semiterm.bvar (0 : Fin 7),
      Semiterm.bvar (4 : Fin 7),
      Semiterm.bvar (5 : Fin 7)]

/-- Apply the named arity-semitformula predicate. -/
noncomputable def semiformulaFormula :
    Bootstrapping.Semiformula V ℒₒᵣ 7 :=
  (⌜(isSemiformula ℒₒᵣ).sigma.val⌝ :
      Bootstrapping.Semiformula V ℒₒᵣ 2).subst
    ![Semiterm.bvar (0 : Fin 7), Semiterm.bvar (6 : Fin 7)]

/-- Apply the named bounded-code predicate at a model-coded lower level. -/
noncomputable def boundedDomainFormula (lowerLevel : V) :
    Bootstrapping.Semiformula V ℒₒᵣ 7 :=
  (⌜(quantifierBoundedCodeDef ℒₒᵣ).val⌝ :
      Bootstrapping.Semiformula V ℒₒᵣ 2).subst
    ![Arithmetic.typedNumeral lowerLevel,
      Semiterm.bvar (6 : Fin 7)]

/-- Typed represented-substitution witness for an arbitrary upper truth
predicate. -/
noncomputable def substitutedTruthWitnessFormula
    (upper : Bootstrapping.Semiformula V ℒₒᵣ 3) :
    Bootstrapping.Semiformula V ℒₒᵣ 7 :=
  ∃⁰
    (((⌜(substsGraph ℒₒᵣ).val⌝ :
          Bootstrapping.Semiformula V ℒₒᵣ 3).subst
        ![Semiterm.bvar (0 : Fin 8),
          Semiterm.bvar (5 : Fin 8),
          Semiterm.bvar (7 : Fin 8)]) ⋏
      LogicalConnective.iff
        (DynamicTruthFormula.apply₃ upper
          (Semiterm.bvar (2 : Fin 8))
          (Semiterm.bvar (3 : Fin 8))
          (Semiterm.bvar (0 : Fin 8)))
        (DynamicTruthFormula.apply₃ upper
          (Semiterm.bvar (6 : Fin 8))
          (Semiterm.bvar (3 : Fin 8))
          (Semiterm.bvar (7 : Fin 8))))

/-- Typed body of simultaneous-substitution invariance for one successor
truth constructor. -/
noncomputable def substitutionInvariantBodyFormula
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    Bootstrapping.Semiformula V ℒₒᵣ 7 :=
  Arrow.arrow
    (semitermVectorFormula ⋏
      (boundLengthFormula ⋏
        (substitutionEnvironmentFormula ⋏
          (semiformulaFormula ⋏ boundedDomainFormula lowerLevel))))
    (substitutedTruthWitnessFormula
      (DynamicTruthFormula.successorTruthFormula
        lower lowerLevel upperLevel))

/-- Unary predicate intended for the later PA induction kernel. -/
noncomputable def substitutionInvariantPredicateFormula
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    Bootstrapping.Semiformula V ℒₒᵣ 1 :=
  ∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰
    substitutionInvariantBodyFormula lower lowerLevel upperLevel

/-- Universally closed simultaneous-substitution certificate field. -/
noncomputable def substitutionInvariantFormula
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) : Bootstrapping.Formula V ℒₒᵣ :=
  ∀⁰ substitutionInvariantPredicateFormula lower lowerLevel upperLevel

/-! ## Exact source specialization -/

/-- Five-place source application commutes literally with specialization. -/
@[simp] theorem translate_apply₅
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 2 → V)
    (p : Semisentence SourceLanguage 5)
    (t₀ t₁ t₂ t₃ t₄ : ClosedSemiterm SourceLanguage n) :
    translateFormula lower parameters
        (Rewriting.emb (apply₅ p t₀ t₁ t₂ t₃ t₄)) =
      (translateFormula lower parameters (Rewriting.emb p)).subst
        ![translateTerm parameters
            (Rew.emb t₀ : SyntacticSemiterm SourceLanguage n),
          translateTerm parameters
            (Rew.emb t₁ : SyntacticSemiterm SourceLanguage n),
          translateTerm parameters
            (Rew.emb t₂ : SyntacticSemiterm SourceLanguage n),
          translateTerm parameters
            (Rew.emb t₃ : SyntacticSemiterm SourceLanguage n),
          translateTerm parameters
            (Rew.emb t₄ : SyntacticSemiterm SourceLanguage n)] := by
  rw [apply₅, Semiformula.coe_subst_eq_subst_coe,
    ModelCodedPredicateParameters.translateFormula_subst]
  congr 1
  exact funext_fin5 rfl rfl rfl rfl rfl

@[simp] theorem translate_sourceSemitermVector
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceSemitermVector) =
      semitermVectorFormula := by
  simp [sourceSemitermVector, semitermVectorFormula,
    ModelCodedPredicateParameters.translateTerm]

@[simp] theorem translate_sourceBoundLength
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceBoundLength) =
      boundLengthFormula := by
  simp [sourceBoundLength, boundLengthFormula,
    ModelCodedPredicateParameters.translateTerm]

@[simp] theorem translate_sourceSubstitutionEnvironment
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceSubstitutionEnvironment) =
      substitutionEnvironmentFormula := by
  simp [sourceSubstitutionEnvironment, substitutionEnvironmentFormula,
    ModelCodedPredicateParameters.translateTerm]

@[simp] theorem translate_sourceSemiformula
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceSemiformula) =
      semiformulaFormula := by
  simp [sourceSemiformula, semiformulaFormula,
    ModelCodedPredicateParameters.translateTerm]

@[simp] theorem translate_sourceBoundedDomain
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceBoundedDomain) =
      boundedDomainFormula lowerLevel := by
  simp [sourceBoundedDomain, boundedDomainFormula,
    ModelCodedPredicateParameters.translateTerm]

@[simp] theorem translate_sourceSubstitutedTruthWitness
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceSubstitutedTruthWitness) =
      substitutedTruthWitnessFormula
        (DynamicTruthFormula.successorTruthFormula
          lower lowerLevel upperLevel) := by
  simp [sourceSubstitutedTruthWitness, substitutedTruthWitnessFormula,
    LogicalConnective.iff,
    ModelCodedPredicateParameters.translateFormula,
    ModelCodedPredicateParameters.translateTerm,
    DynamicTruthFormula.apply₃]
  constructor
  · let sourceLeft : Semisentence SourceLanguage 8 :=
      apply₃ successorTruthFormula (#2) (#3) (#0)
    let typedLeft : Bootstrapping.Semiformula V ℒₒᵣ 8 :=
      DynamicTruthFormula.apply₃
        (DynamicTruthFormula.successorTruthFormula
          lower lowerLevel upperLevel)
        (Semiterm.bvar (2 : Fin 8))
        (Semiterm.bvar (3 : Fin 8))
        (Semiterm.bvar (0 : Fin 8))
    have hneg :
        translateFormula lower ![lowerLevel, upperLevel]
            (Semiformula.neg (Rewriting.emb sourceLeft)) =
          ∼typedLeft := by
      calc
        _ = ∼translateFormula lower ![lowerLevel, upperLevel]
            (Rewriting.emb sourceLeft) := by
          simpa only [Semiformula.neg_eq] using
            (ModelCodedPredicateParameters.translateFormula_neg
              lower ![lowerLevel, upperLevel]
              (Rewriting.emb sourceLeft))
        _ = _ := congrArg (∼·) (by
          simp [sourceLeft, typedLeft,
            ModelCodedPredicateParameters.translateTerm,
            DynamicTruthFormula.apply₃])
    rw [show
      translateFormula lower ![lowerLevel, upperLevel]
          (Semiformula.neg
            (Rewriting.emb
              (apply₃ successorTruthFormula (#2) (#3) (#0)))) =
        ∼typedLeft by simpa [sourceLeft] using hneg]
    simp [typedLeft, DynamicTruthFormula.apply₃,
      Bootstrapping.Semiformula.imp_def]
  · let sourceRight : Semisentence SourceLanguage 8 :=
      apply₃ successorTruthFormula (#6) (#3) (#7)
    let typedRight : Bootstrapping.Semiformula V ℒₒᵣ 8 :=
      DynamicTruthFormula.apply₃
        (DynamicTruthFormula.successorTruthFormula
          lower lowerLevel upperLevel)
        (Semiterm.bvar (6 : Fin 8))
        (Semiterm.bvar (3 : Fin 8))
        (Semiterm.bvar (7 : Fin 8))
    have hneg :
        translateFormula lower ![lowerLevel, upperLevel]
            (Semiformula.neg (Rewriting.emb sourceRight)) =
          ∼typedRight := by
      calc
        _ = ∼translateFormula lower ![lowerLevel, upperLevel]
            (Rewriting.emb sourceRight) := by
          simpa only [Semiformula.neg_eq] using
            (ModelCodedPredicateParameters.translateFormula_neg
              lower ![lowerLevel, upperLevel]
              (Rewriting.emb sourceRight))
        _ = _ := congrArg (∼·) (by
          simp [sourceRight, typedRight,
            ModelCodedPredicateParameters.translateTerm,
            DynamicTruthFormula.apply₃])
    rw [show
      translateFormula lower ![lowerLevel, upperLevel]
          (Semiformula.neg
            (Rewriting.emb
              (apply₃ successorTruthFormula (#6) (#3) (#7)))) =
        ∼typedRight by simpa [sourceRight] using hneg]
    simp [typedRight, DynamicTruthFormula.apply₃,
      Bootstrapping.Semiformula.imp_def]

@[simp] theorem translate_sourceSubstitutionInvariantBody
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceSubstitutionInvariantBody) =
      substitutionInvariantBodyFormula lower lowerLevel upperLevel := by
  simp [sourceSubstitutionInvariantBody,
    substitutionInvariantBodyFormula,
    Bootstrapping.Semiformula.imp_def,
    ModelCodedPredicateParameters.translateFormula]

@[simp] theorem translate_sourceSubstitutionInvariantPredicate
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceSubstitutionInvariantPredicate) =
      substitutionInvariantPredicateFormula
        lower lowerLevel upperLevel := by
  simp [sourceSubstitutionInvariantPredicate,
    substitutionInvariantPredicateFormula,
    ModelCodedPredicateParameters.translateFormula]

/-- Arbitrary model-coded specialization of the fixed source sentence is
literally the advertised simultaneous-substitution field. -/
@[simp] theorem translate_sourceSubstitutionInvariantSentence
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceSubstitutionInvariantSentence) =
      substitutionInvariantFormula lower lowerLevel upperLevel := by
  simp [sourceSubstitutionInvariantSentence,
    substitutionInvariantFormula,
    ModelCodedPredicateParameters.translateFormula]

/-! ## The represented orbit instances -/

/-- The same field constructor with its upper truth predicate supplied
directly.  This view lets the orbit equations name the literal member
truthFormula k instead of only the successor expression that constructs it. -/
noncomputable def upperSubstitutionInvariantFormula
    (upper : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (boundedLevel : V) : Bootstrapping.Formula V ℒₒᵣ :=
  ∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰
    (Arrow.arrow
      (semitermVectorFormula ⋏
        (boundLengthFormula ⋏
          (substitutionEnvironmentFormula ⋏
            (semiformulaFormula ⋏
              boundedDomainFormula boundedLevel))))
      (substitutedTruthWitnessFormula upper))

/-- Base field for truthFormula 0 = levelZeroTruthFormula. -/
noncomputable def baseSubstitutionInvariantFormula :
    Bootstrapping.Formula V ℒₒᵣ :=
  substitutionInvariantFormula baseTruthFormula 0 1

/-- The base field's upper predicate is literally the zeroth represented
orbit member. -/
theorem baseSubstitutionInvariantFormula_eq_upper :
    baseSubstitutionInvariantFormula (V := V) =
      upperSubstitutionInvariantFormula (truthFormula 0) 0 := by
  simp [baseSubstitutionInvariantFormula,
    upperSubstitutionInvariantFormula,
    substitutionInvariantFormula,
    substitutionInvariantPredicateFormula,
    substitutionInvariantBodyFormula, truthFormula_zero,
    DynamicTruthFormula.levelZeroTruthFormula]

/-- Positive successor field, on codes bounded at n + 1. -/
noncomputable def orbitSuccessorSubstitutionInvariantFormula (n : V) :
    Bootstrapping.Formula V ℒₒᵣ :=
  substitutionInvariantFormula
    (truthFormula n) (n + 1) (n + 1 + 1)

/-- Expose the exact upper predicate used by the positive branch. -/
theorem orbitSuccessorSubstitutionInvariantFormula_upper (n : V) :
    orbitSuccessorSubstitutionInvariantFormula n =
      upperSubstitutionInvariantFormula
        (truthFormula (n + 1)) (n + 1) := by
  simp [orbitSuccessorSubstitutionInvariantFormula,
    upperSubstitutionInvariantFormula,
    substitutionInvariantFormula,
    substitutionInvariantPredicateFormula,
    substitutionInvariantBodyFormula, truthFormula_succ]

/-! ## Representability of the positive-branch code -/

/-- The raw code of the positive simultaneous-substitution field is
Sigma-one definable as a function of its possibly nonstandard predecessor.

All formula-building operations are represented syntax constructors.  The
only recursively varying component is truthFormulaCode. -/
theorem orbitSuccessorSubstitutionInvariantFormulaCode_definable :
    HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦
        (orbitSuccessorSubstitutionInvariantFormula n).val) := by
  simp only [orbitSuccessorSubstitutionInvariantFormula,
    substitutionInvariantFormula,
    substitutionInvariantPredicateFormula,
    substitutionInvariantBodyFormula,
    substitutedTruthWitnessFormula,
    semitermVectorFormula, boundLengthFormula,
    substitutionEnvironmentFormula, semiformulaFormula,
    boundedDomainFormula,
    DynamicTruthFormula.apply₃_val,
    Semiformula.val_all, Semiformula.val_imp,
    Semiformula.val_and, Semiformula.val_exs,
    Semiformula.val_iff,
    Bootstrapping.Semiformula.val_substs]
  aesop (config := { terminal := true, maxRuleApplicationDepth := 100 })
    (rule_sets := [Definability])

end LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantFormula
