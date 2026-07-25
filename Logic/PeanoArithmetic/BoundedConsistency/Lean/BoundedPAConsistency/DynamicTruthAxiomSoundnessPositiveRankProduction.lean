import BoundedPAConsistency.DynamicTruthAxiomSoundnessStrongStepSource
import BoundedPAConsistency.DynamicTruthAxiomSoundnessStructuralSuccessor
import BoundedPAConsistency.DynamicTruthCertificateFieldFamily
import BoundedPAConsistency.DynamicTruthQuantifierFreeAnchor
import BoundedPAConsistency.StagedTruthCertificateProofCompiler
import BoundedPAConsistency.TernaryCongruencePrototype
import BoundedPAConsistency.TruthCertificateContextProjection

/-!
# Production compilation of positive-rank PA-axiom soundness

The fixed source step proves soundness of the represented PA-axiom
recognizer from the adjacency of the two named levels, the lower predicate's
existential law, three already installed certificate fields, and three
induction interfaces.  This module compiles that theorem into represented PA,
discharges the placeholder congruence by formula replacement, supplies each
context conjunct at a positive orbit index, and installs the resulting
induction kernel under the exact staged substitution context.

Two of the context conjuncts are ordinary induction axioms for closed
model-coded predicates, so they are supplied by PA's represented induction
recognizer rather than by the certificate.  The adjacency equation becomes a
reflexive equation between typed numerals, because the represented numeral
constructor exposes successor addition syntactically at a positive lower
level.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessPositiveRankProduction

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessStrongStepSource
open LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessStructuralSuccessor
open LeanProofs.BoundedPAConsistency.DynamicTruthCertificateFieldFamily
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthLowerExistentialInterface
open LeanProofs.BoundedPAConsistency.DynamicTruthLowerExistentialLawsFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthQuantifierFreeAnchor
open LeanProofs.BoundedPAConsistency.DynamicTruthSemanticInductionCompilation
open LeanProofs.BoundedPAConsistency.DynamicTruthSemanticInductionSource
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthTemplateFormula
open LeanProofs.BoundedPAConsistency.ModelCodedInductionAxiom
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateEqualityQuotient
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters
open LeanProofs.BoundedPAConsistency.PrimitiveRecursiveTruthCertificate
open LeanProofs.BoundedPAConsistency.StagedTruthCertificateProofCompiler
open LeanProofs.BoundedPAConsistency.TernaryCongruencePrototype
open LeanProofs.BoundedPAConsistency.TruthCertificateContextProjection
open LeanProofs.BoundedPAConsistency.TruthCertificateProofCompiler

private abbrev L := DynamicTruthTemplateFormula.SourceLanguage

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-! ## Structural translation lemmas -/

private theorem translate_and {n : ℕ}
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 2 → V) (p q : Semisentence L n) :
    translateFormula lower parameters (Rewriting.emb (p ⋏ q)) =
      translateFormula lower parameters (Rewriting.emb p) ⋏
        translateFormula lower parameters (Rewriting.emb q) := by
  simp [ModelCodedPredicateParameters.translateFormula]

private theorem translate_arrow {n : ℕ}
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 2 → V) (p q : Semisentence L n) :
    translateFormula lower parameters (Rewriting.emb (Arrow.arrow p q)) =
      Arrow.arrow
        (translateFormula lower parameters (Rewriting.emb p))
        (translateFormula lower parameters (Rewriting.emb q)) := by
  simp [Semiformula.imp_def]

private theorem translate_all {n : ℕ}
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 2 → V) (p : Semisentence L (n + 1)) :
    translateFormula lower parameters (Rewriting.emb (∀⁰ p)) =
      ∀⁰ translateFormula lower parameters (Rewriting.emb p) := by
  simp [ModelCodedPredicateParameters.translateFormula]

private theorem translate_substOne {n : ℕ}
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 2 → V)
    (p : Semisentence L 1) (t : ClosedSemiterm L n) :
    translateFormula lower parameters (Rewriting.emb (p/[t])) =
      (translateFormula lower parameters (Rewriting.emb p)).subst
        ![translateTerm parameters
          (Rew.emb t : SyntacticSemiterm L n)] := by
  rw [Rewriting.emb_subst_eq_subst_coe₁,
    ModelCodedPredicateParameters.translateFormula_subst]
  congr 1
  funext i
  exact Fin.eq_zero i ▸ rfl

/-- The generic closed induction axiom translates literally to the typed
induction body consumed by PA's represented recognizer. -/
@[simp] theorem translate_sourceInductionAxiom
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) (P : Semisentence L 1) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb (sourceInductionAxiom P)) =
      indBody
        (translateFormula lower ![lowerLevel, upperLevel]
          (Rewriting.emb P)) := by
  simp only [sourceInductionAxiom, indBody,
    translate_arrow, translate_all, translate_substOne]
  have hzero :
      translateTerm ![lowerLevel, upperLevel]
          (Rew.emb (sourceZero (n := 0)) :
            SyntacticSemiterm L 0) =
        (Arithmetic.typedNumeral 0 :
          Bootstrapping.Semiterm V ℒₒᵣ 0) := by
    ext
    simp [sourceZero, ModelCodedPredicateParameters.translateTerm,
      Arithmetic.typedNumeral]
  have hvar :
      translateTerm ![lowerLevel, upperLevel]
          (Rew.emb (#0 : ClosedSemiterm L 1) :
            SyntacticSemiterm L 1) =
        (Bootstrapping.Semiterm.bvar 0 :
          Bootstrapping.Semiterm V ℒₒᵣ 1) := rfl
  have hsucc :
      translateTerm ![lowerLevel, upperLevel]
          (Rew.emb (sourceSucc (#0) : ClosedSemiterm L 1) :
            SyntacticSemiterm L 1) =
        (Bootstrapping.Semiterm.bvar 0 + Arithmetic.typedNumeral 1 :
          Bootstrapping.Semiterm V ℒₒᵣ 1) := by
    ext
    simp [sourceSucc, DynamicTruthSemanticInductionSource.sourceOne,
      ModelCodedPredicateParameters.translateTerm,
      Arithmetic.typedNumeral]
  rw [hzero, hvar, hsucc]
  simp

/-- Specialization of the adjacency equation.  At a positive lower level the
represented numeral of the successor is literally the sum term, so the
translated equation compares two typed numerals. -/
theorem translate_sourceLevelAdjacency
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) (hpositive : 0 < lowerLevel) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceLevelAdjacency) =
      (Arithmetic.typedNumeral upperLevel ≐
        Arithmetic.typedNumeral (lowerLevel + 1)) := by
  simp [sourceLevelAdjacency, sourceEquals,
    ModelCodedPredicateParameters.translateFormula,
    translate_sourceLowerLevelSuccessor
      (parameters := ![lowerLevel, upperLevel]) hpositive]

/-! ## Named translated induction predicates -/

/-- Translation of the packed free-independence invariant. -/
noncomputable def freeIndependencePredicateFormula
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    Bootstrapping.Semiformula V ℒₒᵣ 1 :=
  translateFormula lower ![lowerLevel, upperLevel]
    (Rewriting.emb sourceFreeIndependencePredicate)

/-- Translation of the packed universal-closure invariant. -/
noncomputable def closurePredicateFormula
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    Bootstrapping.Semiformula V ℒₒᵣ 1 :=
  translateFormula lower ![lowerLevel, upperLevel]
    (Rewriting.emb sourceClosurePredicate)

/-- Both packed predicates are closed whenever the substituted lower truth
formula is closed.  Arguing through source translation keeps the statement
valid for nonstandard model-coded syntax. -/
@[simp] theorem freeIndependencePredicateFormula_shift
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) (hlower : lower.shift = lower) :
    (freeIndependencePredicateFormula
      lower lowerLevel upperLevel).shift =
      freeIndependencePredicateFormula lower lowerLevel upperLevel := by
  unfold freeIndependencePredicateFormula
  rw [← translateFormula_shift lower ![lowerLevel, upperLevel] hlower]
  congr 1
  unfold Rewriting.shift Rewriting.emb
  rw [← TransitiveRewriting.comp_app]
  congr 2
  ext x <;> simp

@[simp] theorem closurePredicateFormula_shift
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) (hlower : lower.shift = lower) :
    (closurePredicateFormula lower lowerLevel upperLevel).shift =
      closurePredicateFormula lower lowerLevel upperLevel := by
  unfold closurePredicateFormula
  rw [← translateFormula_shift lower ![lowerLevel, upperLevel] hlower]
  congr 1
  unfold Rewriting.shift Rewriting.emb
  rw [← TransitiveRewriting.comp_app]
  congr 2
  ext x <;> simp

/-! ## The translated law context -/

/-- Typed spelling of the fixed source context.  Every conjunct is a formula
already named by the certificate development, an induction body accepted by
PA's recognizer, or the reflexive level equation. -/
noncomputable def axiomSoundnessLawContextFormula
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) : Bootstrapping.Formula V ℒₒᵣ :=
  (Arithmetic.typedNumeral upperLevel ≐
      Arithmetic.typedNumeral (lowerLevel + 1)) ⋏
    (lowerExistentialLawsFormula lower lowerLevel upperLevel ⋏
      (crossLevelFormula lower lowerLevel upperLevel ⋏
        (shiftInvariantFormula lower lowerLevel upperLevel ⋏
          (substitutionInvariantFormula lower lowerLevel upperLevel ⋏
            (semanticInductionFormula lower lowerLevel upperLevel ⋏
              (indBody
                  (freeIndependencePredicateFormula
                    lower lowerLevel upperLevel) ⋏
                indBody
                  (closurePredicateFormula
                    lower lowerLevel upperLevel)))))))

/-- Literal specialization of the complete fixed source context. -/
theorem translate_sourceAxiomSoundnessLawContext
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) (hpositive : 0 < lowerLevel) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceAxiomSoundnessLawContext) =
      axiomSoundnessLawContextFormula lower lowerLevel upperLevel := by
  rw [sourceAxiomSoundnessLawContext]
  rw [translate_and, translate_and, translate_and, translate_and,
    translate_and, translate_and, translate_and]
  rw [translate_sourceLevelAdjacency lower lowerLevel upperLevel hpositive,
    DynamicTruthCrossLevelFormula.translate_sourceCrossLevelSentence,
    DynamicTruthShiftInvariantFormula.translate_sourceShiftInvariantSentence,
    DynamicTruthSubstitutionInvariantFormula.translate_sourceSubstitutionInvariantSentence,
    translate_sourceInductionAxiom, translate_sourceInductionAxiom]
  rfl

/-! ## Compiling the source step -/

private theorem emb_sourceCongruentAxiomSoundnessStepSentence :
    (Rewriting.emb sourceCongruentAxiomSoundnessStepSentence :
        Proposition L) =
      Arrow.arrow
        (Rewriting.emb (placeholderCongruenceSentence 3 2) :
          Proposition L)
        (Rewriting.emb sourceAxiomSoundnessStepSentence :
          Proposition L) := by
  unfold sourceCongruentAxiomSoundnessStepSentence
  rw [LogicalConnective.HomClass.map_imply]

private theorem emb_sourceAxiomSoundnessStepSentence :
    (Rewriting.emb sourceAxiomSoundnessStepSentence : Proposition L) =
      Arrow.arrow
        (Rewriting.emb sourceAxiomSoundnessLawContext : Proposition L)
        (Rewriting.emb sourceAxiomSoundnessSentence : Proposition L) := by
  unfold sourceAxiomSoundnessStepSentence
  rw [LogicalConnective.HomClass.map_imply]

/-- Compile the audited fixed-source derivation and discharge its sole opaque
relation congruence hypothesis with represented PA replacement. -/
noncomputable def compiledAxiomSoundnessStepProof
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) (hlower : lower.shift = lower)
    (hpositive : 0 < lowerLevel) :
    Peano.internalize V ⊢!
      axiomSoundnessLawContextFormula lower lowerLevel upperLevel 🡒
        axiomSoundnessFormula lower lowerLevel upperLevel := by
  have hcompiled : Peano.internalize V ⊢!
      translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceCongruentAxiomSoundnessStepSentence) :=
    ModelCodedPredicateParameters.compilePeanoTemplate
      lower ![lowerLevel, upperLevel] hlower
      sourceCongruentAxiomSoundnessStepProof
  rw [emb_sourceCongruentAxiomSoundnessStepSentence,
    DynamicTruthTemplateFormula.translate_imp,
    emb_sourceAxiomSoundnessStepSentence,
    DynamicTruthTemplateFormula.translate_imp,
    translate_sourceAxiomSoundnessLawContext lower lowerLevel upperLevel
      hpositive,
    translate_sourceAxiomSoundnessSentence] at hcompiled
  exact hcompiled ⨀
    translatedOnePredicateCongruenceProof
      lower ![lowerLevel, upperLevel]

/-! ## Supplying the context at a positive orbit index -/

section Orbit

/-- The level parameters do not occur in the lower predicate's existential
law, so the same represented sentence serves at every parameter tuple. -/
theorem lowerExistentialLawsFormula_parameters
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel lowerLevel' upperLevel' : V) :
    lowerExistentialLawsFormula lower lowerLevel upperLevel =
      lowerExistentialLawsFormula lower lowerLevel' upperLevel' := by
  simp [lowerExistentialLawsFormula,
    sourceLowerExistentialLawsSentence, sourceLowerExistentialBody,
    sourceLowerExistentialCodeWitness, sourceLowerExtendedTruthWitness,
    sourceLowerFormulaDomain,
    ModelCodedPredicateParameters.translateFormula,
    ModelCodedPredicateParameters.translateTerm,
    FirstOrder.Semiformula.iff_eq]
  simp only [← FirstOrder.Semiformula.neg_eq,
    ModelCodedPredicateParameters.translateFormula_neg]
  congr 1
  simp [ModelCodedPredicateParameters.translateTerm]

/-- The adjacency conjunct becomes a reflexive equation between typed
numerals at every positive lower level. -/
noncomputable def levelAdjacencyProof (n : V) :
    Peano.internalize V ⊢!
      (Arithmetic.typedNumeral (n + 1 + 1) ≐
        Arithmetic.typedNumeral (n + 1 + 1) : Bootstrapping.Formula V ℒₒᵣ) :=
  (Arithmetic.eq_refl Peano (Arithmetic.typedNumeral (n + 1 + 1))).get

/-- Every conjunct of the source context is available at a positive orbit
index.  The three certificate fields are projected from the staged
substitution context; the remaining conjuncts are proved outright. -/
noncomputable def proveOrbitLawContextFromSubstitutionContext (m : V) :
    Peano.internalize V ⊢!
      substitutionContext
          ((compiledDynamicTruthCertificateFamily (V := V)).fields (m + 1))
          (orbitCompiledLocalBundleWithQuantifierFreeIntroduction (m + 1))
          (orbitSuccessorCrossLevelFormula (m + 1))
          (orbitSuccessorShiftInvariantFormula (m + 1))
          (orbitSuccessorSubstitutionInvariantFormula (m + 1)) 🡒
        axiomSoundnessLawContextFormula
          (truthFormula (m + 1)) (m + 1 + 1) (m + 1 + 1 + 1) := by
  unfold axiomSoundnessLawContextFormula substitutionContext shiftContext
    crossContext localContext
  refine Entailment.CK_of_C_of_C
    (Entailment.C_of_conseq (levelAdjacencyProof (m + 1)))
    (Entailment.CK_of_C_of_C
      (Entailment.C_of_conseq ?_)
      (Entailment.CK_of_C_of_C
        (Entailment.C_trans Entailment.and₁ <|
          Entailment.C_trans Entailment.and₁ Entailment.and₂)
        (Entailment.CK_of_C_of_C
          (Entailment.C_trans Entailment.and₁ Entailment.and₂)
          (Entailment.CK_of_C_of_C Entailment.and₂
            (Entailment.CK_of_C_of_C
              (Entailment.C_of_conseq ?_)
              (Entailment.CK_of_C_of_C
                (Entailment.C_of_conseq ?_)
                (Entailment.C_of_conseq ?_)))))))
  · exact (lowerExistentialLawsFormula_parameters
      (truthFormula (m + 1)) (m + 1) (m + 1 + 1)
      (m + 1 + 1) (m + 1 + 1 + 1)) ▸
      orbitLowerExistentialLawsProof m
  · exact semanticInductionFormulaProof
      (truthFormula (m + 1)) (m + 1 + 1) (m + 1 + 1 + 1)
      (truthFormula_shift (m + 1))
  · exact paInductionProofOfShiftFixed
      (freeIndependencePredicateFormula
        (truthFormula (m + 1)) (m + 1 + 1) (m + 1 + 1 + 1))
      (congrArg Bootstrapping.Semiformula.val
        (freeIndependencePredicateFormula_shift
          (truthFormula (m + 1)) (m + 1 + 1) (m + 1 + 1 + 1)
          (truthFormula_shift (m + 1))))
  · exact paInductionProofOfShiftFixed
      (closurePredicateFormula
        (truthFormula (m + 1)) (m + 1 + 1) (m + 1 + 1 + 1))
      (congrArg Bootstrapping.Semiformula.val
        (closurePredicateFormula_shift
          (truthFormula (m + 1)) (m + 1 + 1) (m + 1 + 1 + 1)
          (truthFormula_shift (m + 1))))

/-- Represented soundness of the PA-axiom recognizer at every positive
model-coded recurrence index. -/
noncomputable def orbitAxiomSoundnessStructuralUniversalProof (m : V) :
    Peano.internalize V ⊢!
      substitutionContext
          ((compiledDynamicTruthCertificateFamily (V := V)).fields (m + 1))
          (orbitCompiledLocalBundleWithQuantifierFreeIntroduction (m + 1))
          (orbitSuccessorCrossLevelFormula (m + 1))
          (orbitSuccessorShiftInvariantFormula (m + 1))
          (orbitSuccessorSubstitutionInvariantFormula (m + 1)) 🡒
        ∀⁰ nextAxiomSoundnessPredicate (m + 1) :=
  Entailment.C_trans
    (proveOrbitLawContextFromSubstitutionContext m)
    (compiledAxiomSoundnessStepProof
      (truthFormula (m + 1)) (m + 1 + 1) (m + 1 + 1 + 1)
      (truthFormula_shift (m + 1)) (by simp))

/-- Axiom-soundness induction kernel in the exact context expected by the
staged certificate compiler at a positive transition. -/
noncomputable def stagedPositiveAxiomSoundnessInductionKernel (m : V) :
    PAInductionKernel
      (substitutionContext
        ((compiledDynamicTruthCertificateFamily (V := V)).fields (m + 1))
        (orbitCompiledLocalBundleWithQuantifierFreeIntroduction (m + 1))
        (orbitSuccessorCrossLevelFormula (m + 1))
        (orbitSuccessorShiftInvariantFormula (m + 1))
        (orbitSuccessorSubstitutionInvariantFormula (m + 1))) :=
  kernelOfStructuralUniversalProof _ (m + 1)
    (orbitAxiomSoundnessStructuralUniversalProof m)

/-- The staged kernel's predicate is the structural successor's kernel
predicate at the positive index. -/
@[simp] theorem stagedPositiveAxiomSoundnessInductionKernel_predicate
    (m : V) :
    (stagedPositiveAxiomSoundnessInductionKernel m).predicate =
      nextAxiomSoundnessPredicate (m + 1) := rfl

/-- The kernel therefore produces exactly the family's axiom-soundness field
at the next index. -/
@[simp] theorem all_nextAxiomSoundnessPredicate_eq_axiomSound (m : V) :
    (∀⁰ nextAxiomSoundnessPredicate (V := V) (m + 1)) =
      (compiledDynamicTruthCertificateFamily (V := V)).axiomSound
        (m + 1 + 1) := by
  rw [compiledDynamicTruthCertificateFamily_axiomSound_succ]
  rfl

end Orbit

end LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessPositiveRankProduction
