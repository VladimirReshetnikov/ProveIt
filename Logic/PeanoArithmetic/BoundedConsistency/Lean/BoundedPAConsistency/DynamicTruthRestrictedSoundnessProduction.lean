import BoundedPAConsistency.DynamicTruthCertificateFieldFamily
import BoundedPAConsistency.DynamicTruthRestrictedConsistencySource
import BoundedPAConsistency.DynamicTruthRestrictedSoundnessStrongStep
import BoundedPAConsistency.ModelCodedStrongInduction
import BoundedPAConsistency.StagedTruthCertificateProofCompiler
import BoundedPAConsistency.TruthCertificateContextProjection

/-!
# Production compilation of the final restricted-consistency transition

The staged certificate compiler asks for one direct proof after all four
induction kernels have run: the complete new soundness context must yield
restricted consistency at the new level.  This module supplies that proof
uniformly at every, possibly nonstandard, certificate index.

The route has three links.

* The audited fixed source theorem proves the strong-induction step for the
  invariant "every restricted derivation code has a true conclusion
  sequent".  Its antecedent is the adjacency of the two named levels, the
  lower predicate's existential law, and the four laws of the new truth
  successor.  Represented strong induction turns that step into the closed
  invariant.
* The falsity bridge of `DynamicTruthRestrictedConsistencySource` converts
  the invariant into the certificate's forced sixth coordinate.
* The two extra antecedents are discharged outright.  Adjacency becomes a
  literal instance of represented equality reflexivity, because the source
  successor term collapses to the represented numeral of the upper level at
  every positive lower level, and the orbit's lower level is `n + 1`.  The
  existential law is the already compiled law of the orbit member serving as
  lower predicate.

Only the existential law distinguishes the two ranks.  At a positive
predecessor index the lower predicate is a represented successor, so the
compiled orbit law applies; at index zero the target is restricted
consistency at the standard level one, which PA proves outright by the
fixed-level argument and D1 transports into an arbitrary model.  The public
definition is therefore uniform in the model element `n`.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthRestrictedSoundnessProduction

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency
open LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthCertificateFieldFamily
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthLowerExistentialInterface
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthQuantifierFreeAnchor
open LeanProofs.BoundedPAConsistency.DynamicTruthRestrictedConsistencySource
open LeanProofs.BoundedPAConsistency.DynamicTruthRestrictedSoundnessPredicate
open LeanProofs.BoundedPAConsistency.DynamicTruthRestrictedSoundnessStrongStep
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthTemplateFormula
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateEqualityQuotient
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters
open LeanProofs.BoundedPAConsistency.ModelCodedStrongInduction
open LeanProofs.BoundedPAConsistency.PrimitiveRecursiveTruthCertificate
open LeanProofs.BoundedPAConsistency.StagedTruthCertificateProofCompiler
open LeanProofs.BoundedPAConsistency.TernaryCongruencePrototype
open LeanProofs.BoundedPAConsistency.TruthCertificateContextProjection
open LeanProofs.BoundedPAConsistency.TruthCertificateProofCompiler
open LeanProofs.BoundedPAConsistency.UniformInternalProvability

private abbrev L := DynamicTruthTemplateFormula.SourceLanguage

/-! ## Structural translation into the generic strong-step shape -/

private theorem emb_apply₁_soundnessPredicate :
    (Rewriting.emb
        (DynamicTruthAxiomSoundnessFormula.apply₁
          sourceDerivationSoundnessPredicate
          (#0 : ClosedSemiterm L 2)) : Semiproposition L 2) =
      (Rew.subst ![(#0 : SyntacticSemiterm L 2)] ▹
        (Rewriting.emb sourceDerivationSoundnessPredicate :
          Semiproposition L 1)) := by
  unfold DynamicTruthAxiomSoundnessFormula.apply₁
  rw [Semiformula.coe_subst_eq_subst_coe]
  congr 2
  funext i
  exact Fin.eq_zero i ▸ rfl

/-- Expose the prefix's binder, guard, and unary application without
traversing the invariant itself. -/
private theorem emb_sourceDerivationSoundnessPrefix :
    (Rewriting.emb sourceDerivationSoundnessPrefix :
        Semiproposition L 1) =
      ∀⁰ Arrow.arrow
        (Rewriting.emb sourceDerivationPrefixGuard :
          Semiproposition L 2)
        (Rew.subst ![(#0 : SyntacticSemiterm L 2)] ▹
          (Rewriting.emb sourceDerivationSoundnessPredicate :
            Semiproposition L 1)) := by
  unfold sourceDerivationSoundnessPrefix
  rw [Rewriting.app_all]
  simp only [Rew.q_emb]
  rw [LogicalConnective.HomClass.map_imply, emb_apply₁_soundnessPredicate]

/-- Expose the outer implication and universal binder of the source step. -/
private theorem emb_sourceDerivationSoundnessStrongStep :
    (Rewriting.emb sourceDerivationSoundnessStrongStep : Proposition L) =
      ∀⁰ Arrow.arrow
        (Rewriting.emb sourceDerivationSoundnessPrefix :
          Semiproposition L 1)
        (Rewriting.emb sourceDerivationSoundnessPredicate :
          Semiproposition L 1) := by
  unfold sourceDerivationSoundnessStrongStep
  rw [Rewriting.app_all]
  simp only [Rew.q_emb]
  rw [LogicalConnective.HomClass.map_imply]

private theorem emb_sourceRestrictedSoundnessStrongStepSentence :
    (Rewriting.emb sourceRestrictedSoundnessStrongStepSentence :
        Proposition L) =
      Arrow.arrow
        (Rewriting.emb sourceSoundnessLawContext : Proposition L)
        (Rewriting.emb sourceDerivationSoundnessStrongStep :
          Proposition L) := by
  unfold sourceRestrictedSoundnessStrongStepSentence
  rw [LogicalConnective.HomClass.map_imply]

private theorem emb_sourceCongruentRestrictedSoundnessStrongStepSentence :
    (Rewriting.emb sourceCongruentRestrictedSoundnessStrongStepSentence :
        Proposition L) =
      Arrow.arrow
        (Rewriting.emb (placeholderCongruenceSentence 3 2) : Proposition L)
        (Rewriting.emb sourceRestrictedSoundnessStrongStepSentence :
          Proposition L) := by
  unfold sourceCongruentRestrictedSoundnessStrongStepSentence
  rw [LogicalConnective.HomClass.map_imply]

section Translation

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1] [V↓[ℒₒᵣ] ⊧* Peano]

omit [V↓[ℒₒᵣ] ⊧* Peano] in
private theorem translate_sourceAll {n : ℕ}
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 2 → V)
    (body : Semiproposition L (n + 1)) :
    translateFormula lower parameters (∀⁰ body) =
      ∀⁰ translateFormula lower parameters body := rfl

private theorem translate_sourceDerivationSoundnessPrefix_of_target
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V)
    (target : Bootstrapping.Semiformula V ℒₒᵣ 1)
    (htarget :
      translateFormula lower ![lowerLevel, upperLevel]
          (Rewriting.emb sourceDerivationSoundnessPredicate) = target) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceDerivationSoundnessPrefix) =
      strongPrefixFormula target := by
  have hguard :
      translateFormula lower ![lowerLevel, upperLevel]
          (Rewriting.emb sourceDerivationPrefixGuard) =
        ModelCodedTwoPredicateParameters.translateFormula
          (⊤ : Bootstrapping.Formula V ℒₒᵣ) target ![]
          (Rewriting.emb ModelCodedStrongInduction.sourcePrefixGuard) := by
    rw [sourceDerivationPrefixGuard,
      DynamicTruthTemplateFormula.translate_liftArithmeticFormula]
    simp [ModelCodedStrongInduction.sourcePrefixGuard,
      ModelCodedTwoPredicateParameters.translateFormula,
      ModelCodedTwoPredicateParameters.translateTerm]
    rfl
  have hsourceApplication :
      translateFormula lower ![lowerLevel, upperLevel]
          (Rew.subst ![(#0 : SyntacticSemiterm L 2)] ▹
            (Rewriting.emb sourceDerivationSoundnessPredicate :
              Semiproposition L 1)) =
        target.subst ![Semiterm.bvar (0 : Fin 2)] := by
    rw [ModelCodedPredicateParameters.translateFormula_subst, htarget]
    congr 1
    funext i
    exact Fin.eq_zero i ▸ rfl
  have hgenericApplication :
      ModelCodedTwoPredicateParameters.translateFormula
          (⊤ : Bootstrapping.Formula V ℒₒᵣ) target ![]
          (Rewriting.emb
            (ModelCodedStrongInduction.sourcePredicateAtom (#0))) =
        target.subst ![Semiterm.bvar (0 : Fin 2)] := by
    simp [ModelCodedStrongInduction.sourcePredicateAtom,
      TwoPredicateSourceContextInductionKernel.secondAtom,
      ModelCodedTwoPredicateParameters.translateFormula,
      ModelCodedTwoPredicateParameters.translateTerm]
    congr 1
    funext i
    exact Fin.eq_zero i ▸ rfl
  have hgenericShape :
      strongPrefixFormula target =
        ∀⁰
          (ModelCodedTwoPredicateParameters.translateFormula
              (⊤ : Bootstrapping.Formula V ℒₒᵣ) target ![]
              (∼(Rewriting.emb
                ModelCodedStrongInduction.sourcePrefixGuard)) ⋎
            ModelCodedTwoPredicateParameters.translateFormula
              (⊤ : Bootstrapping.Formula V ℒₒᵣ) target ![]
              (Rewriting.emb
                (ModelCodedStrongInduction.sourcePredicateAtom (#0)))) := by
    rfl
  rw [emb_sourceDerivationSoundnessPrefix, translate_sourceAll,
    hgenericShape, DynamicTruthTemplateFormula.translate_imp,
    ModelCodedTwoPredicateParameters.translateFormula_neg,
    hguard, hsourceApplication, hgenericApplication]
  rfl

/-- The source's bounded prefix is exactly the generic represented
strong-induction prefix instantiated with the translated invariant. -/
theorem translate_sourceDerivationSoundnessPrefix
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceDerivationSoundnessPrefix) =
      strongPrefixFormula
        (derivationSoundnessPredicateFormula lower lowerLevel upperLevel) :=
  translate_sourceDerivationSoundnessPrefix_of_target lower
    lowerLevel upperLevel _ rfl

/-- Exact translated antecedent of the audited source theorem. -/
noncomputable def soundnessLawContextFormula
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) : Bootstrapping.Formula V ℒₒᵣ :=
  translateFormula lower ![lowerLevel, upperLevel]
    (Rewriting.emb sourceSoundnessLawContext)

/-- Exact translated adjacency premise. -/
noncomputable def adjacentLevelsFormula
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) : Bootstrapping.Formula V ℒₒᵣ :=
  translateFormula lower ![lowerLevel, upperLevel]
    (Rewriting.emb sourceAdjacentLevels)

omit [V↓[ℒₒᵣ] ⊧* Peano] in
/-- At a positive lower level the source successor term collapses to the
represented numeral of that successor, so adjacency becomes an equation
between two represented numerals. -/
theorem adjacentLevelsFormula_of_positive
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) (hpositive : 0 < lowerLevel) :
    adjacentLevelsFormula lower lowerLevel upperLevel =
      (Arithmetic.typedNumeral upperLevel ≐
        Arithmetic.typedNumeral (lowerLevel + 1)) := by
  simp [adjacentLevelsFormula, sourceAdjacentLevels,
    ModelCodedPredicateParameters.translateFormula,
    DynamicTruthTemplateFormula.parameterTerm,
    ModelCodedPredicateParameters.translateTerm,
    DynamicTruthLowerExistentialInterface.translate_sourceLowerLevelSuccessor
      (parameters := ![lowerLevel, upperLevel]) hpositive]

omit [V↓[ℒₒᵣ] ⊧* Peano] in
/-- The translated source context is the explicit conjunction of adjacency,
the lower existential law, and the four fields of the new successor. -/
@[simp] theorem translate_sourceSoundnessLawContext
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    soundnessLawContextFormula lower lowerLevel upperLevel =
      (adjacentLevelsFormula lower lowerLevel upperLevel ⋏
        (lowerExistentialLawsFormula lower lowerLevel upperLevel ⋏
          (crossLevelFormula lower lowerLevel upperLevel ⋏
            (shiftInvariantFormula lower lowerLevel upperLevel ⋏
              (substitutionInvariantFormula lower lowerLevel upperLevel ⋏
                axiomSoundnessFormula lower lowerLevel upperLevel))))) := by
  unfold soundnessLawContextFormula adjacentLevelsFormula
  rw [sourceSoundnessLawContext]
  simp only [LogicalConnective.HomClass.map_and,
    ModelCodedPredicateParameters.translateFormula,
    DynamicTruthLowerExistentialInterface.translate_sourceLowerExistentialLawsSentence,
    DynamicTruthCrossLevelFormula.translate_sourceCrossLevelSentence,
    DynamicTruthShiftInvariantFormula.translate_sourceShiftInvariantSentence,
    DynamicTruthSubstitutionInvariantFormula.translate_sourceSubstitutionInvariantSentence,
    DynamicTruthAxiomSoundnessFormula.translate_sourceAxiomSoundnessSentence]

/-- The complete audited source step translates literally to the premise
accepted by `ModelCodedStrongInduction`. -/
theorem translate_sourceRestrictedSoundnessStrongStepSentence
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceRestrictedSoundnessStrongStepSentence) =
      strongStepFormula
        (soundnessLawContextFormula lower lowerLevel upperLevel)
        (derivationSoundnessPredicateFormula
          lower lowerLevel upperLevel) := by
  rw [emb_sourceRestrictedSoundnessStrongStepSentence,
    DynamicTruthTemplateFormula.translate_imp,
    emb_sourceDerivationSoundnessStrongStep, translate_sourceAll,
    DynamicTruthTemplateFormula.translate_imp,
    translate_sourceDerivationSoundnessPrefix, strongStepFormula_eq]
  rfl

theorem translate_sourceCongruentRestrictedSoundnessStrongStepSentence
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb
          sourceCongruentRestrictedSoundnessStrongStepSentence) =
      (translateFormula lower ![lowerLevel, upperLevel]
          (Rewriting.emb (placeholderCongruenceSentence 3 2)) 🡒
        strongStepFormula
          (soundnessLawContextFormula lower lowerLevel upperLevel)
          (derivationSoundnessPredicateFormula
            lower lowerLevel upperLevel)) := by
  rw [emb_sourceCongruentRestrictedSoundnessStrongStepSentence,
    DynamicTruthTemplateFormula.translate_imp,
    translate_sourceRestrictedSoundnessStrongStepSentence]

/-- Compile the audited source theorem and discharge its opaque-relation
congruence premise with PA's represented replacement theorem. -/
noncomputable def compiledRestrictedSoundnessStrongStepProof
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) (hlower : lower.shift = lower) :
    Peano.internalize V ⊢!
      strongStepFormula
        (soundnessLawContextFormula lower lowerLevel upperLevel)
        (derivationSoundnessPredicateFormula
          lower lowerLevel upperLevel) := by
  have hcompiled : Peano.internalize V ⊢!
      translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb
          sourceCongruentRestrictedSoundnessStrongStepSentence) :=
    compilePeanoTemplate lower ![lowerLevel, upperLevel] hlower
      sourceCongruentRestrictedSoundnessStrongStepProof
  rw [translate_sourceCongruentRestrictedSoundnessStrongStepSentence]
    at hcompiled
  exact hcompiled ⨀
    translatedOnePredicateCongruenceProof lower ![lowerLevel, upperLevel]

omit [V↓[ℒₒᵣ] ⊧* Peano] in
/-- The source antecedent is closed under the represented free-variable
shift.  The proof transports the fixed source sentence and never unfolds a
model-coded field. -/
@[simp] theorem soundnessLawContextFormula_shift
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) (hlower : lower.shift = lower) :
    (soundnessLawContextFormula lower lowerLevel upperLevel).shift =
      soundnessLawContextFormula lower lowerLevel upperLevel := by
  unfold soundnessLawContextFormula
  rw [← ModelCodedPredicateParameters.translateFormula_shift
    lower ![lowerLevel, upperLevel] hlower]
  congr 1
  unfold Rewriting.shift Rewriting.emb
  rw [← TransitiveRewriting.comp_app]
  congr 2
  ext x <;> simp

/-- Represented strong induction on derivation codes.  The compiler is
uniform in the possibly nonstandard lower syntax and levels. -/
noncomputable def compiledDerivationSoundnessUniversalProof
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) (hlower : lower.shift = lower) :
    Peano.internalize V ⊢!
      soundnessLawContextFormula lower lowerLevel upperLevel 🡒
        ∀⁰ derivationSoundnessPredicateFormula
          lower lowerLevel upperLevel :=
  ModelCodedStrongInduction.strongInductionProof
    (soundnessLawContextFormula lower lowerLevel upperLevel)
    (derivationSoundnessPredicateFormula lower lowerLevel upperLevel)
    (soundnessLawContextFormula_shift lower lowerLevel upperLevel hlower)
    (derivationSoundnessPredicateFormula_shift
      lower lowerLevel upperLevel hlower)
    (compiledRestrictedSoundnessStrongStepProof
      lower lowerLevel upperLevel hlower)

/-- The complete source context proves restricted consistency at the lower
named level. -/
noncomputable def compiledRestrictedConsistencyProof
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) (hlower : lower.shift = lower) :
    Peano.internalize V ⊢!
      soundnessLawContextFormula lower lowerLevel upperLevel 🡒
        paRestrictedConsistencyFormula lowerLevel :=
  Entailment.C_trans
    (compiledDerivationSoundnessUniversalProof
      lower lowerLevel upperLevel hlower)
    (compiledConsistencyFromSoundnessProof lower lowerLevel upperLevel hlower)

omit [V↓[ℒₒᵣ] ⊧* Peano] in
/-- The lower predicate's existential law does not mention either named
level, so its represented specialization is the same formula at every
parameter pair. -/
theorem lowerExistentialLawsFormula_levels
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3) (a b c d : V) :
    lowerExistentialLawsFormula lower a b =
      lowerExistentialLawsFormula lower c d := by
  have hdomain :
      translateFormula lower ![a, b]
          (Rewriting.emb (DynamicTruthAxiomSoundnessFormula.apply₁
            (liftArithmeticFormula (isUFormula ℒₒᵣ).sigma.val)
            (#2 : ClosedSemiterm L 3))) =
        translateFormula lower ![c, d]
          (Rewriting.emb (DynamicTruthAxiomSoundnessFormula.apply₁
            (liftArithmeticFormula (isUFormula ℒₒᵣ).sigma.val)
            (#2 : ClosedSemiterm L 3))) := by
    simp
    rfl
  have hdomainNeg :
      translateFormula lower ![a, b]
          (∼(Rewriting.emb (DynamicTruthAxiomSoundnessFormula.apply₁
            (liftArithmeticFormula (isUFormula ℒₒᵣ).sigma.val)
            (#2 : ClosedSemiterm L 3)))) =
        translateFormula lower ![c, d]
          (∼(Rewriting.emb (DynamicTruthAxiomSoundnessFormula.apply₁
            (liftArithmeticFormula (isUFormula ℒₒᵣ).sigma.val)
            (#2 : ClosedSemiterm L 3)))) := by
    rw [ModelCodedPredicateParameters.translateFormula_neg,
      ModelCodedPredicateParameters.translateFormula_neg, hdomain]
  simp [DynamicTruthLowerExistentialInterface.lowerExistentialLawsFormula,
    DynamicTruthLowerExistentialInterface.sourceLowerExistentialLawsSentence,
    DynamicTruthLowerExistentialInterface.sourceLowerExistentialBody,
    DynamicTruthLowerExistentialInterface.sourceLowerExistentialCodeWitness,
    DynamicTruthLowerExistentialInterface.sourceLowerExtendedTruthWitness,
    DynamicTruthLowerExistentialInterface.sourceLowerFormulaDomain,
    ModelCodedPredicateParameters.translateFormula,
    ModelCodedPredicateParameters.translateTerm,
    FirstOrder.Semiformula.iff_eq]
  exact hdomainNeg

end Translation

/-! ## Exact dynamic-orbit specialization -/

section Orbit

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-- The complete staged context available to the final direct proof of the
transition out of certificate index `n`. -/
noncomputable def orbitStagedSoundnessContext (n : V) :
    Bootstrapping.Formula V ℒₒᵣ :=
  soundnessContext
    ((compiledDynamicTruthCertificateFamily (V := V)).fields n)
    (orbitCompiledLocalBundleWithQuantifierFreeIntroduction n)
    (orbitSuccessorCrossLevelFormula n)
    (orbitSuccessorShiftInvariantFormula n)
    (orbitSuccessorSubstitutionInvariantFormula n)
    (orbitSuccessorAxiomSoundnessFormula n)

noncomputable def orbitStagedCrossProjection (n : V) :
    Peano.internalize V ⊢!
      orbitStagedSoundnessContext n 🡒 orbitSuccessorCrossLevelFormula n :=
  Entailment.C_trans Entailment.and₁
    (Entailment.C_trans Entailment.and₁
      (Entailment.C_trans Entailment.and₁ Entailment.and₂))

noncomputable def orbitStagedShiftProjection (n : V) :
    Peano.internalize V ⊢!
      orbitStagedSoundnessContext n 🡒
        orbitSuccessorShiftInvariantFormula n :=
  Entailment.C_trans Entailment.and₁
    (Entailment.C_trans Entailment.and₁ Entailment.and₂)

noncomputable def orbitStagedSubstitutionProjection (n : V) :
    Peano.internalize V ⊢!
      orbitStagedSoundnessContext n 🡒
        orbitSuccessorSubstitutionInvariantFormula n :=
  Entailment.C_trans Entailment.and₁ Entailment.and₂

noncomputable def orbitStagedAxiomProjection (n : V) :
    Peano.internalize V ⊢!
      orbitStagedSoundnessContext n 🡒
        orbitSuccessorAxiomSoundnessFormula n :=
  Entailment.and₂

/-- The orbit's lower level is a represented successor, hence positive, so
adjacency is a literal instance of represented equality reflexivity. -/
noncomputable def orbitAdjacentLevelsProof (n : V) :
    Peano.internalize V ⊢!
      adjacentLevelsFormula (truthFormula n) (n + 1) (n + 1 + 1) := by
  rw [adjacentLevelsFormula_of_positive (truthFormula n) (n + 1)
    (n + 1 + 1) (by simp)]
  exact (Arithmetic.eq_refl Peano _).get

/-- The existential law of a positive orbit member, restated at the parameter
pair used by the next transition. -/
noncomputable def orbitLowerExistentialLawsAtProof (m a b : V) :
    Peano.internalize V ⊢!
      lowerExistentialLawsFormula (truthFormula (m + 1)) a b := by
  rw [lowerExistentialLawsFormula_levels (truthFormula (m + 1)) a b
    (m + 1) (m + 1 + 1)]
  exact DynamicTruthLowerExistentialInterface.orbitLowerExistentialLawsProof m

/-- At a positive predecessor index the staged context supplies the four
successor laws, and the two remaining source premises are PA theorems. -/
noncomputable def orbitPositiveSoundnessLawContextProof (m : V) :
    Peano.internalize V ⊢!
      orbitStagedSoundnessContext (m + 1) 🡒
        soundnessLawContextFormula (truthFormula (m + 1))
          (m + 1 + 1) (m + 1 + 1 + 1) := by
  rw [translate_sourceSoundnessLawContext]
  exact Entailment.CK_of_C_of_C
    (Entailment.C_of_conseq (orbitAdjacentLevelsProof (m + 1)))
    (Entailment.CK_of_C_of_C
      (Entailment.C_of_conseq
        (orbitLowerExistentialLawsAtProof m (m + 1 + 1) (m + 1 + 1 + 1)))
      (Entailment.CK_of_C_of_C
        (orbitStagedCrossProjection (m + 1))
        (Entailment.CK_of_C_of_C
          (orbitStagedShiftProjection (m + 1))
          (Entailment.CK_of_C_of_C
            (orbitStagedSubstitutionProjection (m + 1))
            (orbitStagedAxiomProjection (m + 1))))))

/-- Final consistency for a positive-to-next-positive transition. -/
noncomputable def orbitPositiveFinalConsistencyProof (m : V) :
    Peano.internalize V ⊢!
      orbitStagedSoundnessContext (m + 1) 🡒
        paRestrictedConsistencyFormula (m + 1 + 1) :=
  Entailment.C_trans (orbitPositiveSoundnessLawContextProof m)
    (compiledRestrictedConsistencyProof (truthFormula (m + 1))
      (m + 1 + 1) (m + 1 + 1 + 1) (truthFormula_shift (m + 1)))

/-! ## The base transition -/

/-- At the base transition the requested coordinate is restricted
consistency at the standard level one, so it is the quotation of an ordinary
arithmetic sentence. -/
theorem paRestrictedConsistencyFormula_zero_add_one :
    paRestrictedConsistencyFormula ((0 : V) + 1) =
      (⌜(paRestrictedConsistencyTemplate/[(1 : ℕ)] : ArithmeticSentence)⌝ :
        Bootstrapping.Formula V ℒₒᵣ) := by
  apply Bootstrapping.Semiformula.ext
  rw [paRestrictedConsistencyFormula_val]
  rw [show ((0 : V) + 1) = (ORingStructure.numeral 1 : V) by simp]
  exact substNumeral_paRestrictedConsistencyTemplate_eq_quote 1

/-- PA proves restricted consistency at level one by the fixed-level
argument; D1 transports that derivation into an arbitrary ambient model. -/
noncomputable def baseFinalConsistencyAtLevelOneProof :
    Peano.internalize V ⊢! paRestrictedConsistencyFormula ((0 : V) + 1) := by
  rw [paRestrictedConsistencyFormula_zero_add_one]
  exact (internal_provable_of_outer_provable (V := V)
    (pa_proves_paRestrictedConsistencyTemplate_instance 1)).get

/-- The base transition holds outright, so the staged implication is a
weakening. -/
noncomputable def orbitBaseFinalConsistencyProof :
    Peano.internalize V ⊢!
      orbitStagedSoundnessContext (0 : V) 🡒
        paRestrictedConsistencyFormula ((0 : V) + 1) :=
  Entailment.C_of_conseq baseFinalConsistencyAtLevelOneProof

/-! ## The uniform staged proof -/

/-- The sixth staged obligation at an arbitrary, possibly nonstandard,
certificate index.

The two ranks differ only in how the lower predicate's existential law is
obtained, so the statement is uniform in `n` even though the internal case
distinction is not. -/
noncomputable def stagedFinalConsistencyProof (n : V) :
    Peano.internalize V ⊢!
      soundnessContext
          ((compiledDynamicTruthCertificateFamily (V := V)).fields n)
          (orbitCompiledLocalBundleWithQuantifierFreeIntroduction n)
          (orbitSuccessorCrossLevelFormula n)
          (orbitSuccessorShiftInvariantFormula n)
          (orbitSuccessorSubstitutionInvariantFormula n)
          (orbitSuccessorAxiomSoundnessFormula n) 🡒
        paRestrictedConsistencyFormula (n + 1) :=
  (show Peano.internalize V ⊢
      orbitStagedSoundnessContext n 🡒
        paRestrictedConsistencyFormula (n + 1) by
    rcases zero_or_succ n with rfl | ⟨m, rfl⟩
    · exact ⟨orbitBaseFinalConsistencyProof⟩
    · exact ⟨orbitPositiveFinalConsistencyProof m⟩).get

end Orbit

end LeanProofs.BoundedPAConsistency.DynamicTruthRestrictedSoundnessProduction
