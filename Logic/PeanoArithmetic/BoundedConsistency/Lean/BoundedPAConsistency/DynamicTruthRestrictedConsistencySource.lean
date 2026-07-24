import BoundedPAConsistency.DynamicTruthRestrictedSoundnessPredicate
import BoundedPAConsistency.PrimitiveRecursiveTruthCertificate
import BoundedPAConsistency.TernaryCongruencePrototype

/-!
# From represented derivation soundness to restricted consistency

Strong induction on derivation codes yields the invariant "every restricted
derivation has a true conclusion sequent".  The last certificate field asks
for less: falsity has no restricted derivation at all.

The bridge between the two is the falsity clause of a dynamic truth
successor.  `SuccessorTruth.falsum_iff` reduces the successor's value at the
coded `⊥` to quantifier-free truth, which is refutable outright.  No
hierarchy law, adjacency assumption, or induction is used, so the bridge is
compiled here as one fixed source implication over the opaque ternary
placeholder.

Its arithmetic specialization is exactly the sixth certificate coordinate:
`translateFormula` sends the lifted consistency template applied to the first
named level to `paRestrictedConsistencyFormula` at that level.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthRestrictedConsistencySource

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency
open LeanProofs.BoundedPAConsistency.AbstractSoundness
open LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthCertificateSemantics
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelStrongStepSource
open LeanProofs.BoundedPAConsistency.DynamicTruthRestrictedSoundnessPredicate
open LeanProofs.BoundedPAConsistency.DynamicTruthTemplateFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthTemplateSemantics
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateEqualityQuotient
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters
open LeanProofs.BoundedPAConsistency.PrimitiveRecursiveTruthCertificate
open LeanProofs.BoundedPAConsistency.TernaryCongruencePrototype
open LeanProofs.BoundedPAConsistency.UniformInternalProvability

private abbrev L := DynamicTruthTemplateFormula.SourceLanguage

/-! ## Fixed source syntax -/

/-- Restricted consistency of PA at the first named hierarchy level.  The
unary template is PA's own `Pi`-one consistency formula, so its
specialization is definitionally the family's forced sixth coordinate. -/
noncomputable def sourceRestrictedConsistencySentence : Sentence L :=
  apply₁ (liftArithmeticFormula paRestrictedConsistencyTemplate)
    (parameterTerm 0)

/-- The bridge itself: soundness of every restricted derivation code excludes
a restricted derivation of falsity. -/
noncomputable def sourceConsistencyFromSoundnessSentence : Sentence L :=
  (∀⁰ sourceDerivationSoundnessPredicate) 🡒
    sourceRestrictedConsistencySentence

/-- Equality-safe form submitted to source completeness. -/
noncomputable def sourceCongruentConsistencyFromSoundnessSentence :
    Sentence L :=
  placeholderCongruenceSentence 3 2 🡒
    sourceConsistencyFromSoundnessSentence

/-! ## Source semantics -/

section Semantics

variable {M : Type*}
variable [sourceStructure : Structure L M]
variable [Nonempty M] [ORingStructure M]
variable [Structure.ORing L M]
variable [hPA : M↓[ℒₒᵣ] ⊧* Peano]

local instance : M↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

variable (hArithmeticReduct :
  sourceStructure.lMap (arithmeticHom 3 2) =
    LO.FirstOrder.Arithmetic.standardModel M)

omit [Structure.ORing L M] in
include hArithmeticReduct in
@[simp] theorem eval_sourceRestrictedConsistencySentence :
    sourceRestrictedConsistencySentence.Evalb (M := M) ![] ↔
      RestrictedConsistent Peano (level (M := M) 0) := by
  simp [sourceRestrictedConsistencySentence,
    DynamicTruthCertificateSemantics.eval_apply₁,
    DynamicTruthTemplateSemantics.eval_liftArithmeticFormula
      hArithmeticReduct,
    DynamicTruthCertificateSemantics.eval_parameterTerm,
    paRestrictedConsistencyTemplate]

omit [Structure.ORing L M] in
include hArithmeticReduct in
@[simp] theorem eval_allSourceDerivationSoundnessPredicate :
    (∀⁰ sourceDerivationSoundnessPredicate : Sentence L).Evalb
        (M := M) ![] ↔
      ∀ d : M, RestrictedDerivation Peano (level (M := M) 0) d →
        SequentTrue
          (SuccessorTruth lowerRelation
            (level (M := M) 0) (level (M := M) 1))
          (fstIdx d) := by
  simp [eval_sourceDerivationSoundnessPredicate hArithmeticReduct]

end Semantics

/-! ## The fixed source proof -/

set_option maxHeartbeats 1600000 in
/-- Falsity is excluded by the truth invariant.  Completeness is used only
after the placeholder has been quotiented by its explicit congruence
antecedent, so the argument is sound for arbitrary relation
interpretations. -/
noncomputable def sourceCongruentConsistencyFromSoundnessProof :
    parameterTemplatePeano 3 2 ⊢!
      sourceCongruentConsistencyFromSoundnessSentence := by
  simpa [sourceCongruentConsistencyFromSoundnessSentence] using
    (complete_underPlaceholderCongruence
      sourceConsistencyFromSoundnessSentence
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
        have hmain :
            (∀ d : X, RestrictedDerivation Peano (level (M := X) 0) d →
                SequentTrue
                  (SuccessorTruth lowerRelation
                    (level (M := X) 0) (level (M := X) 1))
                  (fstIdx d)) →
              RestrictedConsistent Peano (level (M := X) 0) := by
          intro hsound hprovable
          rcases hprovable with ⟨d, hfst, hderivation⟩
          have hzeroSeq : Arithmetic.Seq (0 : X) := by
            simpa [emptyset_def] using (seq_empty : Arithmetic.Seq (∅ : X))
          rcases hsound d hderivation 0 hzeroSeq with ⟨p, hp, htrue⟩
          rw [hfst] at hp
          have hpFalsum : p = (qqFalsum : X) := by simpa using hp
          subst hpFalsum
          have hqf := SuccessorTruth.falsum_iff.mp htrue
          simp at hqf
        simpa [models_iff, sourceConsistencyFromSoundnessSentence,
          eval_allSourceDerivationSoundnessPredicate hArithmeticReduct,
          eval_sourceRestrictedConsistencySentence hArithmeticReduct] using
          hmain))

/-! ## Model-coded specialization -/

section Production

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

private theorem emb_sourceConsistencyFromSoundnessSentence :
    (Rewriting.emb sourceConsistencyFromSoundnessSentence : Proposition L) =
      Arrow.arrow
        (∀⁰ (Rewriting.emb sourceDerivationSoundnessPredicate :
          Semiproposition L 1))
        (Rewriting.emb sourceRestrictedConsistencySentence :
          Proposition L) := by
  unfold sourceConsistencyFromSoundnessSentence
  rw [LogicalConnective.HomClass.map_imply, Rewriting.app_all]
  simp only [Rew.q_emb]

private theorem emb_sourceCongruentConsistencyFromSoundnessSentence :
    (Rewriting.emb sourceCongruentConsistencyFromSoundnessSentence :
        Proposition L) =
      Arrow.arrow
        (Rewriting.emb (placeholderCongruenceSentence 3 2) : Proposition L)
        (Rewriting.emb sourceConsistencyFromSoundnessSentence :
          Proposition L) := by
  unfold sourceCongruentConsistencyFromSoundnessSentence
  rw [LogicalConnective.HomClass.map_imply]

/-- The lifted consistency template applied to the first named level
specializes to the exact final certificate coordinate. -/
@[simp] theorem translate_sourceRestrictedConsistencySentence
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceRestrictedConsistencySentence) =
      paRestrictedConsistencyFormula lowerLevel := by
  rw [sourceRestrictedConsistencySentence, translate_apply₁,
    translate_liftArithmeticFormula]
  simp [paRestrictedConsistencyFormula]

@[simp] theorem translate_sourceConsistencyFromSoundnessSentence
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceConsistencyFromSoundnessSentence) =
      ((∀⁰ derivationSoundnessPredicateFormula lower lowerLevel upperLevel) 🡒
        paRestrictedConsistencyFormula lowerLevel) := by
  rw [emb_sourceConsistencyFromSoundnessSentence,
    DynamicTruthTemplateFormula.translate_imp,
    translate_sourceRestrictedConsistencySentence]
  rfl

theorem translate_sourceCongruentConsistencyFromSoundnessSentence
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceCongruentConsistencyFromSoundnessSentence) =
      (translateFormula lower ![lowerLevel, upperLevel]
          (Rewriting.emb (placeholderCongruenceSentence 3 2)) 🡒
        ((∀⁰ derivationSoundnessPredicateFormula
            lower lowerLevel upperLevel) 🡒
          paRestrictedConsistencyFormula lowerLevel)) := by
  rw [emb_sourceCongruentConsistencyFromSoundnessSentence,
    DynamicTruthTemplateFormula.translate_imp,
    translate_sourceConsistencyFromSoundnessSentence]

/-- Compile the fixed bridge and discharge its congruence premise with PA's
represented replacement theorem. -/
noncomputable def compiledConsistencyFromSoundnessProof
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) (hlower : lower.shift = lower) :
    Peano.internalize V ⊢!
      (∀⁰ derivationSoundnessPredicateFormula lower lowerLevel upperLevel) 🡒
        paRestrictedConsistencyFormula lowerLevel := by
  have hcompiled : Peano.internalize V ⊢!
      translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceCongruentConsistencyFromSoundnessSentence) :=
    compilePeanoTemplate lower ![lowerLevel, upperLevel] hlower
      sourceCongruentConsistencyFromSoundnessProof
  rw [translate_sourceCongruentConsistencyFromSoundnessSentence] at hcompiled
  exact hcompiled ⨀
    translatedOnePredicateCongruenceProof
      lower ![lowerLevel, upperLevel]

end Production

end LeanProofs.BoundedPAConsistency.DynamicTruthRestrictedConsistencySource
