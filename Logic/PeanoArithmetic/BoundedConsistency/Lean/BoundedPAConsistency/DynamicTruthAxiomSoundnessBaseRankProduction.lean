import BoundedPAConsistency.DynamicTruthAxiomSoundnessStructuralSuccessor
import BoundedPAConsistency.DynamicTruthBaseAxiomSoundness
import BoundedPAConsistency.DynamicTruthCertificateFieldFamily
import BoundedPAConsistency.DynamicTruthCrossLevelBaseRankProduction
import BoundedPAConsistency.DynamicTruthSubstitutionInvariantFormula
import BoundedPAConsistency.StagedTruthCertificateProofCompiler
import Foundation.FirstOrder.Completeness

/-!
# Production compilation of the base PA-axiom-soundness transition

The staged certificate compiler consumes one axiom-soundness induction
kernel per certificate transition.  At a positive transition the field is
genuinely model-coded: its truth predicate is a nonstandard member of the
represented orbit, and its lower predicate's Tarski laws are available only
as represented syntax.

At the first transition every ingredient is ordinary arithmetic syntax.  The
lower predicate is the quotation of `levelZeroTruthSyntax`, the new truth
predicate is the quotation of `levelOneTruthSyntax`, and the advertised
quantifier-group bound is the standard numeral `1`.  Following the
convention of `DynamicTruthBaseAxiomSoundness`, this module writes the field
as one ordinary sentence, proves it in PA from fixed-level axiom soundness
at external level one, and transports the derivation into an arbitrary
ambient PA model with the first derivability condition.  The transported
universal theorem is then installed behind the induction-kernel interface
expected by the staged compiler.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessBaseRankProduction

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessStructuralSuccessor
open LeanProofs.BoundedPAConsistency.DynamicTruthBaseAxiomSoundness
open LeanProofs.BoundedPAConsistency.DynamicTruthCertificateFieldFamily
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelBaseRankProduction
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthQuantifierFreeAnchor
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantFormula
open LeanProofs.BoundedPAConsistency.FixedLevelPAAxioms
open LeanProofs.BoundedPAConsistency.FixedLevelTruth
open LeanProofs.BoundedPAConsistency.PrimitiveRecursiveTruthCertificate
open LeanProofs.BoundedPAConsistency.StagedTruthCertificateProofCompiler
open LeanProofs.BoundedPAConsistency.TruthCertificateProofCompiler

/-! ## Standard syntax for the base-successor axiom-soundness field -/

/-- Ordinary syntax saying that the formula code has quantifier-group bound
one.  Within the two-variable body, `#1` is the formula code. -/
noncomputable def standardOneAxiomBoundedDomainFormula :
    ArithmeticSemisentence 2 :=
  standardApply₂ (quantifierBoundedCodeDef ℒₒᵣ).val
    (‘1’ : ArithmeticSemiterm Empty 2) (#1)

/-- The ordinary level-one axiom-soundness implication. -/
noncomputable def standardBaseSuccessorAxiomSoundnessBody :
    ArithmeticSemisentence 2 :=
  Arrow.arrow
    (standardRecognizedPAAxiomFormula ⋏
      (standardOneAxiomBoundedDomainFormula ⋏
        standardAxiomFreeSequenceFormula))
    (standardApply₃ levelOneTruthSyntax
      (‘0’ : ArithmeticSemiterm Empty 2) (#0) (#1))

/-- Ordinary sentence whose quotation is the exact axiom-soundness field of
the first positive certificate transition. -/
noncomputable def standardBaseSuccessorAxiomSoundnessSentence :
    ArithmeticSentence :=
  ∀⁰ ∀⁰ standardBaseSuccessorAxiomSoundnessBody

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-- The ordinary and model-coded presentations of the base-successor
axiom-soundness field are literally the same syntax after quotation. -/
@[simp] theorem typedQuote_standardBaseSuccessorAxiomSoundnessSentence :
    (⌜standardBaseSuccessorAxiomSoundnessSentence⌝ :
        Bootstrapping.Formula V ℒₒᵣ) =
      ∀⁰ axiomSoundnessPredicateFormula
        (successorTruthFormula levelZeroTruthFormula 1 2) 1 := by
  simp [standardBaseSuccessorAxiomSoundnessSentence,
    standardBaseSuccessorAxiomSoundnessBody,
    standardRecognizedPAAxiomFormula,
    standardOneAxiomBoundedDomainFormula,
    standardAxiomFreeSequenceFormula,
    axiomSoundnessPredicateFormula, axiomSoundnessBodyFormula,
    recognizedPAAxiomFormula, axiomBoundedDomainFormula,
    freeSequenceFormula, DynamicTruthFormula.apply₃,
    DynamicTruthAxiomSoundnessFormula.typedSourceZeroTerm]

/-! ## The PA proof and its internal transport -/

/-- Outer PA proves the ordinary base-successor field.  Completeness reduces
the claim to an arbitrary PA model, where the three represented hypotheses
are membership in PA's Delta-one axiom class, quantifier-group boundedness at
level one, and sequencehood.  The level-generic fixed-level theorem supplies
the desired `SigmaTrue 2` conclusion for arbitrary, possibly nonstandard,
codes and environments. -/
noncomputable def standardBaseSuccessorAxiomSoundnessProof :
    Peano ⊢! standardBaseSuccessorAxiomSoundnessSentence :=
  (LO.FirstOrder.Arithmetic.complete.{0} Peano _ <| by
    intro M _ hM
    letI : M↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hM
    simp [models_iff, standardBaseSuccessorAxiomSoundnessSentence,
      standardBaseSuccessorAxiomSoundnessBody,
      standardRecognizedPAAxiomFormula,
      standardOneAxiomBoundedDomainFormula,
      standardAxiomFreeSequenceFormula,
      standardApply₁, standardApply₂, standardApply₃]
    intro p free hp hbounded hfree
    have hbounded' : QuantifierBoundedCode ℒₒᵣ
        (levelCode (V := M) 1) p := by
      apply OrientedHierarchy.quantifierBoundedCode_iff_sigma_or_pi.mpr
      simpa [levelCode] using hbounded
    simpa [eval_levelOneTruthSyntax_iff, levelCode] using
      (sigmaTrue_succ_of_mem_pa_delta1Class (V := M) 1
        hp hbounded' hfree)).get

/-- Genuine typed PA proof of the exact base-successor axiom-soundness
field. -/
noncomputable def baseSuccessorAxiomSoundnessProof :
    Peano.internalize V ⊢!
      ∀⁰ axiomSoundnessPredicateFormula
        (successorTruthFormula levelZeroTruthFormula 1 2) 1 := by
  rw [← typedQuote_standardBaseSuccessorAxiomSoundnessSentence (V := V)]
  exact (internal_provable_of_outer_provable (V := V)
    (show Peano ⊢ standardBaseSuccessorAxiomSoundnessSentence from
      ⟨standardBaseSuccessorAxiomSoundnessProof⟩)).get

/-! ## Exact kernel predicate -/

/-- At the standard base point the model levels `0 + 1` and `0 + 1 + 1` are
the numerals `1` and `2`, so the structural successor's kernel predicate at
index zero is the standard transition target proved above. -/
theorem nextAxiomSoundnessPredicate_zero_eq_levelOne :
    nextAxiomSoundnessPredicate (V := V) 0 =
      axiomSoundnessPredicateFormula
        (successorTruthFormula levelZeroTruthFormula 1 2) 1 := by
  simp [nextAxiomSoundnessPredicate, one_add_one_eq_two]

/-- The transported standard proof already concludes the complete universal
closure of the base kernel predicate. -/
noncomputable def baseAxiomSoundnessUniversalProof :
    Peano.internalize V ⊢! ∀⁰ nextAxiomSoundnessPredicate (0 : V) := by
  rw [nextAxiomSoundnessPredicate_zero_eq_levelOne]
  exact baseSuccessorAxiomSoundnessProof

/-- The base transition holds outright, so its structural implication is a
weakening under an arbitrary staged context. -/
noncomputable def baseAxiomSoundnessStructuralUniversalProof
    (context : Bootstrapping.Formula V ℒₒᵣ) :
    Peano.internalize V ⊢!
      context 🡒 ∀⁰ nextAxiomSoundnessPredicate (0 : V) :=
  Entailment.C_of_conseq baseAxiomSoundnessUniversalProof

/-- Production induction kernel for the base axiom-soundness transition
under an arbitrary staged context. -/
noncomputable def baseAxiomSoundnessInductionKernel
    (context : Bootstrapping.Formula V ℒₒᵣ) :
    PAInductionKernel context :=
  kernelOfStructuralUniversalProof context 0
    (baseAxiomSoundnessStructuralUniversalProof context)

/-! ## Installation under the production staged context -/

/-- Axiom-soundness induction kernel in the exact context expected by the
staged certificate compiler for the base-to-first-positive transition. -/
noncomputable def stagedBaseAxiomSoundnessInductionKernel :
    PAInductionKernel
      (substitutionContext
        ((compiledDynamicTruthCertificateFamily (V := V)).fields 0)
        (orbitCompiledLocalBundleWithQuantifierFreeIntroduction 0)
        (orbitSuccessorCrossLevelFormula 0)
        (orbitSuccessorShiftInvariantFormula 0)
        (orbitSuccessorSubstitutionInvariantFormula 0)) :=
  baseAxiomSoundnessInductionKernel _

/-- The staged kernel's predicate is the structural successor's kernel
predicate at index zero. -/
@[simp] theorem stagedBaseAxiomSoundnessInductionKernel_predicate :
    (stagedBaseAxiomSoundnessInductionKernel (V := V)).predicate =
      nextAxiomSoundnessPredicate 0 := rfl

/-- Closing the kernel predicate is definitionally the first positive orbit
axiom-soundness field. -/
@[simp] theorem all_baseNextAxiomSoundnessPredicate_eq_orbit :
    (∀⁰ nextAxiomSoundnessPredicate (V := V) 0) =
      orbitSuccessorAxiomSoundnessFormula 0 := rfl

/-- The kernel therefore produces exactly the family's axiom-soundness field
at index one. -/
@[simp] theorem all_baseNextAxiomSoundnessPredicate_eq_axiomSound :
    (∀⁰ nextAxiomSoundnessPredicate (V := V) 0) =
      (compiledDynamicTruthCertificateFamily (V := V)).axiomSound (0 + 1) := by
  rw [compiledDynamicTruthCertificateFamily_axiomSound_succ]
  rfl

end LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessBaseRankProduction
