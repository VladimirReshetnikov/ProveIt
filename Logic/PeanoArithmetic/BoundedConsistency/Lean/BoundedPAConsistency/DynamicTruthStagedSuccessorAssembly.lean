import BoundedPAConsistency.DynamicTruthAxiomSoundnessBaseRankProduction
import BoundedPAConsistency.DynamicTruthAxiomSoundnessPositiveRankProduction
import BoundedPAConsistency.DynamicTruthCrossLevelBaseRankProduction
import BoundedPAConsistency.DynamicTruthCrossLevelPositiveRankProduction
import BoundedPAConsistency.DynamicTruthRestrictedSoundnessProduction
import BoundedPAConsistency.DynamicTruthShiftInvariantPositiveRankProduction
import BoundedPAConsistency.DynamicTruthSubstitutionInvariantPositiveRankProduction
import BoundedPAConsistency.StagedDirectTruthCertificatePackage

/-!
# Assembly of the staged successor step

Four of the six staged slots are uniform in the certificate index: the
augmented local bundle and its proof, the shift- and substitution-invariance
kernels, and the final consistency implication.  The cross-level and
axiom-soundness slots are not.  Their represented derived-level sources
collapse successor terms to numerals only at a positive old level, because the
internal numeral function satisfies `numeral (x + 1) = numeral x + 1` just for
`0 < x`.  Each therefore has a separate standard-syntax production out of index
zero.

The assembly consequently splits the ambient model element once, at the
outermost level, and builds a complete step on each branch.  Everything except
the two rank-dependent kernels is shared, so the branch-independent work is
factored into a single builder that takes those two kernels together with the
equations identifying their universal closures with the orbit fields.

`PAStagedTruthCertificateStep` states each slot's context in terms of the
*closures of the preceding kernels*, while every production module states its
kernel in terms of the corresponding orbit field.  These agree definitionally,
but the terms involved are represented syntax, so asking the elaborator to
confirm it inside a structure literal is prohibitively expensive.  The
transport combinator below moves a kernel along a proved context equation
instead, and its projection equation keeps the later slots' contexts in the
orbit form, so every equation supplied to it stays a small rewrite between
named formulas.
-/

namespace LeanProofs.BoundedPAConsistency.TruthCertificateProofCompiler.PAInductionKernel

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1] [V↓[ℒₒᵣ] ⊧* Peano]

/-- Move an induction kernel along an equation between its context and
another formula.  The stored predicate, and hence the compiled conclusion, is
unchanged. -/
noncomputable def ofEq {context context' : Bootstrapping.Formula V ℒₒᵣ}
    (h : context = context')
    (kernel : PAInductionKernel context) :
    PAInductionKernel context' :=
  h ▸ kernel

omit [V↓[ℒₒᵣ] ⊧* Peano] in
/-- Transport leaves the kernel's predicate, and therefore the field it
contributes to the successor certificate, completely untouched. -/
@[simp] theorem ofEq_predicate {context context' : Bootstrapping.Formula V ℒₒᵣ}
    (h : context = context') (kernel : PAInductionKernel context) :
    (ofEq h kernel).predicate = kernel.predicate := by
  cases h
  rfl

end LeanProofs.BoundedPAConsistency.TruthCertificateProofCompiler.PAInductionKernel

namespace LeanProofs.BoundedPAConsistency.DynamicTruthStagedSuccessorAssembly

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessBaseRankProduction
open LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessPositiveRankProduction
open LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessStructuralSuccessor
open LeanProofs.BoundedPAConsistency.DynamicTruthCertificateFieldFamily
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelBaseRankProduction
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelPositiveRankProduction
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelStructuralSuccessor
open LeanProofs.BoundedPAConsistency.DynamicTruthQuantifierFreeAnchor
open LeanProofs.BoundedPAConsistency.DynamicTruthRestrictedSoundnessProduction
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantPositiveRankProduction
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantStructuralSuccessor
open LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantPositiveRankProduction
open LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantStructuralSuccessor
open LeanProofs.BoundedPAConsistency.PrimitiveRecursiveTruthCertificate
open LeanProofs.BoundedPAConsistency.StagedDirectTruthCertificatePackage
open LeanProofs.BoundedPAConsistency.StagedTruthCertificateProofCompiler
open LeanProofs.BoundedPAConsistency.TruthCertificateProofCompiler

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-! ## Closures of the two uniform production kernels

Each production installs its kernel by `recontextualize`, which copies the
predicate verbatim, so reading the predicate off a staged kernel is a
projection.  Naming the resulting closure equations keeps every context
rewrite below a rewrite between named orbit formulas. -/

/-- The staged shift-invariance kernel carries the structural successor's
named predicate. -/
@[simp] theorem stagedShiftInvariantInductionKernel_predicate (n : V) :
    (stagedShiftInvariantInductionKernel (V := V) n).predicate =
      nextShiftInvariantPredicate n := rfl

/-- Its closure is therefore the next positive shift-invariance orbit
field. -/
theorem all_stagedShiftInvariantInductionKernel_predicate (n : V) :
    (∀⁰ (stagedShiftInvariantInductionKernel (V := V) n).predicate) =
      orbitSuccessorShiftInvariantFormula n := by
  rw [stagedShiftInvariantInductionKernel_predicate,
    all_nextShiftInvariantPredicate_eq_orbit]

/-- The staged substitution-invariance kernel carries the structural
successor's named predicate. -/
@[simp] theorem stagedSubstitutionInvariantInductionKernel_predicate (n : V) :
    (stagedSubstitutionInvariantInductionKernel (V := V) n).predicate =
      nextSubstitutionInvariantPredicate n := rfl

/-- Its closure is therefore the next positive substitution-invariance orbit
field. -/
theorem all_stagedSubstitutionInvariantInductionKernel_predicate (n : V) :
    (∀⁰ (stagedSubstitutionInvariantInductionKernel (V := V) n).predicate) =
      orbitSuccessorSubstitutionInvariantFormula n := by
  rw [stagedSubstitutionInvariantInductionKernel_predicate,
    all_nextSubstitutionInvariantPredicate_eq_orbit]

/-- The positive-rank cross-level kernel carries the structural successor's
named predicate. -/
@[simp] theorem stagedPositiveCrossLevelInductionKernel_predicate (n : V) :
    (stagedPositiveCrossLevelInductionKernel (V := V) n).predicate =
      nextCrossLevelPredicate n := rfl

/-! ## The branch-independent builder -/

/-- A complete staged successor step out of certificate index `n`, given the
two rank-dependent kernels and the equations identifying their universal
closures with the corresponding orbit fields.

The three remaining kernels and the two direct proofs are uniform in `n`, so
this builder contains the whole shape of a successor transition.  Every
context adjustment is a transport along an equation between named formulas;
no represented syntax is ever unfolded. -/
noncomputable def stagedStepOfKernels (n : V)
    (crossLevelKernel : PAInductionKernel
      (localContext
        ((compiledDynamicTruthCertificateFamily (V := V)).fields n)
        (orbitCompiledLocalBundleWithQuantifierFreeIntroduction n)))
    (hcrossLevel : (∀⁰ crossLevelKernel.predicate) =
      orbitSuccessorCrossLevelFormula n)
    (axiomSoundKernel : PAInductionKernel
      (substitutionContext
        ((compiledDynamicTruthCertificateFamily (V := V)).fields n)
        (orbitCompiledLocalBundleWithQuantifierFreeIntroduction n)
        (orbitSuccessorCrossLevelFormula n)
        (orbitSuccessorShiftInvariantFormula n)
        (orbitSuccessorSubstitutionInvariantFormula n)))
    (haxiomSound : (∀⁰ axiomSoundKernel.predicate) =
      orbitSuccessorAxiomSoundnessFormula n) :
    PAStagedTruthCertificateStep
      ((compiledDynamicTruthCertificateFamily (V := V)).fields n) where
  localStep := orbitCompiledLocalBundleWithQuantifierFreeIntroduction n
  proveLocalStep :=
    Entailment.C_of_conseq
      (orbitCompiledLocalBundleWithQuantifierFreeIntroductionProof n)
  crossLevel := crossLevelKernel
  shiftInvariant :=
    PAInductionKernel.ofEq (by simp only [hcrossLevel])
      (stagedShiftInvariantInductionKernel n)
  substitutionInvariant :=
    PAInductionKernel.ofEq
      (by
        simp only [PAInductionKernel.ofEq_predicate,
          all_stagedShiftInvariantInductionKernel_predicate, hcrossLevel])
      (stagedSubstitutionInvariantInductionKernel n)
  axiomSound :=
    PAInductionKernel.ofEq
      (by
        simp only [PAInductionKernel.ofEq_predicate,
          all_stagedShiftInvariantInductionKernel_predicate,
          all_stagedSubstitutionInvariantInductionKernel_predicate,
          hcrossLevel])
      axiomSoundKernel
  finalConsistency := paRestrictedConsistencyFormula (n + 1)
  proveFinalConsistency := by
    simp only [PAInductionKernel.ofEq_predicate,
      all_stagedShiftInvariantInductionKernel_predicate,
      all_stagedSubstitutionInvariantInductionKernel_predicate,
      hcrossLevel, haxiomSound]
    exact stagedFinalConsistencyProof n

/-- The builder's public six-field target is exactly the concrete family at
the next index.  The final coordinate matches because the builder proves the
restricted-consistency formula that `PATruthCertificateFamily.fields` forces
into that slot. -/
theorem stagedStepOfKernels_target (n : V)
    (crossLevelKernel : PAInductionKernel
      (localContext
        ((compiledDynamicTruthCertificateFamily (V := V)).fields n)
        (orbitCompiledLocalBundleWithQuantifierFreeIntroduction n)))
    (hcrossLevel : (∀⁰ crossLevelKernel.predicate) =
      orbitSuccessorCrossLevelFormula n)
    (axiomSoundKernel : PAInductionKernel
      (substitutionContext
        ((compiledDynamicTruthCertificateFamily (V := V)).fields n)
        (orbitCompiledLocalBundleWithQuantifierFreeIntroduction n)
        (orbitSuccessorCrossLevelFormula n)
        (orbitSuccessorShiftInvariantFormula n)
        (orbitSuccessorSubstitutionInvariantFormula n)))
    (haxiomSound : (∀⁰ axiomSoundKernel.predicate) =
      orbitSuccessorAxiomSoundnessFormula n) :
    (stagedStepOfKernels n crossLevelKernel hcrossLevel
        axiomSoundKernel haxiomSound).target =
      (compiledDynamicTruthCertificateFamily (V := V)).fields (n + 1) := by
  simp only [PAStagedTruthCertificateStep.target, stagedStepOfKernels,
    PATruthCertificateFamily.fields,
    PAInductionKernel.ofEq_predicate,
    all_stagedShiftInvariantInductionKernel_predicate,
    all_stagedSubstitutionInvariantInductionKernel_predicate,
    hcrossLevel, haxiomSound,
    compiledDynamicTruthCertificateFamily_localStep_succ,
    compiledDynamicTruthCertificateFamily_crossLevel_succ,
    compiledDynamicTruthCertificateFamily_shiftInvariant_succ,
    compiledDynamicTruthCertificateFamily_substitutionInvariant_succ,
    compiledDynamicTruthCertificateFamily_axiomSound_succ]

/-- Raw-code form of the builder's target equality, as required by the
staged package relation. -/
theorem stagedStepOfKernels_target_val (n : V)
    (crossLevelKernel : PAInductionKernel
      (localContext
        ((compiledDynamicTruthCertificateFamily (V := V)).fields n)
        (orbitCompiledLocalBundleWithQuantifierFreeIntroduction n)))
    (hcrossLevel : (∀⁰ crossLevelKernel.predicate) =
      orbitSuccessorCrossLevelFormula n)
    (axiomSoundKernel : PAInductionKernel
      (substitutionContext
        ((compiledDynamicTruthCertificateFamily (V := V)).fields n)
        (orbitCompiledLocalBundleWithQuantifierFreeIntroduction n)
        (orbitSuccessorCrossLevelFormula n)
        (orbitSuccessorShiftInvariantFormula n)
        (orbitSuccessorSubstitutionInvariantFormula n)))
    (haxiomSound : (∀⁰ axiomSoundKernel.predicate) =
      orbitSuccessorAxiomSoundnessFormula n) :
    (stagedStepOfKernels n crossLevelKernel hcrossLevel
          axiomSoundKernel haxiomSound).target.sentence.val =
      (compiledDynamicTruthCertificateFamily (V := V)).code (n + 1) := by
  rw [PATruthCertificateFamily.code]
  exact congrArg (fun F : TruthCertificateFields (V := V) ↦ F.sentence.val)
    (stagedStepOfKernels_target n crossLevelKernel hcrossLevel
      axiomSoundKernel haxiomSound)

/-! ## The two ranks -/

/-- Closure equation for the base-rank cross-level kernel. -/
theorem all_stagedBaseCrossLevelInductionKernel_predicate :
    (∀⁰ (stagedBaseCrossLevelInductionKernel (V := V)).predicate) =
      orbitSuccessorCrossLevelFormula 0 := by
  rw [stagedBaseCrossLevelInductionKernel_predicate,
    all_baseNextCrossLevelPredicate_eq_orbit]

/-- Closure equation for the base-rank axiom-soundness kernel. -/
theorem all_stagedBaseAxiomSoundnessInductionKernel_predicate :
    (∀⁰ (stagedBaseAxiomSoundnessInductionKernel (V := V)).predicate) =
      orbitSuccessorAxiomSoundnessFormula 0 := by
  rw [stagedBaseAxiomSoundnessInductionKernel_predicate,
    all_baseNextAxiomSoundnessPredicate_eq_orbit]

/-- Closure equation for the positive-rank cross-level kernel. -/
theorem all_stagedPositiveCrossLevelInductionKernel_predicate (m : V) :
    (∀⁰ (stagedPositiveCrossLevelInductionKernel (V := V) m).predicate) =
      orbitSuccessorCrossLevelFormula (m + 1) := by
  rw [stagedPositiveCrossLevelInductionKernel_predicate,
    all_nextCrossLevelPredicate_eq_orbit]

/-- Closure equation for the positive-rank axiom-soundness kernel. -/
theorem all_stagedPositiveAxiomSoundnessInductionKernel_predicate (m : V) :
    (∀⁰ (stagedPositiveAxiomSoundnessInductionKernel (V := V) m).predicate) =
      orbitSuccessorAxiomSoundnessFormula (m + 1) := by
  rw [stagedPositiveAxiomSoundnessInductionKernel_predicate,
    all_nextAxiomSoundnessPredicate_eq_orbit]

/-- The staged successor step out of the base certificate. -/
noncomputable def baseStagedStep :
    PAStagedTruthCertificateStep
      ((compiledDynamicTruthCertificateFamily (V := V)).fields 0) :=
  stagedStepOfKernels 0 stagedBaseCrossLevelInductionKernel
    all_stagedBaseCrossLevelInductionKernel_predicate
    stagedBaseAxiomSoundnessInductionKernel
    all_stagedBaseAxiomSoundnessInductionKernel_predicate

/-- The staged successor step out of a positive certificate index. -/
noncomputable def positiveStagedStep (m : V) :
    PAStagedTruthCertificateStep
      ((compiledDynamicTruthCertificateFamily (V := V)).fields (m + 1)) :=
  stagedStepOfKernels (m + 1) (stagedPositiveCrossLevelInductionKernel m)
    (all_stagedPositiveCrossLevelInductionKernel_predicate m)
    (stagedPositiveAxiomSoundnessInductionKernel m)
    (all_stagedPositiveAxiomSoundnessInductionKernel_predicate m)

/-! ## The successor obligation of the staged package -/

/-- Every certificate index of the concrete dynamic truth family admits a
dependency-ordered successor step whose public target is the family's next
master certificate.

This is the last obligation of the staged direct package: the base
certificate and the master-code graph are already available, so the
model-internal restricted-consistency proof selector follows. -/
theorem compiledDynamicTruthCertificateFamily_hasStagedSuccessor :
    HasStagedTruthCertificateSuccessor
      (compiledDynamicTruthCertificateFamily (V := V)) := by
  intro n
  rcases zero_or_succ n with rfl | ⟨m, rfl⟩
  · exact ⟨baseStagedStep, stagedStepOfKernels_target_val _ _ _ _ _⟩
  · exact ⟨positiveStagedStep m, stagedStepOfKernels_target_val _ _ _ _ _⟩

end LeanProofs.BoundedPAConsistency.DynamicTruthStagedSuccessorAssembly
