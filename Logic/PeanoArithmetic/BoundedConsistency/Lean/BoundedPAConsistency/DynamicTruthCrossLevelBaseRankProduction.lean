import BoundedPAConsistency.DynamicTruthCertificateFieldFamily
import BoundedPAConsistency.FixedLevelTruthCoherence
import BoundedPAConsistency.StagedTruthCertificateProofCompiler
import BoundedPAConsistency.TruthCertificateContextProjection
import Foundation.FirstOrder.Completeness

/-!
# Production compilation of the base cross-level transition

The staged certificate compiler consumes one cross-level induction kernel
per certificate transition.  `DynamicTruthCrossLevelPositiveRankProduction`
supplies every positive-to-next-positive kernel from the derived-level
strong-step source.  That source names only the old hierarchy level and
computes the current and next levels as literal successor terms, so its
translation collapses those terms to represented numerals *only at a
positive old level*: the internal numeral function satisfies
`numeral (x + 1) = numeral x + 1` just for `0 < x`, while `numeral 1` is
the one-symbol code rather than the sum code `numeral 0 + 1`.  At the base
transition the old level is `0`, so the derived translation cannot produce
the represented field `orbitSuccessorCrossLevelFormula 0` syntactically.

No represented induction is needed there either.  Every ingredient of the
base transition is standard syntax: the lower predicate is the quotation of
`levelZeroTruthSyntax` and both hierarchy levels are the standard numerals
`1` and `2`.  Following the convention of `DynamicTruthBaseCertificate`,
this module states the target field as one ordinary arithmetic sentence,
proves it in PA by the level-generic fixed-level coherence theorems, and
transports the derivation into an arbitrary ambient PA model with D1.  The
transported universal theorem is then installed behind the standard
induction-kernel interface expected by the staged compiler.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelBaseRankProduction

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.QuantifierFreeTruth
open LeanProofs.BoundedPAConsistency.FixedLevelTruth
open LeanProofs.BoundedPAConsistency.FixedLevelTruthCoherence
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthQuantifierFreeAnchor
open LeanProofs.BoundedPAConsistency.DynamicTruthCertificateFieldFamily
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters
open LeanProofs.BoundedPAConsistency.PrimitiveRecursiveTruthCertificate
open LeanProofs.BoundedPAConsistency.StagedTruthCertificateProofCompiler
open LeanProofs.BoundedPAConsistency.TruthCertificateContextProjection
open LeanProofs.BoundedPAConsistency.TruthCertificateProofCompiler

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-! ## Standard syntax for the second positive truth level -/

/-- Ordinary syntax for the second positive partial-truth level: one further
successor-certificate layer over the first positive level. -/
noncomputable def levelOneTruthSyntax : ArithmeticSemisentence 3 :=
  standardSuccessorTruthFormula levelZeroTruthSyntax 1 2

/-- The quotation of the second standard level is exactly the model-coded
successor of the first, at the represented numerals `1` and `2`. -/
@[simp] theorem typedQuote_levelOneTruthSyntax :
    (⌜levelOneTruthSyntax⌝ : Bootstrapping.Semiformula V ℒₒᵣ 3) =
      successorTruthFormula levelZeroTruthFormula 1 2 := by
  simp [levelOneTruthSyntax]

set_option maxHeartbeats 1600000 in
/-- Semantic identification of the second standard level.  As with the first
level, only ordinary syntax is unfolded, so Foundation's formula semantics is
legitimate here. -/
@[simp] theorem eval_levelOneTruthSyntax_iff
    (v : Fin 3 → V) :
    levelOneTruthSyntax.Evalb (M := V) v ↔
      SigmaTrue 2 (v 0) (v 1) (v 2) := by
  simp [levelOneTruthSyntax, standardSuccessorTruthFormula,
    standardApply₂, SigmaTrue, levelCode]

/-! ## Standard syntax for the base-successor cross-level field -/

/-- Ordinary Sigma-oriented rank-one domain. -/
noncomputable def standardOneSigmaDomain : ArithmeticSemisentence 3 :=
  standardApply₂ isSigmaCodeDef.val
    (‘1’ : ArithmeticSemiterm Empty 3) (#2)

/-- Ordinary Pi-oriented rank-one domain. -/
noncomputable def standardOnePiDomain : ArithmeticSemisentence 3 :=
  standardApply₂ isPiCodeDef.val
    (‘1’ : ArithmeticSemiterm Empty 3) (#2)

/-- The lower Pi presentation at level one, with the represented negation
witness left explicit exactly as in the model-coded field. -/
noncomputable def standardLevelOneLowerPiTruth : ArithmeticSemisentence 3 :=
  standardOnePiDomain ⋏
    (∃⁰
      (standardApply₂ (negGraph ℒₒᵣ).val (#0) (#3) ⋏
        ∼(standardApply₃ levelZeroTruthSyntax (#1) (#2) (#0))))

/-- Both ordinary rank-one coherence clauses at fixed environments and
formula code. -/
noncomputable def standardBaseSuccessorCrossLevelBody :
    ArithmeticSemisentence 3 :=
  (Arrow.arrow standardOneSigmaDomain
      (LogicalConnective.iff
        (standardApply₃ levelOneTruthSyntax (#0) (#1) (#2))
        (standardApply₃ levelZeroTruthSyntax (#0) (#1) (#2)))) ⋏
    (Arrow.arrow standardOnePiDomain
      (LogicalConnective.iff
        (standardApply₃ levelOneTruthSyntax (#0) (#1) (#2))
        standardLevelOneLowerPiTruth))

/-- Ordinary sentence whose quotation is the exact cross-level field of the
first positive certificate transition. -/
noncomputable def standardBaseSuccessorCrossLevelSentence :
    ArithmeticSentence :=
  ∀⁰ ∀⁰ ∀⁰ standardBaseSuccessorCrossLevelBody

/-- Applying a typed ternary formula to the three ambient bound variables in
their original order is syntactically the identity. -/
@[simp] private theorem typedApply₃_bvars_eq_self
    (S : Bootstrapping.Semiformula V ℒₒᵣ 3) :
    DynamicTruthFormula.apply₃ S
        (Bootstrapping.Semiterm.bvar (0 : Fin 3))
        (Bootstrapping.Semiterm.bvar (1 : Fin 3))
        (Bootstrapping.Semiterm.bvar (2 : Fin 3)) = S := by
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

/-- The explicit negation-graph application used by the model-coded field
syntax is the same closed substitution used by `standardApply₂`. -/
private theorem typedQuote_negGraph_application :
    (⌜((negGraph ℒₒᵣ).val/[#0, #3] :
        ArithmeticSemisentence 4)⌝ :
      Bootstrapping.Semiformula V ℒₒᵣ 4) =
    (⌜(negGraph ℒₒᵣ).val⌝ :
      Bootstrapping.Semiformula V ℒₒᵣ 2).subst
      ![Bootstrapping.Semiterm.bvar (0 : Fin 4),
        Bootstrapping.Semiterm.bvar (3 : Fin 4)] := by
  simpa [standardApply₂] using
    (typedQuote_standardApply₂ (V := V) (negGraph ℒₒᵣ).val
      (#0) (#3))

/-- The ordinary and model-coded presentations of the base-successor
coherence field are literally the same syntax after quotation. -/
@[simp] theorem typedQuote_standardBaseSuccessorCrossLevelSentence :
    (⌜standardBaseSuccessorCrossLevelSentence⌝ :
        Bootstrapping.Formula V ℒₒᵣ) =
      crossLevelFormula levelZeroTruthFormula 1 2 := by
  simp [standardBaseSuccessorCrossLevelSentence,
    standardBaseSuccessorCrossLevelBody,
    standardLevelOneLowerPiTruth, standardOneSigmaDomain,
    standardOnePiDomain, crossLevelFormula,
    crossLevelPredicateFormula, crossLevelBodyFormula,
    sigmaDomainFormula, piDomainFormula, lowerPiTruthFormula,
    typedQuote_negGraph_application]

/-! ## The PA proof and its internal transport -/

/-- PA proves coherence between the first and second positive truth levels
on both oriented rank-one domains.  The semantic argument is the
level-generic fixed-level coherence theorem at level one; it is uniform over
arbitrary PA models and arbitrary, possibly nonstandard, coded formulas and
environments. -/
noncomputable def standardBaseSuccessorCrossLevelProof :
    Peano ⊢! standardBaseSuccessorCrossLevelSentence :=
  (LO.FirstOrder.Arithmetic.complete.{0} Peano _ <| by
    intro M _ hM
    letI : M↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hM
    simp [models_iff, standardBaseSuccessorCrossLevelSentence,
      standardBaseSuccessorCrossLevelBody, standardLevelOneLowerPiTruth,
      standardOneSigmaDomain, standardOnePiDomain,
      standardApply₂, standardApply₃]
    intro p free bound
    constructor
    · intro hs
      have hs' : OrientedHierarchy.IsSigmaCode ℒₒᵣ
          (levelCode (V := M) 1) p := by
        simpa [levelCode] using hs
      simpa [eval_levelOneTruthSyntax_iff,
        eval_levelZeroTruthSyntax_iff] using
        (sigmaTrue_succ_iff_of_isSigmaCode (V := M) 1 hs')
    · intro hp
      have hp' : OrientedHierarchy.IsPiCode ℒₒᵣ
          (levelCode (V := M) 1) p := by
        simpa [levelCode] using hp
      simpa [eval_levelOneTruthSyntax_iff,
        eval_levelZeroTruthSyntax_iff, piTrue_iff] using
        (sigmaTrue_succ_iff_piTrue_of_isPiCode (V := M) 1 hp')).get

/-- Genuine typed PA proof of the exact base-successor cross-level field. -/
noncomputable def baseSuccessorCrossLevelProof :
    Peano.internalize V ⊢! crossLevelFormula levelZeroTruthFormula 1 2 := by
  rw [← typedQuote_standardBaseSuccessorCrossLevelSentence (V := V)]
  exact (internal_provable_of_outer_provable (V := V)
    (show Peano ⊢ standardBaseSuccessorCrossLevelSentence from
      ⟨standardBaseSuccessorCrossLevelProof⟩)).get

/-! ## Exact kernel predicate -/

/-- The unary predicate whose universal closure is the cross-level field of
the certificate at index one.  Its levels are spelled `0 + 1` and
`0 + 1 + 1` so that the closure is definitionally the represented orbit
field at predecessor index zero. -/
noncomputable def baseNextCrossLevelPredicate :
    Bootstrapping.Semiformula V ℒₒᵣ 1 :=
  crossLevelPredicateFormula (truthFormula 0) (0 + 1) (0 + 1 + 1)

/-- Closing the named predicate is definitionally the first positive orbit
field. -/
@[simp] theorem all_baseNextCrossLevelPredicate_eq_orbit :
    (∀⁰ baseNextCrossLevelPredicate (V := V)) =
      orbitSuccessorCrossLevelFormula 0 := by
  rfl

/-- The kernel therefore produces exactly the family's cross-level field at
index one. -/
@[simp] theorem all_baseNextCrossLevelPredicate_eq_crossLevel :
    (∀⁰ baseNextCrossLevelPredicate (V := V)) =
      (compiledDynamicTruthCertificateFamily (V := V)).crossLevel (0 + 1) := by
  rw [compiledDynamicTruthCertificateFamily_crossLevel_succ]
  rfl

/-- At the standard base point the model levels `0 + 1` and `0 + 1 + 1`
are the numerals `1` and `2`, so the kernel predicate is the standard
transition target proved above. -/
theorem baseNextCrossLevelPredicate_eq_levelOne :
    baseNextCrossLevelPredicate (V := V) =
      crossLevelPredicateFormula levelZeroTruthFormula 1 2 := by
  simp [baseNextCrossLevelPredicate, one_add_one_eq_two]

/-- The base kernel predicate has no free variables: its hierarchy levels
are typed numerals and its lower truth predicate is shift-fixed, so internal
`shift` leaves the complete model-coded formula unchanged. -/
@[simp] theorem baseNextCrossLevelPredicate_shift :
    (baseNextCrossLevelPredicate (V := V)).shift =
      baseNextCrossLevelPredicate := by
  unfold baseNextCrossLevelPredicate
  rw [← translate_sourceCrossLevelPredicate (truthFormula 0)
    (0 + 1) (0 + 1 + 1)]
  rw [← ModelCodedPredicateParameters.translateFormula_shift
    (truthFormula 0) ![0 + 1, 0 + 1 + 1] (truthFormula_shift 0)]
  congr 1
  unfold Rewriting.shift Rewriting.emb
  rw [← TransitiveRewriting.comp_app]
  congr 2
  ext x <;> simp

/-- Raw-code form of `baseNextCrossLevelPredicate_shift`, as expected by
`PAInductionKernel.ofUniversalProof`. -/
@[simp] theorem baseNextCrossLevelPredicate_shift_val :
    shift ℒₒᵣ (baseNextCrossLevelPredicate (V := V)).val =
      (baseNextCrossLevelPredicate (V := V)).val := by
  exact congrArg Bootstrapping.Semiformula.val
    baseNextCrossLevelPredicate_shift

/-! ## The base induction kernel -/

/-- The transported standard proof already concludes the complete universal
closure of the base kernel predicate. -/
noncomputable def baseCrossLevelUniversalProof :
    Peano.internalize V ⊢! ∀⁰ baseNextCrossLevelPredicate := by
  rw [baseNextCrossLevelPredicate_eq_levelOne]
  exact baseSuccessorCrossLevelProof

/-- Base analogue of the positive structural universal theorem.  The
antecedent is the certificate's cross-level field at index zero; the base
transition holds outright, so the implication is a weakening. -/
noncomputable def baseCrossLevelStructuralUniversalProof :
    Peano.internalize V ⊢!
      baseCrossLevelFormula 🡒 ∀⁰ baseNextCrossLevelPredicate :=
  Entailment.C_of_conseq baseCrossLevelUniversalProof

/-- Production induction kernel for the base cross-level transition. -/
noncomputable def baseCrossLevelInductionKernel :
    PAInductionKernel (baseCrossLevelFormula (V := V)) :=
  PAInductionKernel.ofUniversalProof
    baseNextCrossLevelPredicate
    baseNextCrossLevelPredicate_shift_val
    baseCrossLevelStructuralUniversalProof

/-! ## Installation under the production staged context -/

/-- At the base certificate transition, the preceding master sentence is the
certificate at index zero.  Its cross-level projection is exactly the
minimal antecedent consumed above; the newly established local field remains
available as the right conjunct of the staged context. -/
noncomputable def proveBaseCrossFromBaseLocalContext :
    Peano.internalize V ⊢!
      localContext
          ((compiledDynamicTruthCertificateFamily (V := V)).fields 0)
          (orbitCompiledLocalBundleWithQuantifierFreeIntroduction 0) 🡒
        baseCrossLevelFormula := by
  unfold localContext
  exact Entailment.C_trans Entailment.and₁ <| by
    simpa only [PATruthCertificateFamily.fields,
      compiledDynamicTruthCertificateFamily_crossLevel_zero] using
      (TruthCertificateFields.proveCrossLevel
        (T := Peano.internalize V)
        ((compiledDynamicTruthCertificateFamily (V := V)).fields 0))

/-- Cross-level induction kernel in the exact context expected by the staged
certificate compiler for the base-to-first-positive transition. -/
noncomputable def stagedBaseCrossLevelInductionKernel :
    PAInductionKernel
      (localContext
        ((compiledDynamicTruthCertificateFamily (V := V)).fields 0)
        (orbitCompiledLocalBundleWithQuantifierFreeIntroduction 0)) :=
  PAInductionKernel.recontextualize
    proveBaseCrossFromBaseLocalContext
    baseCrossLevelInductionKernel

/-- The staged kernel's predicate is the named base kernel predicate, so its
compiled universal closure is the family's cross-level field at index one. -/
@[simp] theorem stagedBaseCrossLevelInductionKernel_predicate :
    (stagedBaseCrossLevelInductionKernel (V := V)).predicate =
      baseNextCrossLevelPredicate := rfl

end LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelBaseRankProduction
