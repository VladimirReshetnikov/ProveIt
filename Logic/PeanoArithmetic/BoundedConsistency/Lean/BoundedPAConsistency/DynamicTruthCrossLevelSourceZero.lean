import BoundedPAConsistency.DynamicTruthCrossLevelSourceTemplate
import BoundedPAConsistency.FinFunext
import Foundation.FirstOrder.Completeness

/-!
# Zero case for the structural cross-level source invariant

The structural induction invariant is guarded by the Sigma- and Pi-oriented
formula-code domains.  At the induction base its formula-code argument is
zero, which is not the code of a formula.  Consequently both guarded clauses
hold independently of the two predicate placeholders and of the prior
cross-level context.

This file packages that observation as the exact fixed source derivation
required by `TwoPredicateSourceContextInductionKernel.Template.proveZero`.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceZero

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateParameters
open LeanProofs.BoundedPAConsistency.TwoPredicateSourceContextInductionKernel
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceTemplate

/-- Under two quantifiers, the original unary argument is de Bruijn index
two.  This small normalization lemma keeps the semantic base-case proof from
depending on reduction details of numeral notation for `Fin 3`. -/
private lemma subst_q_q_bvar_two {L : Language} {ξ : Type*}
    (t : Semiterm L ξ 0) :
    (Rew.subst ![t]).q.q (#2 : Semiterm L ξ 3) =
      Rew.bShift (Rew.bShift t) := by
  change (Rew.subst ![t]).q.q
    (#(Fin.succ (Fin.succ (0 : Fin 1)))) = _
  rw [Rew.q_bvar_succ, Rew.q_bvar_succ, Rew.subst_bvar]
  simp

/-- Arithmetic says uniformly in the hierarchy level that formula code zero
belongs to neither oriented formula-code domain. -/
noncomputable def arithmeticZeroDomainsSentence : ArithmeticSentence :=
  ∀⁰
    (∼(isSigmaCodeDef.val/[
        #0, (‘0’ : ArithmeticSemiterm Empty 1)]) ⋏
      ∼(isPiCodeDef.val/[
        #0, (‘0’ : ArithmeticSemiterm Empty 1)]))

/-- PA proves the elementary coding fact used by the structural base case. -/
noncomputable def arithmeticZeroDomainsProof :
    Peano ⊢! arithmeticZeroDomainsSentence :=
  (LO.FirstOrder.Arithmetic.complete.{0} Peano _ <| by
    intro M _ hPA
    letI : M↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA
    simp [models_iff, arithmeticZeroDomainsSentence,
      Semiformula.eval_substs, OrientedHierarchy.IsSigmaCode,
      OrientedHierarchy.IsPiCode]).get

/-- Lift the arithmetic coding fact into the source language.  This proof is
obtained by language transport; the extra predicates and named constants do
not occur in the transported sentence. -/
noncomputable def liftedArithmeticZeroDomainsProof :
    twoPredicateParameterPeano 3 3 3 ⊢!
      arithmeticZeroDomainsSentence.lMap (arithmeticHom 3 3 3) :=
  (Theory.Proof.small_complete <|
    lMap_models_lMap (Theory.Proof.sound
      (show Peano ⊢ arithmeticZeroDomainsSentence from
        ⟨arithmeticZeroDomainsProof⟩))).get

/-- The literal base sentence expected by the structural source-context
induction template. -/
noncomputable def sourceZeroSentence : Sentence SourceLanguage :=
  zeroSentence sourcePriorCrossLevelContext
    sourceNextCrossLevelInvariant

/-- A fixed lifted-PA proof of the base case.  Semantically, code zero cannot
belong to either oriented formula-code domain, so both implications in the
invariant are vacuous. -/
noncomputable def sourceZeroProof :
    twoPredicateParameterPeano 3 3 3 ⊢! sourceZeroSentence :=
  (Theory.Proof.small_complete <| consequence_iff.mpr fun _ ↦ by
    simp [models_iff, sourceZeroSentence, zeroSentence,
      sourceNextCrossLevelInvariant, sourceNextCrossLevelBody,
      sourceCurrentSigmaDomain, sourceCurrentPiDomain,
      apply₂, liftArithmeticFormula, zeroTerm, levelTerm,
      Semiformula.eval_rew, Semiformula.eval_lMap]
    intro _ambient _structure hmodels _priorContext bound free
    letI : Nonempty _ := ⟨_ambient⟩
    have hzero := models_of_provable hmodels
      (show twoPredicateParameterPeano 3 3 3 ⊢
          arithmeticZeroDomainsSentence.lMap (arithmeticHom 3 3 3) from
        ⟨liftedArithmeticZeroDomainsProof⟩)
    simp [models_iff, arithmeticZeroDomainsSentence,
      Semiformula.eval_rew, Semiformula.eval_lMap] at hzero
    let currentLevel : _ :=
      (namedParameterTerm (arity₀ := 3) (arity₁ := 3) (count := 3)
        (n := 2) (1 : Fin 3)).val ![free, bound] Empty.elim
    have hzeroAt := hzero currentLevel
    constructor
    · intro hdomain
      exfalso
      apply hzeroAt.1
      convert hdomain using 1
      congr 1
      refine funext_fin2 ?_ ?_
      · simp only [Function.comp_def, Rew.subst_bvar]
        simp [currentLevel, namedParameterTerm, Matrix.empty_eq]
      · simp [Function.comp_def]
        rw [subst_q_q_bvar_two]
        simp [FirstOrder.Semiterm.val_bShift,
          FirstOrder.Semiterm.val_lMap, Matrix.empty_eq]
    · intro hdomain
      exfalso
      apply hzeroAt.2
      convert hdomain using 1
      congr 1
      refine funext_fin2 ?_ ?_
      · simp only [Function.comp_def, Rew.subst_bvar]
        simp [currentLevel, namedParameterTerm, Matrix.empty_eq]
      · simp [Function.comp_def]
        rw [subst_q_q_bvar_two]
        simp [FirstOrder.Semiterm.val_bShift,
          FirstOrder.Semiterm.val_lMap, Matrix.empty_eq]).get

end LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceZero
