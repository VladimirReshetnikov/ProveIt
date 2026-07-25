import ZFCinPA.EnlargedFields

/-!
# The local-step field transfers under the enlarged certificate

`ZFCinPA.LocalStepDerivation.exclusivity_not_step_transferable` showed that
the **five**-field antecedent does not carry the `localStep` field one level
up, and `ZFCinPA.EnlargedFields.exclusivity_step` showed that the enlarged
(seven-field) antecedent does carry its hard conjunct, *given* the internal
code-induction hypothesis.  This module states and proves the composite:
the whole `localStep` field, both conjuncts, at the closure level over an
arbitrary previous level.

It is deliberately stated in goal 2's abstract closure vocabulary —
`BoundedZFCConsistency.LevelClosed`/`LevelJustified` with the previous level
an arbitrary ternary relation `L` — which is exactly the generality an
abstract interpretation of the two source placeholders provides.  So
`localStepLaws_step` is the **semantic half** of the successor obligation
for the first field: what remains between it and
`StagedSuccessor.ZFCSuccessorImplications` is the evaluation bridge from
the source formulas of `ZFCinPA.SuccessorSources` to these predicates, plus
the discharge of the two hypotheses recorded below.

## The exact antecedent

`localStepLaws_step` consumes, at the previous level `L` and bound `b`:

* `hprev` — the previous level's own `localStep` field (`LocalStepLaws`);
* `hL` — `EnlargedFields.LevelLaws`, i.e. exclusivity, decidedness, and the
  two **new** fields `tarskiElim`/`tarskiIntro`;
* `hind` — `EnlargedFields.CodeInduction` at `StepGood`, the honest cost
  recorded in `EnlargedFields`' header: a Separation instance for a
  *placeholder* formula, to be discharged after translation by
  `ZFCinPA.SeparationKernel`;
* `hb` — **`b ∈ ω`**.

The last hypothesis is not optional and is *not* implied by any certificate
field.  Every rank-arithmetic lemma the transfer consumes
(`LevelCollapse.piBounded_imp`, `sigmaBounded_and`, `piBounded_all`,
`sigmaBounded_ex`, `piBounded_of_sigmaBounded_all_succ`,
`sigmaBounded_of_piBounded_ex_succ`, and
`UniverseTruthLevel.quantBounded_of_piBounded`) carries `mem b (omegaV H)`
as an explicit hypothesis, and `EnlargedFields.stepGood_of_levelLaws`
therefore does too.  In the source template the bound is the numeral
placeholder, whose interpretation is *opaque*: a template structure may
interpret `Num` by any set whatsoever.  So the source sentence has to carry
"every `Num` is a natural number" as a further antecedent, to be discharged
after translation, where `Num` has become `numChainCode x`.  This is a
genuine additional obligation, and it is recorded here rather than
discovered later.

Nothing in this module is assumed anywhere; `localStepLaws_levelSat`
records that the statement is true of goal 2's real hierarchy, so the
abstraction is not vacuous.

## What still separates this from a source derivation

`localStepLaws_step` settles the *mathematics* of the successor step for
the first field.  Turning it into
`templateZFC 2 levelArities ⊢! (congruence ⋏ side conditions) 🡒 srcLocalStepStep`
through `SetPlaceholderQuotient.complete_underSetPlaceholderCongruence`
needs an **evaluation bridge** that this project does not yet have: the
tool's hypothesis quantifies over arbitrary template structures
`X ⊧* templateZFC 2 ![1, 2]` with genuine equality, and the source formulas
of `ZFCinPA.SuccessorSources` have to be *evaluated* there.  Concretely:

1. from `X ⊧* templateZFC k arities` and `Structure.Eq`, identify the
   `ℒₛₑₜ` reduct with `SetTheory.standardStructure` of the induced
   membership (`SetTheory.standardStructure_unique`), obtain
   `X↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖` as in
   `SetPlaceholderQuotient.models_fullEquality`, and extract goal 2's
   nine-axiom bundle by `ZFCinPA.zfcAxioms_of_models`;
2. evaluate `liftP φ` as `SetTheory.Sat` of `φ` (`ZFCinPA.eval_toSet`) and
   the placeholder atoms as the structure's two relations `Num`, `Clos`;
3. unfold `srcLvlInstP`, `srcLevelSat`, `srcNumChainSucc`, `srcJustRow`,
   `srcAllClause`, `srcExClause`, `srcClosStep`, `srcLevelSatSucc` into
   `LevelClosed`/`LevelJustified` over the induced previous level
   `LS₁ c e b :≡ ∃ n C, Num n ∧ Clos n C ∧ ⟨c, e, b⟩ ∈ C`, matching each
   fixed leaf against its `Sat` spec (`fTripleMemF_spec`, `fNumF_spec`,
   `fUnivEnvF_spec`, `fLevelImpF_spec`, …);
4. the same for the Tarski rows of `ZFCinPA.TarskiSources`, whose source
   readings and translation identities are already proved there;
5. express `EnlargedFields.StepGood` and its induction instance as source
   formulas, so that `CodeInduction` and the `ω`-membership of the numeral
   placeholder become source antecedents dischargeable after translation
   (`ZFCinPA.SeparationKernel.zfcSeparationProofOfShiftFixed` for the
   former).

Item 3 is the bulk: `srcJustRow`'s evaluation has to reproduce the
six-disjunct `LevelJustified` definition slot by slot.  Nothing above is
assumed anywhere in the project, and nothing here weakens
`StagedSuccessor.ZFCSuccessorImplications`.
-/

set_option autoImplicit false

namespace LeanProofs
namespace ZFCinPA
namespace LocalStepTransfer

open BoundedZFCConsistency
open EnlargedFields
open SetTheory (ZFAxioms vempty omegaV vsucc)

universe u

variable {W : Type u} {mem : W → W → Prop}

/-! ## The local-step field, abstractly

This is the semantic reading of `CertificateFields.localStepF` at a single
level: the two conjuncts of `ZFCinPA.LocalStepSuccessor.srcLocalStep`, with
the level-truth predicate an arbitrary ternary relation. -/

/-- **The local polarity laws at one level.**  Conjunct 1: the falsity code
is never Sigma-true.  Conjunct 2: a form code is never both Sigma-true and
Pi-false. -/
structure LocalStepLaws (H : ZFAxioms mem) (S : W → W → W → Prop) : Prop where
  /-- Conjunct 1, goal-2 counterpart `sigmaTrue_bot`. -/
  botNotSigma : ∀ e, IsUnivEnv H e → ¬ S (botC H) e (natV H 1)
  /-- Conjunct 2, goal-2 counterpart `sigmaTrue_not_piFalse`. -/
  excl : ∀ c e, IsFormCodeSem H c → IsUnivEnv H e →
    S c e (natV H 1) → ¬ S c e (natV H 0)

/-! ## The transfer -/

section Transfer

variable (H : ZFAxioms mem)

/-- **Conjunct 1 transfers, at any bound, with no property of `L` beyond
the previous field.**  This is
`LocalStepDerivation.bot_notSigma_step` phrased on `EnlargedFields.Step`:
the falsity code carries head tag `2`, and the five structural rows of
`LevelJustified` each force a head tag in `{3, …, 7}`, so only the
delegation row survives.  No closed set is constructed, which matters
because at an opaque placeholder level none can be. -/
theorem botNotSigma_step {L : W → W → W → Prop} {bnd : W}
    (hprev : ∀ e, IsUnivEnv H e → ¬ L (botC H) e (natV H 1))
    {e : W} (he : IsUnivEnv H e) :
    ¬ Step H L bnd (botC H) e (natV H 1) := by
  rintro ⟨C, hC, hm⟩
  exact hprev e he
    (levelJustified_of_tag_low H (t := 2) (by omega) (hC _ _ _ hm).2)

/-- **The whole local-step field transfers to the closure level under the
enlarged certificate.**

The positive counterpart of
`LocalStepDerivation.exclusivity_not_step_transferable`: the same field,
about the same closure level, now derivable — with the two new certificate
fields in the antecedent, the internal code induction as an explicit
hypothesis, and the bound an element of `ω`.

Conjunct 1 is `botNotSigma_step` and needs nothing new.  Conjunct 2 is
`EnlargedFields.exclusivity_step`, i.e. the single induction on internal
formula codes of `stepGood_of_levelLaws`. -/
theorem localStepLaws_step {L : W → W → W → Prop} {b : W}
    (hb : mem b (omegaV H)) (hprev : LocalStepLaws H L) (hL : LevelLaws H L b)
    (hind : ∀ C, LevelClosed H L (vsucc H b) C →
      CodeInduction H (StepGood H L (vsucc H b) C)) :
    LocalStepLaws H (Step H L (vsucc H b)) where
  botNotSigma := fun e he ↦ botNotSigma_step H hprev.botNotSigma he
  excl := fun c e hc he h1 ↦ exclusivity_step H hb hL hind hc he h1

end Transfer

/-! ## Soundness

The abstract statement is true of goal 2's actual hierarchy at every level,
so neither `LocalStepLaws` nor the transfer above is vacuous. -/

section Soundness

variable (H : ZFAxioms mem)

/-- **The local polarity laws hold at every level of the real
hierarchy.** -/
theorem localStepLaws_levelSat (n : Nat) : LocalStepLaws H (LevelSat H n) where
  botNotSigma := fun _ _ h ↦ sigmaTrue_bot H n h
  excl := fun c e hc he h ↦ sigmaTrue_not_piFalse H n c e hc he h

/-- **The transfer is instantiable at the real hierarchy**, at every
standard index: all four hypotheses are met, the code induction by
`EnlargedFields.codeInduction_of_definable`'s source
(`FormulaClosedSet.isFormCodeSem_ind'`) and the bound by
`natV_mem_omega`. -/
theorem localStepLaws_step_levelSat (n : Nat)
    (hind : ∀ C, LevelClosed H (LevelSat H (n + 1)) (vsucc H (natV H n)) C →
      CodeInduction H
        (StepGood H (LevelSat H (n + 1)) (vsucc H (natV H n)) C)) :
    LocalStepLaws H (Step H (LevelSat H (n + 1)) (vsucc H (natV H n))) :=
  localStepLaws_step H (natV_mem_omega H n) (localStepLaws_levelSat H (n + 1))
    (levelLaws_levelSat H n) hind

end Soundness

end LocalStepTransfer
end ZFCinPA
end LeanProofs
