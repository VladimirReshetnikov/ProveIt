/-!
# Object-language targets for ProveIt's iPRA

STATUS: uncompiled interface blueprint.  The comments below state the exact
endpoint required for completion.  No ambient `Real` theorem is counted as the
object-theory result.
-/

-- Intended repository imports at snapshot
-- 8f028dcb4be7a7397d0c11d7c467aa1170cbf2f3:
--
-- import ConciseIPRA.PR
-- import ConciseIPRA.NativeBiInterpretation
-- import IPRADerivations

namespace LeanProofs.ConciseIPRA

/-
open Syn
open scoped Fm

The compiler must define concrete symbols such as

  gaussianCDFCheck  : PR 4
  gaussianMoment    : PR 1
  hermiteCoeff      : PR 2
  millsCheck        : PR 4
  quantileCheck     : PR 4
  matrixPDCheck     : PR 2
  sampleDecompCheck : PR 3

and prove their defining equations with `PRA.precZero`, `PRA.precSucc`,
composition lemmas, bounded-sum derivations, and `PRA.qfInd`.

For each checker, expose a closed formula.  Schematic examples:

  def momentRecurrenceSentence : Fm PTm 0 :=
    ∀ n, gaussianMoment (n+2) = (n+1) * gaussianMoment n

  def cdfSoundSentence : Fm PTm 0 :=
    ∀ x p c,
      gaussianCDFCheck x p c = 1 →
      intervalWidth c ≤ 2^(-p) ∧ CDFContract x c

  def coverageSentence : Fm PTm 0 :=
    coverageCheck 1 c1 = 1 ∧ ... ∧ coverageCheck 6 c6 = 1

The required exported theorems then literally have types

  theorem momentRecurrence_object :
      ([] : List (Fm PTm 0)) ⊢[PRAAx] momentRecurrenceSentence := by
    ...

  theorem cdfSound_object :
      ([] : List (Fm PTm 0)) ⊢[PRAAx] cdfSoundSentence := by
    ...

  theorem coverage_object :
      ([] : List (Fm PTm 0)) ⊢[PRAAx] coverageSentence := by
    ...

After an ordinary derivation `h`, the checked native endpoint is obtained from

  (pra_iff_native.mp h) :
    NPrf (([] : List (Fm PTm 0)).map NFm.ofPRA)
      (NFm.ofPRA coverageSentence)

The exact bridge is proved in `ConciseIPRA.NativeBiInterpretation` and must not
be replaced by a semantic soundness assumption.
-/

end LeanProofs.ConciseIPRA
