import ZFCinPA.CodeInductionSource

/-!
# Audit for the code-induction source antecedent

Five things must stay visible.

* **The semantic bridge is unconditional.**
  `codeInduction_of_pairSeparation` and
  `codeInduction_stepGood_of_pairSeparation` are *theorems* over goal 2's
  abstract closure vocabulary; they assume only one **parameter-free**
  Separation instance at the closed predicate `StepGoodPair`, which is
  exactly the shape `SeparationKernel.zfcSeparationProofOfShiftFixed`
  supplies.  Nothing about the source language enters.
* **The conclusion is the hypothesis `localStepLaws_step` consumes.**
  `codeInduction_of_srcCodeInduction` produces
  `EnlargedFields.CodeInduction H (EnlargedFields.StepGood H
  (templateLevel X H) bnd C)` at *every* bound and *every* certificate,
  and `codeInduction_of_srcCodeInductionSucc` the same over
  `templateStepLevel`.  Nothing is weakened: the `LevelClosed` guard that
  `localStepLaws_step` carries is simply not needed here, so the statement
  is strictly stronger than what is required.
* **The evaluation is in an arbitrary template structure.**  The `X` of
  `eval_srcCodeInductionOf` is any `Structure srcL X` with genuine
  equality; the two placeholders are opaque.
* **The discharge is real.**  `zfcCodeInductionSentenceProof` produces an
  element of `(𝗭𝗙𝗖).internalize V ⊢! …` — an honest internal `𝗭𝗙𝗖` proof
  code in `V` — at every model index `x : V`, standard or not.  Its only
  input is `SeparationKernel.zfcSeparationProofOfShiftFixed` at the
  translated core, whose shift-fixedness comes from
  `shift_translateFormula_of_fvFree`.
* **Nothing is assumed.**  The four new `freeMax` bounds are kernel
  `decide`s, not axioms; there is no `sorry`, no `axiom`, no
  `native_decide`.

The `#print axioms` lines must show only Lean's three standard classical
axioms.
-/

namespace LeanProofs.ZFCinPA.CodeInductionSourceAudit

open LeanProofs.ZFCinPA
open LeanProofs.ZFCinPA.CodeInductionSource

/-! ## The semantic bridge -/

#check @StepGoodPair
#check @codeInduction_congr
#check @codeInduction_of_pairSeparation
#check @codeInduction_stepGood_of_pairSeparation

/-! ## The shift lemma -/

#check @shift_eq_self_of_fvFree
#check @shift_translateFormula_of_fvFree

/-! ## The new free-slot bounds -/

#check @freeMax_tripleMemGoodOne
#check @freeMax_tripleMemGoodZero
#check @freeMax_kpairPair
#check @freeMax_kpairOuter
#check @free_tripleMemGoodOne
#check @free_tripleMemGoodZero
#check @free_kpairPair
#check @free_kpairOuter
#check @free_fMem

/-! ## The source formulas -/

#check @srcStepGoodBody
#check @srcStepGoodPairAt
#check @srcCodeInductionOf
#check @srcCodeInduction
#check @srcCodeInductionSucc
#check @srcCodeInductionSentence
#check @srcCodeInductionSuccSentence

/-! ## Free-variable-freeness -/

#check @fvFree_iff'
#check @fvFree_srcStepGoodBody
#check @fvFree_srcStepGoodPairAt
#check @fvFree_srcCodeInductionOf
#check @fvFree_srcCodeInduction
#check @fvFree_srcCodeInductionSucc

/-! ## Evaluation -/

#check @eval_srcStepGoodBody
#check @eval_srcStepGoodPairAt
#check @eval_srcCodeInductionOf
#check @codeInduction_stepGood_of_eval
#check @codeInduction_of_srcCodeInduction
#check @codeInduction_of_srcCodeInductionSucc

/-! ## Translation and discharge -/

#check @translate_liftP_move
#check @translate_srcStepGoodBody_depth
#check @translate_srcStepGoodPairAt_depth
#check @stepGoodPairQ
#check @shift_stepGoodPairQ
#check @toSet_sepAtomZY
#check @toSet_sepAtomZX
#check @subst_sepSubstConst_stepGoodPairQ
#check @translate_srcCodeInductionOf
#check @zfcCodeInductionProof
#check @zfcCodeInductionSentenceProof
#check @zfcCodeInductionSuccSentenceProof

/-! ## Assumption audit -/

#print axioms StepGoodPair
#print axioms codeInduction_congr
#print axioms codeInduction_of_pairSeparation
#print axioms codeInduction_stepGood_of_pairSeparation
#print axioms shift_eq_self_of_fvFree
#print axioms shift_translateFormula_of_fvFree
#print axioms freeMax_tripleMemGoodOne
#print axioms freeMax_tripleMemGoodZero
#print axioms freeMax_kpairPair
#print axioms freeMax_kpairOuter
#print axioms free_tripleMemGoodOne
#print axioms free_tripleMemGoodZero
#print axioms free_kpairPair
#print axioms free_kpairOuter
#print axioms free_fMem
#print axioms srcStepGoodBody
#print axioms srcStepGoodPairAt
#print axioms srcCodeInductionOf
#print axioms srcCodeInduction
#print axioms srcCodeInductionSucc
#print axioms srcCodeInductionSentence
#print axioms srcCodeInductionSuccSentence
#print axioms fvFree_iff'
#print axioms fvFree_srcStepGoodBody
#print axioms fvFree_srcStepGoodPairAt
#print axioms fvFree_srcCodeInductionOf
#print axioms fvFree_srcCodeInduction
#print axioms fvFree_srcCodeInductionSucc
#print axioms eval_srcStepGoodBody
#print axioms eval_srcStepGoodPairAt
#print axioms eval_srcCodeInductionOf
#print axioms codeInduction_stepGood_of_eval
#print axioms codeInduction_of_srcCodeInduction
#print axioms codeInduction_of_srcCodeInductionSucc
#print axioms translate_liftP_move
#print axioms translate_srcStepGoodBody_depth
#print axioms translate_srcStepGoodPairAt_depth
#print axioms stepGoodPairQ
#print axioms shift_stepGoodPairQ
#print axioms toSet_sepAtomZY
#print axioms toSet_sepAtomZX
#print axioms subst_sepSubstConst_stepGoodPairQ
#print axioms translate_srcCodeInductionOf
#print axioms zfcCodeInductionProof
#print axioms zfcCodeInductionSentenceProof
#print axioms zfcCodeInductionSuccSentenceProof

end LeanProofs.ZFCinPA.CodeInductionSourceAudit
