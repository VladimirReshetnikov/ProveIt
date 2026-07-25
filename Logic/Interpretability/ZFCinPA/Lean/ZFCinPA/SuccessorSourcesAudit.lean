import ZFCinPA.SuccessorSources

/-!
# Audit for the shared source layer of the certificate-field successors

The audit keeps four things visible.

* **Shift-fixedness of the two model-coded leaves.**  `shift_numChainCode`,
  `shift_closCode` and the typed corollary `shift_levelLeaves` are
  *theorems*, not hypotheses: this is the premise
  `SetPlaceholders.compileSetTemplate` places on any interpretation of the
  placeholders, and it is now discharged once for all five certificate
  fields.
* **The exported free-slot bounds.**  `LevelCodeTower.fm01`–`fm16` and
  `freeMax_closF_zero` are the project's only kernel evaluations of
  `freeMax` on the concrete macros; every depth move below goes through
  one of them, and none is re-`decide`d here.  The single new evaluation
  is `freeMax_tripleMemCanon`.
* **The source tower.**  The template (`levelArities`, `srcL`,
  `levelLeaves`), the atoms, and the canonical-slot readings at the
  successor index, each with its reconciliation lemma.
* **The successor spine.**  `srcClosStep` is the source counterpart of
  `closCode_succ = closStepCode (numChainCode x) (closCode x)` — the
  nineteen-leaf spine every field's successor has to unfold — together
  with `srcNumChainSucc` and the level tower one level up.  Their
  reconciliation lemmas are equations between *specializations* and the
  raw builders of `ZFCinPA.LevelCodeTower`, at every model index and every
  ambient arity that can hold the corresponding formula.

Nothing here evaluates a Gödel code: the fixed leaf codes are compared
with quotations only through `coe_toNat_eq_quote` and `quote_leaf_move`.

The `#print axioms` lines must show only Lean's three standard classical
axioms.
-/

namespace LeanProofs.ZFCinPA.SuccessorSourcesAudit

open LeanProofs.ZFCinPA
open LeanProofs.ZFCinPA.SuccessorSources

/-! ## The exported free-slot bounds of `ZFCinPA.LevelCodeTower` -/

#check @fm01
#check @fm08
#check @fm16
#check @freeMax_closF_zero
#check @freeMax_tripleMemCanon

/-! ## Shift-fixedness -/

#check @ShiftFixed
#check @shiftFixed_leafCode
#check @shiftFixed_lvlInstPart
#check @shiftFixed_allClauseCode
#check @shiftFixed_exClauseCode
#check @shiftFixed_justRowCode
#check @shiftFixed_closStepCode
#check @shift_numChainCode
#check @shift_closCode
#check @shift_levelLeaves

/-! ## The template and its atoms -/

#check @levelArities
#check @srcL
#check @levelLeaves
#check @srcPProp
#check @srcPlaceholder
#check @liftP
#check @srcNumAt
#check @srcClsAt
#check @translate_srcPlaceholder
#check @translate_liftP
#check @quote_toSet_eq_code
#check @quote_leaf_move

/-! ## The source level tower at the canonical slots -/

#check @srcLvlInst
#check @srcLvlInstP
#check @srcLevelSat
#check @srcSigmaTrue
#check @srcPiFalse
#check @srcPiTrue
#check @srcCanonAt
#check @translate_srcLvlInst
#check @translate_srcLvlInstP
#check @translate_srcLevelSat
#check @translate_srcSigmaTrue
#check @translate_srcPiFalse
#check @translate_srcPiTrue
#check @translate_srcCanonAt

/-! ## The successor spine -/

#check @srcNumChainSucc
#check @srcAllClause
#check @srcExClause
#check @srcJustRow
#check @srcClosStep
#check @translate_srcNumChainSucc
#check @translate_srcAllClause
#check @translate_srcExClause
#check @translate_srcJustRow
#check @translate_srcClosStep

/-! ## The level tower one level up -/

#check @srcLevelSatSucc
#check @srcSigmaTrueSucc
#check @srcPiFalseSucc
#check @srcPiTrueSucc
#check @translate_srcLevelSatSucc
#check @translate_srcSigmaTrueSucc
#check @translate_srcPiFalseSucc
#check @translate_srcPiTrueSucc

/-! ## Free-variable-freeness and the closure into a sentence -/

#check @FvFree
#check @fvFree_liftP
#check @fvFree_srcPlaceholder
#check @fvFree_srcClosStep
#check @fvFree_srcSigmaTrueSucc
#check @fvFree_srcPiTrueSucc
#check @emb_univCl_of_fvFree

/-! ## Assumption audit -/

#print axioms shift_numChainCode
#print axioms shift_closCode
#print axioms shift_levelLeaves
#print axioms shiftFixed_closStepCode
#print axioms translate_srcPlaceholder
#print axioms translate_srcLevelSat
#print axioms translate_srcSigmaTrue
#print axioms translate_srcPiFalse
#print axioms translate_srcPiTrue
#print axioms translate_srcCanonAt
#print axioms translate_srcNumChainSucc
#print axioms translate_srcAllClause
#print axioms translate_srcExClause
#print axioms translate_srcJustRow
#print axioms translate_srcClosStep
#print axioms translate_srcLevelSatSucc
#print axioms translate_srcSigmaTrueSucc
#print axioms translate_srcPiFalseSucc
#print axioms translate_srcPiTrueSucc
#print axioms fvFree_srcClosStep
#print axioms emb_univCl_of_fvFree

end LeanProofs.ZFCinPA.SuccessorSourcesAudit
