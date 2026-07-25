import ZFCinPA.LevelCodeTower

/-!
# Audit for the level-indexed code towers

The audit keeps the tower's layers visible in their types:

* the form-level recursion shape — the closure kernel, the unfolded
  successor instance, and the canonical wrappers;
* the tight free-slot bound and the kernel fact `Free i (closF n) → i < 2`
  that licenses every depth move;
* the internal builder — the `𝚺₁`-represented step function and the two
  `PR` towers with their graphs;
* standard-point quotation agreement for the kernel, the canonical
  instance, and the three derived readings;
* the functional relation `LevelSatCode` with totality, single-valuedness,
  and its numeral points.

Nothing here evaluates a Gödel code: the fixed leaf codes are compared
with quotations only through `coe_toNat_eq_quote`.
-/

namespace LeanProofs.ZFCinPA.LevelCodeTowerAudit

open LeanProofs.ZFCinPA

/-! ## Form-level analysis -/

#check @closF
#check @lvlInstF
#check @levelSatF_succ_eq
#check @closF_succ_form
#check @fSigmaTrueF_canonical
#check @fPiFalseF_canonical
#check @fPiTrueF_canonical

/-! ## The tight free-slot bound -/

#check @freeMax
#check @free_lt_freeMax
#check @free_closF

/-! ## The fixed codes -/

#check @tripleMemHeadCode
#check @tripleMemInstACode
#check @tripleMemInstBCode
#check @tripleMemInstCCode
#check @tripleMemCanonCode
#check @levelSatZeroCode
#check @closZeroCode

/-! ## The internal builder -/

#check @lvlInstPart
#check @lvlInstGraph
#check @lvlInstPart.defined
#check @allClauseCode
#check @allClauseCode.defined
#check @exClauseCode
#check @exClauseCode.defined
#check @justRowCode
#check @justRowCode.defined
#check @closStepCode
#check @closStepGraph
#check @closStepCode.defined
#check @closCode
#check @closGraph
#check @closCode_zero
#check @closCode_succ
#check @closCode.defined
#check @levelSatCode
#check @levelSatGraph
#check @levelSatCode_zero
#check @levelSatCode_succ
#check @levelSatCode.defined
#check @sigmaTrueCode
#check @sigmaTrueCode.defined
#check @piFalseCode
#check @piFalseCode.defined
#check @piTrueCode
#check @piTrueCode.defined

/-! ## Standard points -/

#check @quote_lvlInstF
#check @quote_closF_succ
#check @closCode_natCast
#check @levelSatCode_natCast
#check @sigmaTrueCode_natCast
#check @piFalseCode_natCast
#check @piTrueCode_natCast

/-! ## The functional relation -/

#check @LevelSatCode
#check @eval_levelSatGraph_iff
#check @levelSatCode_total
#check @levelSatCode_functional
#check @levelSatCode_existsUnique
#check @levelSatCode_quote_numeral
#check @sigmaTrueCode_quote_numeral
#check @piFalseCode_quote_numeral
#check @piTrueCode_quote_numeral

/-! ## Assumption audit

Foundation's arithmetic and the repository's semantic core are classical,
so `Classical.choice`, `propext` and `Quot.sound` are expected; nothing
beyond Lean's three standard axioms should appear, and in particular no
`sorry` and no theory-specific axiom. -/

#print axioms free_closF
#print axioms closCode_natCast
#print axioms quote_closF_succ
#print axioms levelSatCode_natCast
#print axioms sigmaTrueCode_natCast
#print axioms piFalseCode_natCast
#print axioms piTrueCode_natCast
#print axioms levelSatCode_total
#print axioms levelSatCode_quote_numeral

end LeanProofs.ZFCinPA.LevelCodeTowerAudit
