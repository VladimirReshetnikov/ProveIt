import ZFCinPA.LTemplate
import ZFCinPA.LPieces
import ZFCinPA.LTransVal

/-! Axiom audit for `LTemplate`, `LPieces` and `LTransVal`. -/

open LeanProofs.ZFCinPA

#print axioms LTemplate.equality_cases
#print axioms LTemplate.translated_axiom
#print axioms LTemplate.compileT_provable
#print axioms LTemplate.pure_models
#print axioms LTemplate.sep_iff
#print axioms LTemplate.repl_iff
#print axioms LTemplate.templ_provable
#print axioms LPieces.eval_piece
#print axioms LPieces.eval_stageP
#print axioms LPieces.eval_finSuppP
#print axioms LPieces.eval_satP
#print axioms LTransVal.val_translateFormula
#print axioms LTransVal.transVal_definable
