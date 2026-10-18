import ZFCinPA.LSepBase

/-! Axiom audit for the schema obligations (`LFvBound`, `LPeel`, `LSepBase`). -/

open LeanProofs.ZFCinPA

#print axioms LFvBound.bindFreeAt_subst_opening
#print axioms LFvBound.fvBound_subst
#print axioms LFvBound.sep_core_bound
#print axioms LFvBound.repl_core_bound
#print axioms LPeel.peelG_provable
#print axioms LPeel.finG_provable
#print axioms LPeel.peel
#print axioms LPeel.peel_close
#print axioms LSepBase.sepComb_provable
#print axioms LSepBase.sep_base
#print axioms LSepBase.sep_obligation
