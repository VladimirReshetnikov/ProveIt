import ZFCinPA.LSchema

/-! Axiom audit for the schema obligations and the choice transport
(`LFvBound`, `LPeel`, `LSepBase`, `LReplBase`, `LSchema`). -/

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
#print axioms LReplBase.QX2_free
#print axioms LReplBase.qPremise2
#print axioms LReplBase.replComb_provable
#print axioms LReplBase.repl_base
#print axioms LReplBase.repl_obligation
#print axioms LSchema.hSchema
#print axioms LSchema.provable_falsum_ZF_of_ZFC
#print axioms LSchema.iSigma1_proves_con_ZF_imp_con_ZFC
#print axioms LSchema.peano_proves_con_ZF_imp_con_ZFC

#check @LSchema.peano_proves_con_ZF_imp_con_ZFC
