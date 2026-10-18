import ZFCinPA.NativeSchema

/-! Axiom audit for the WF interpretation of `ZF` in the native theory (`R3`). -/

open LeanProofs.ZFCinPA

#print axioms NTemplate.nativeGicProof
#print axioms NTemplate.compileN
#print axioms NTInterp.interp_translate
#print axioms NativePeel.peel
#print axioms NativeSchemaSem.sepT_provable
#print axioms NativeSchemaSem.replT_provable
#print axioms NativeSchema.sep_obligation
#print axioms NativeSchema.repl_obligation
#print axioms NativeSchema.provable_falsum_native_of_ZF
#print axioms NativeSchema.iSigma1_proves_con_native_imp_con_ZF
#print axioms NativeSchema.peano_proves_con_native_imp_con_ZF
