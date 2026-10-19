import ZFCinPA.ValidatorConsistencyEquivalence

/-! Axiom audit for the native-to-validator translation (`R2`) and the final
`𝗣𝗔 ⊢ Con(𝗭𝗙) ↔ validator consistency ↔ Con(𝗭𝗙𝗖)` equivalence. -/

open LeanProofs.ZFCinPA

#print axioms R2Neg.encode_neg
#print axioms R2Quant.all_intro
#print axioms R2Quant.ex_intro
#print axioms R2Main.cProv_falsum_of_provable
#print axioms R2Gic.gic_bridge_core
#print axioms R2Ax.gic_axiom
#print axioms R2Fixed.relExt_mem_ax
#print axioms R2Fixed.irr_ax
#print axioms R2Fixed.container_ax
#print axioms R2Native.axOK_native
#print axioms R2Native.cProv_falsum_of_ZF
#print axioms R2Native.peano_proves_validator_imp_con_ZF
#print axioms ValidatorConsistencyEquivalence.iSigma2_proves_con_ZF_iff_validator
#print axioms ValidatorConsistencyEquivalence.peano_proves_con_ZF_iff_validator
#print axioms ValidatorConsistencyEquivalence.peano_proves_con_ZFC_iff_validator
