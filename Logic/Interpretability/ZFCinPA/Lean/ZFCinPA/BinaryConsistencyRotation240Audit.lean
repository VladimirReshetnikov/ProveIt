import ZFCinPA.BinaryConsistencyRotation240

/-! Axiom audit for the binary Rotation240 PA endpoint:
`𝗣𝗔 ⊢ Con(𝗭𝗙𝗖) ↔ ¬(the exact 240-state machine halts from the blank tape)`. -/

open LeanProofs.ZFCinPA

#print axioms BinaryConsistencyRotation240.control_table_eq
#print axioms BinaryConsistencyRotation240.blankSentence_iff_rotationHaltsSentence_eval
#print axioms BinaryConsistencyRotation240.isigma1_proves_blank_iff_rotation_halts
#print axioms BinaryConsistencyRotation240.iSigma2_proves_con_ZF_iff_not_binary_halts
#print axioms BinaryConsistencyRotation240.iSigma2_proves_con_ZFC_iff_not_binary_halts
#print axioms BinaryConsistencyRotation240.peano_proves_con_ZF_iff_not_binary_halts
#print axioms BinaryConsistencyRotation240.peano_proves_con_ZFC_iff_not_binary_halts
