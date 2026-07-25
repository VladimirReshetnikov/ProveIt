import ZFCinPA.CertificateFamily

/-!
# Audit for the six-field `𝗭𝗙𝗖` certificate families

The audit keeps the design boundary visible: the sixth certificate field is
forced to the internalized `Conₓ(ZFC)` whose raw code is `conZFCSetCodeFun`,
the typed wrapper's well-formedness witness is recovered from the master
proof itself rather than assumed, and the master-code `𝚺₁` graph is
assembled compositionally from the five variable field graphs plus the
already-established `conZFCSetCodeGraph`.
-/

namespace LeanProofs.ZFCinPA.CertificateFamilyAudit

open LeanProofs.ZFCinPA

/-! ## Formula-hood from proof-hood -/

#check @isFormula_of_proof

/-! ## The six-field record -/

#check @ZFCTruthCertificateFields
#check @ZFCTruthCertificateFields.sentence
#check @ZFCTruthCertificateFields.intro
#check @ZFCTruthCertificateFields.finalConsistencyProof

/-! ## The typed consistency target -/

#check @conZFCSetFormula
#check @conZFCSetFormula_val
#check @isFormula_conZFCSetCodeFun_natCast
#check @isFormula_conZFCSetCodeFun_zero

/-! ## The level-indexed family -/

#check @ZFCTruthCertificateFamily
#check @ZFCTruthCertificateFamily.fields
#check @ZFCTruthCertificateFamily.code
#check @ZFCTruthCertificateFamily.fields_sentence_val
#check @ZFCTruthCertificateFamily.isFormula_conCode_of_masterProof
#check @ZFCTruthCertificateFamily.toTProof
#check @ZFCTruthCertificateFamily.exists_finalProof_of_masterProof

/-! ## Master-code definability -/

#check @assembleZFCTruthCertificateCode
#check @assembleZFCTruthCertificateCode_definable
#check @ZFCTruthCertificateFamily.conZFCSetCodeFun_definable
#check @ZFCTruthCertificateFamily.code_definable_of_fields

/-! ## Assumption audit

Foundation's arithmetic is classical, so `Classical.choice`, `propext` and
`Quot.sound` are expected; nothing beyond Lean's three standard axioms
should appear, and in particular no `sorry` and no theory-specific axiom. -/

#print axioms isFormula_of_proof
#print axioms conZFCSetFormula
#print axioms isFormula_conZFCSetCodeFun_zero
#print axioms ZFCTruthCertificateFamily.fields_sentence_val
#print axioms ZFCTruthCertificateFamily.isFormula_conCode_of_masterProof
#print axioms ZFCTruthCertificateFamily.toTProof
#print axioms ZFCTruthCertificateFamily.exists_finalProof_of_masterProof
#print axioms ZFCTruthCertificateFamily.code_definable_of_fields

end LeanProofs.ZFCinPA.CertificateFamilyAudit
