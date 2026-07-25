import ZFCinPA.StagedCompiler

/-!
# Audit for the staged `𝗭𝗙𝗖` certificate compiler

The audit keeps the reduction's boundary visible: the staged compiler is
Hilbert-level plumbing over `UniversalKernel`s, the successor witness feeds
`PackageInduction`'s direct master-proof induction, and the endpoints leave
exactly a concrete certificate family (five `𝚺₁` field-code graphs, a typed
base certificate, staged successor steps at every model index) as the
remaining obligation of the uniform internal-provability project.
-/

namespace LeanProofs.ZFCinPA.StagedCompilerAudit

open LeanProofs.ZFCinPA

/-! ## Cumulative contexts -/

#check @localContext
#check @crossContext
#check @shiftContext
#check @substitutionContext
#check @soundnessContext

/-! ## The dependency-aware successor step -/

#check @ZFCStagedCertificateStep
#check @ZFCStagedCertificateStep.target
#check @ZFCStagedCertificateStep.compile
#check @ZFCStagedCertificateStep.compile_isProof
#check @ZFCStagedCertificateStep.compile_isZFCProof

/-! ## Staged successor witnesses and the selector endpoints -/

#check @HasStagedSuccessor
#check @exists_zfcMasterProof_succ_of_staged
#check @zfcProofSelectorIn_of_stagedCertificates
#check @zfcProofSelectorIn_of_stagedTypedCertificates
#check @zfcProofSelectorIn_of_stagedCertificates_and_fieldCodes

/-! ## Assumption audit

Foundation's arithmetic is classical, so `Classical.choice`, `propext` and
`Quot.sound` are expected; nothing beyond Lean's three standard axioms
should appear, and in particular no `sorry` and no theory-specific axiom. -/

#print axioms ZFCStagedCertificateStep.compile
#print axioms ZFCStagedCertificateStep.compile_isProof
#print axioms ZFCStagedCertificateStep.compile_isZFCProof
#print axioms exists_zfcMasterProof_succ_of_staged
#print axioms zfcProofSelectorIn_of_stagedCertificates
#print axioms zfcProofSelectorIn_of_stagedTypedCertificates
#print axioms zfcProofSelectorIn_of_stagedCertificates_and_fieldCodes

end LeanProofs.ZFCinPA.StagedCompilerAudit
