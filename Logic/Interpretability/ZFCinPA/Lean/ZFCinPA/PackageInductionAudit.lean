import ZFCinPA.PackageInduction

/-!
# Audit for the existential proof-package induction

The audit keeps the reduction's boundary visible: the selector follows from
a `𝚺₁` package relation together with base, successor, and extraction
hypotheses, and nothing here constructs those packages.  The direct
specialization shows the exact `𝚺₁` interface expected from the staged
master-certificate compiler.
-/

namespace LeanProofs.ZFCinPA.PackageInductionAudit

open LeanProofs.ZFCinPA

/-! ## The abstract package induction -/

#check @HasZFCConsistencyProofPackage
#check @hasZFCConsistencyProofPackage_definable
#check @zfcProofSelectorIn_of_package

/-! ## The direct master-certificate specialization -/

#check @DirectZFCMasterProofPackage
#check @directZFCMasterProofPackage_definable
#check @zfcProofSelectorIn_of_directMasterProofs

/-! ## Assumption audit

Foundation's arithmetic is classical, so `Classical.choice`, `propext` and
`Quot.sound` are expected; nothing beyond Lean's three standard axioms
should appear, and in particular no `sorry` and no theory-specific axiom. -/

#print axioms hasZFCConsistencyProofPackage_definable
#print axioms zfcProofSelectorIn_of_package
#print axioms directZFCMasterProofPackage_definable
#print axioms zfcProofSelectorIn_of_directMasterProofs

end LeanProofs.ZFCinPA.PackageInductionAudit
