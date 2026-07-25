import ZFCinPA.BaseCertificate

/-!
# Audit for the base master certificate

The audit keeps the module's layers visible in their types:

* satisfaction of the gadgets and of the five field sentences in every
  structure carrying goal 2's nine-axiom bundle, at every level;
* the field sentences in Foundation's `ℒₛₑₜ` and their `𝗭𝗙𝗖` derivations
  by completeness;
* the quotation identifications with the internal builders at index `0`;
* the six typed internal proofs, the assembled base master certificate,
  and the endpoint reduction of the whole uniform internal-provability
  project to the staged successor.
-/

namespace LeanProofs.ZFCinPA.BaseCertificateAudit

open LeanProofs.ZFCinPA

/-! ## Satisfaction -/

#check @sat_canonAtF
#check @sat_sigmaAtF
#check @sat_piFalseAtF
#check @sat_piTrueAtF
#check @sat_boundedAtF
#check @sat_localStepF
#check @sat_crossLevelF
#check @sat_shiftInvariantF
#check @sat_substitutionInvariantF
#check @sat_axiomSoundF

/-! ## The field sentences and their derivations -/

#check @localStepSet
#check @crossLevelSet
#check @shiftInvariantSet
#check @substitutionInvariantSet
#check @axiomSoundSet
#check @zfc_proves_localStepSet
#check @zfc_proves_crossLevelSet
#check @zfc_proves_shiftInvariantSet
#check @zfc_proves_substitutionInvariantSet
#check @zfc_proves_axiomSoundSet

/-! ## Quotation at the base index -/

#check @quote_localStepSet
#check @quote_crossLevelSet
#check @quote_shiftInvariantSet
#check @quote_substitutionInvariantSet
#check @quote_axiomSoundSet

/-! ## The typed base proofs and the master certificate -/

#check @baseLocalStepProof
#check @baseCrossLevelProof
#check @baseShiftInvariantProof
#check @baseSubstitutionInvariantProof
#check @baseAxiomSoundProof
#check @baseFinalConsistencyProof
#check @baseZFCMasterCertificate

/-! ## The exact remaining obligation -/

#check @zfcProofSelectorIn_of_concreteStagedSuccessor

/-! ## Assumption audit

Foundation's arithmetic and the repository's semantic core are classical,
so `Classical.choice`, `propext` and `Quot.sound` are expected; nothing
beyond Lean's three standard axioms should appear, and in particular no
`sorry` and no theory-specific axiom. -/

#print axioms sat_localStepF
#print axioms sat_crossLevelF
#print axioms sat_shiftInvariantF
#print axioms sat_substitutionInvariantF
#print axioms sat_axiomSoundF
#print axioms sat_connClauseF
#print axioms sat_quantClauseF
#print axioms sat_botClauseF
#print axioms sat_tarskiElimF
#print axioms sat_tarskiIntroF
#print axioms zfc_proves_localStepSet
#print axioms zfc_proves_crossLevelSet
#print axioms zfc_proves_shiftInvariantSet
#print axioms zfc_proves_substitutionInvariantSet
#print axioms zfc_proves_axiomSoundSet
#print axioms zfc_proves_tarskiElimSet
#print axioms zfc_proves_tarskiIntroSet
#print axioms quote_tarskiElimSet
#print axioms quote_tarskiIntroSet
#print axioms baseTarskiElimProof
#print axioms baseTarskiIntroProof
#print axioms baseZFCMasterCertificate
#print axioms zfcProofSelectorIn_of_concreteStagedSuccessor

end LeanProofs.ZFCinPA.BaseCertificateAudit
