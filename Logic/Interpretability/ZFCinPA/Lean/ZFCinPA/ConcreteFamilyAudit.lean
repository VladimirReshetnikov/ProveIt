import ZFCinPA.ConcreteFamily

/-!
# Audit for the concrete truth-certificate family

The audit keeps the module's layers visible in their types:

* arity monotonicity and the leaf well-formedness principle;
* the tower well-formedness invariants, proved by model-internal `𝚺₁`
  successor induction;
* well-formedness of the five field codes and their typed views;
* the assembled `ZFCTruthCertificateFamily` and its five `𝚺₁` field-code
  graphs in exactly the endpoint's shape, plus the master-code graph.
-/

namespace LeanProofs.ZFCinPA.ConcreteFamilyAudit

open LeanProofs.ZFCinPA

/-! ## Arity plumbing -/

#check @isSemiformula_of_le
#check @leafArity

/-! ## Tower invariants -/

#check @numChainCode_definable
#check @closCode_definable
#check @levelSatCode_definable
#check @isSemiformula_numChainCode
#check @isSemiformula_closCode
#check @isSemiformula_levelSatCode
#check @isSemiformula_sigmaTrueCode
#check @isSemiformula_piFalseCode
#check @isSemiformula_piTrueCode

/-! ## Field-code well-formedness and typed views -/

#check @isFormula_localStepCode
#check @isFormula_crossLevelCode
#check @isFormula_shiftInvariantCode
#check @isFormula_substitutionInvariantCode
#check @isFormula_axiomSoundCode
#check @localStepFormula
#check @crossLevelFormula
#check @shiftInvariantFormula
#check @substitutionInvariantFormula
#check @axiomSoundFormula

/-! ## The assembled family -/

#check @concreteZFCTruthCertificateFamily
#check @concreteZFCTruthCertificateFamily_localStep
#check @concreteZFCTruthCertificateFamily_crossLevel
#check @concreteZFCTruthCertificateFamily_shiftInvariant
#check @concreteZFCTruthCertificateFamily_substitutionInvariant
#check @concreteZFCTruthCertificateFamily_axiomSound
#check @concreteFamily_localStep_definable
#check @concreteFamily_crossLevel_definable
#check @concreteFamily_shiftInvariant_definable
#check @concreteFamily_substitutionInvariant_definable
#check @concreteFamily_axiomSound_definable
#check @concreteFamily_code_definable

/-! ## Assumption audit

Foundation's arithmetic and the repository's semantic core are classical,
so `Classical.choice`, `propext` and `Quot.sound` are expected; nothing
beyond Lean's three standard axioms should appear, and in particular no
`sorry` and no theory-specific axiom. -/

#print axioms isSemiformula_numChainCode
#print axioms isSemiformula_closCode
#print axioms isSemiformula_levelSatCode
#print axioms isFormula_localStepCode
#print axioms isFormula_crossLevelCode
#print axioms isFormula_shiftInvariantCode
#print axioms isFormula_substitutionInvariantCode
#print axioms isFormula_axiomSoundCode
#print axioms concreteFamily_code_definable

end LeanProofs.ZFCinPA.ConcreteFamilyAudit
