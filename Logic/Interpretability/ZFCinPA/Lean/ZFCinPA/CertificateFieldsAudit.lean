import ZFCinPA.CertificateFields

/-!
# Audit for the five variable certificate fields

The audit keeps the module's layers visible in their types:

* the five field sentences and the three gadget combinators at the `Form`
  level;
* the free-slot bounds — the structural bounds for the level towers and
  the gadgets, and closedness of the five sentences;
* the fixed leaf codes and the internal builders with their `𝚺₁` graphs;
* standard-point quotation agreement for the gadgets and all five field
  builders.

Nothing here evaluates a Gödel code: fixed leaf codes are compared with
quotations only through `coe_toNat_eq_quote`.
-/

namespace LeanProofs.ZFCinPA.CertificateFieldsAudit

open LeanProofs.ZFCinPA

/-! ## Form-level definitions -/

#check @canonAtF
#check @sigmaAtF
#check @piFalseAtF
#check @piTrueAtF
#check @boundedAtF
#check @localStepF
#check @crossLevelF
#check @shiftInvariantF
#check @substitutionInvariantF
#check @axiomSoundF

/-! ## Free-slot bounds -/

#check @free_levelSatF_canonical
#check @free_fSigmaTrueF_canonical
#check @free_fPiFalseF_canonical
#check @free_fPiTrueF_canonical
#check @free_canonAtF
#check @free_sigmaAtF
#check @free_piFalseAtF
#check @free_piTrueAtF
#check @free_boundedAt1F
#check @free_fEq
#check @not_free_localStepF
#check @not_free_crossLevelF
#check @not_free_shiftInvariantF
#check @not_free_substitutionInvariantF
#check @not_free_axiomSoundF

/-! ## The fixed codes -/

#check @eqGuardCode
#check @univEnv0D2Code
#check @univEnv1D4Code
#check @univEnv1D5Code
#check @taggedEmptyD2Code
#check @isFormCode1D2Code
#check @isFormCode3D4Code
#check @isFormCode4D5Code
#check @zfcAxiomCodeD2Code
#check @quantBoundedD3Code
#check @succMapD5Code
#check @renamesShiftD5Code
#check @econsD5Code
#check @varMap3D5Code
#check @renamesSubstD5Code
#check @compD5Code

/-! ## The internal builders -/

#check @canonAtPart
#check @canonAtGraph
#check @canonAtPart.defined
#check @sigmaAtCode
#check @sigmaAtGraph
#check @sigmaAtCode.defined
#check @piFalseAtCode
#check @piFalseAtCode.defined
#check @piTrueAtCode
#check @piTrueAtCode.defined
#check @boundedAtPart
#check @boundedAtPart.defined
#check @localStepCode
#check @localStepGraph
#check @localStepCode.defined
#check @crossLevelCode
#check @crossLevelGraph
#check @crossLevelCode.defined
#check @shiftInvariantCode
#check @shiftInvariantGraph
#check @shiftInvariantCode.defined
#check @substitutionInvariantCode
#check @substitutionInvariantGraph
#check @substitutionInvariantCode.defined
#check @axiomSoundCode
#check @axiomSoundGraph
#check @axiomSoundCode.defined

/-! ## Standard points -/

#check @quote_toSet_fAll'
#check @quote_toSet_fEx'
#check @quote_toSet_fAnd
#check @quote_toSet_fOr
#check @quote_toSet_fIff
#check @quote_fEq_move
#check @quote_canonAtF
#check @quote_sigmaAtF
#check @quote_piFalseAtF
#check @quote_piTrueAtF
#check @quote_boundedAtF
#check @localStepCode_natCast
#check @crossLevelCode_natCast
#check @shiftInvariantCode_natCast
#check @substitutionInvariantCode_natCast
#check @axiomSoundCode_natCast

/-! ## Assumption audit

Foundation's arithmetic and the repository's semantic core are classical,
so `Classical.choice`, `propext` and `Quot.sound` are expected; nothing
beyond Lean's three standard axioms should appear, and in particular no
`sorry` and no theory-specific axiom. -/

#print axioms not_free_localStepF
#print axioms not_free_crossLevelF
#print axioms not_free_shiftInvariantF
#print axioms not_free_substitutionInvariantF
#print axioms not_free_axiomSoundF
#print axioms localStepCode_natCast
#print axioms crossLevelCode_natCast
#print axioms shiftInvariantCode_natCast
#print axioms substitutionInvariantCode_natCast
#print axioms axiomSoundCode_natCast

end LeanProofs.ZFCinPA.CertificateFieldsAudit
