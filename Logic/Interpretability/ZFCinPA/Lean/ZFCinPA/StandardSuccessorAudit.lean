import ZFCinPA.StandardSuccessor

/-!
# Audit for the standard-index successor implications

The audit keeps the module's layers visible in their types:

* well-formedness of the successor consistency code at a standard index;
* the six typed internal `𝗭𝗙𝗖` proofs of the level-`↑n+1` fields, each by
  goal 2's semantics, completeness, and **D1**;
* their assembly into `ZFCSuccessorImplications` at `↑n`, and the
  resulting staged step at every standard index.

The scope of the module is deliberately limited: it establishes the
successor obligation along the standard cut only, which is *not* the
staged successor (that quantifies over all `x : V`).  Its purpose is to
certify that the six-implication interface is the right one.
-/

namespace LeanProofs.ZFCinPA.StandardSuccessorAudit

open LeanProofs.ZFCinPA

/-! ## Well-formedness -/

#check @isFormula_conZFCSetCodeFun_natCast_succ

/-! ## The six typed internal proofs -/

#check @standardLocalStepProof
#check @standardCrossLevelProof
#check @standardShiftInvariantProof
#check @standardSubstitutionInvariantProof
#check @standardAxiomSoundProof
#check @standardTarskiElimProof
#check @standardTarskiIntroProof
#check @standardFinalConsistencyProof

/-! ## Assembly -/

#check @standardSuccessorImplications
#check @exists_stagedStep_natCast

/-! ## Assumption audit -/

#print axioms isFormula_conZFCSetCodeFun_natCast_succ
#print axioms standardSuccessorImplications
#print axioms exists_stagedStep_natCast

end LeanProofs.ZFCinPA.StandardSuccessorAudit
