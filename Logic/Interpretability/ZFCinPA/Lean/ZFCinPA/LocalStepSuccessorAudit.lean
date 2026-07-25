import ZFCinPA.LocalStepSuccessor

/-!
# Audit for the level-tower proof template and the local-step field

The audit keeps three things visible.

* **The template.**  `levelArities`, `srcL`, `levelLeaves`: the whole
  `x`-dependence of a certificate field code is two model-coded leaves of
  arities `1` and `2`.
* **The reconciliation.**  `translate_srcPlaceholder` (the compiler emits a
  substitution, `ZFCinPA.SubstIdentity` removes it), the tower layers, and
  the headline `translate_srcLocalStep_formula`: at *every* model index the
  first certificate field is the specialization of one fixed source
  formula.
* **The reduction.**  `localStepSuccessor_of_source` derives the
  `localStep` field of `ZFCSuccessorImplications` from two explicit
  inputs.  Its statement is the honest boundary of this module: the source
  sentence together with its specialization identity, and the source
  proof, are *hypotheses*, not claims.  Shift-fixedness of the two
  model-coded leaves is no longer among them — it is proved in
  `ZFCinPA.SuccessorSources` (`shift_levelLeaves`) and audited there.

The `#print axioms` lines must show only Lean's three standard classical
axioms.  In particular `previous_imp_localStep` — the one unconditional
consequence of the previous master certificate used here — is a plain
`⋏`-elimination.
-/

namespace LeanProofs.ZFCinPA.LocalStepSuccessorAudit

open LeanProofs.ZFCinPA.LocalStepSuccessor

/-! ## The template -/

#check @levelArities
#check @srcL
#check @levelLeaves
#check @srcPProp
#check @srcPlaceholder
#check @liftP

/-! ## Atom-level reconciliation -/

#check @translate_srcPlaceholder
#check @translate_liftP
#check @quote_toSet_eq_code

/-! ## The source tower and its reconciliation -/

#check @srcLevelSat
#check @srcSigmaTrue
#check @srcPiFalse
#check @srcPiTrue
#check @srcCanonAt
#check @srcLocalStep
#check @srcLocalStepSucc
#check @srcLocalStepStepProp
#check @srcLocalStepStep

#check @translate_srcLevelSat
#check @translate_srcSigmaTrue
#check @translate_srcPiFalse
#check @translate_srcPiTrue
#check @translate_srcCanonAt
#check @translate_srcLocalStep
#check @translate_srcLocalStep_formula
#check @translate_srcLocalStepSucc
#check @translate_srcLocalStepSucc_formula
#check @translate_srcLocalStepStepProp
#check @emb_srcLocalStepStep
#check @translate_srcLocalStepStep

/-! ## The reduction, with its explicit hypotheses -/

#check @previous_imp_localStep
#check @localStepSuccessor_of_source
#check @localStepSuccessor_of_sourceProof
#check @localStepSuccessor_of_derivation

/-! ## Assumption audit -/

#print axioms translate_srcPlaceholder
#print axioms translate_srcLevelSat
#print axioms translate_srcSigmaTrue
#print axioms translate_srcPiFalse
#print axioms translate_srcPiTrue
#print axioms translate_srcCanonAt
#print axioms translate_srcLocalStep
#print axioms translate_srcLocalStep_formula
#print axioms translate_srcLocalStepSucc
#print axioms emb_srcLocalStepStep
#print axioms translate_srcLocalStepStep
#print axioms previous_imp_localStep
#print axioms localStepSuccessor_of_source
#print axioms localStepSuccessor_of_derivation

end LeanProofs.ZFCinPA.LocalStepSuccessorAudit
