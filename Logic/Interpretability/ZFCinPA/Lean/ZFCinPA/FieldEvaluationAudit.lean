import ZFCinPA.FieldEvaluation

/-!
# Audit for the certificate-field readings

Four things must stay visible.

* **The first field is read, both levels.**  `eval_srcLocalStep` and
  `eval_srcLocalStepSucc` are *theorems*: in every template structure with
  genuine equality, the fixed source formulas
  `LocalStepSuccessor.srcLocalStep` and `srcLocalStepSucc` evaluate to
  `LocalStepTransfer.LocalStepLaws` at the two induced levels.
* **The levels are the abstract ones.**  `templateLevel` is an arbitrary
  interpretation of the two placeholders, and `templateStepLevel` is
  `EnlargedFields.Step` over it — exactly the shapes
  `LocalStepTransfer.localStepLaws_step` consumes and produces.
* **The bound is existentially quantified.**  Read
  `TowerEvaluation.templateStepLevel`: the numeral witness `k` is under an
  `∃`.  That is what the source syntax forces, and it is strictly weaker
  than `localStepLaws_step`'s conclusion, which fixes one `b`.  The gap is
  a `Num`-uniqueness antecedent; see item 3 of `ZFCinPA.FieldEvaluation`'s
  residue section.
* **Nothing is assumed.**  No Tarski field reading, no `srcCrossLevel`, no
  source `CodeInduction`, and no assembled source sentence exists in this
  project; the residue section states each of them.

The `#print axioms` lines must show only Lean's three standard classical
axioms.
-/

namespace LeanProofs.ZFCinPA.FieldEvaluationAudit

open LeanProofs.ZFCinPA
open LeanProofs.ZFCinPA.TemplateEvaluation

/-! ## The level tower -/

#check @templateStepLevel
#check @eval_srcLevelSatAt
#check @eval_srcNumChainSucc
#check @eval_srcBitWitnessAt
#check @eval_srcCanonAtPair
#check @eval_srcPolarAt
#check @eval_srcLevelSatSuccAt
#check @eval_srcBitWitnessSuccAt
#check @eval_srcPolarAtSucc

/-! ## The first certificate field -/

#check @eval_srcLocalStep
#check @eval_srcLocalStepSucc

/-! ## The abstract field the readings land on -/

#check @LocalStepTransfer.LocalStepLaws
#check @LocalStepTransfer.localStepLaws_step

/-! ## Assumption audit -/

#print axioms eval_srcLevelSatAt
#print axioms eval_srcNumChainSucc
#print axioms eval_srcBitWitnessAt
#print axioms eval_srcCanonAtPair
#print axioms eval_srcPolarAt
#print axioms eval_srcLevelSatSuccAt
#print axioms eval_srcBitWitnessSuccAt
#print axioms eval_srcPolarAtSucc
#print axioms eval_srcLocalStep
#print axioms eval_srcLocalStepSucc

end LeanProofs.ZFCinPA.FieldEvaluationAudit
