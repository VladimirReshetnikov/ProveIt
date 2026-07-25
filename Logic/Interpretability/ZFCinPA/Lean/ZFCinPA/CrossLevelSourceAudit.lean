import ZFCinPA.CrossLevelSource

/-!
# Audit for the source form of the decidedness field

Five things must stay visible.

* **The field has a source formula at both levels.**  `srcCrossLevel` and
  `srcCrossLevelSucc` are *definitions* over the fixed placeholder
  language `SuccessorSources.srcL`, with no model and no index in them.
* **They specialize to the real field codes.**
  `translate_srcCrossLevel` and `translate_srcCrossLevelSucc` are
  theorems, at an arbitrary `x : V` — nonstandard indices included.
* **They are free-variable-free**, so they can be closed into sentences by
  `SuccessorSources.emb_univCl_of_fvFree`.
* **They read as decidedness.**  `eval_srcCrossLevel` and
  `eval_srcCrossLevelSucc` are theorems, in an *arbitrary* template
  structure with genuine equality, over `templateLevel` and
  `templateStepLevel`.  The bound is existential in the **antecedent**, so
  `decided_of_srcCrossLevel` / `decided_of_srcCrossLevelSucc` recover
  `EnlargedFields.LevelLaws.decided`'s statement at any recognized bound
  with no uniqueness hypothesis.
* **Nothing is assumed.**  No assembled source sentence and no source
  derivation exists here; see the residue section of
  `ZFCinPA.CrossLevelSource`.

The `#print axioms` lines must show only Lean's three standard classical
axioms.
-/

namespace LeanProofs.ZFCinPA.CrossLevelSourceAudit

open LeanProofs.ZFCinPA
open LeanProofs.ZFCinPA.SuccessorSources
open LeanProofs.ZFCinPA.TemplateEvaluation

/-! ## Free-slot bounds -/

#check @free_isFormCode1D2
#check @free_univEnv0D2
#check @free_quantBounded02

/-! ## The source formulas -/

#check @srcBoundedAt
#check @srcBoundedAtSucc
#check @srcCrossLevel
#check @srcCrossLevelSucc

/-! ## Translation identities -/

#check @translate_srcBoundedAt
#check @translate_srcBoundedAtSucc
#check @translate_srcCrossLevel
#check @translate_srcCrossLevel_formula
#check @translate_srcCrossLevelSucc
#check @translate_srcCrossLevelSucc_formula

/-! ## Free-variable-freeness -/

#check @fvFree_srcBoundedAt
#check @fvFree_srcBoundedAtSucc
#check @fvFree_srcCrossLevel
#check @fvFree_srcCrossLevelSucc

/-! ## The readings -/

#check @eval_srcBoundedAt
#check @eval_srcBoundedAtSucc
#check @eval_srcCrossLevel
#check @eval_srcCrossLevelSucc
#check @decided_of_srcCrossLevel
#check @decided_of_srcCrossLevelSucc
#check @levelLaws_of_srcCrossLevel

/-! ## The abstract field the readings land on -/

#check @EnlargedFields.LevelLaws

/-! ## Assumption audit -/

#print axioms free_isFormCode1D2
#print axioms free_univEnv0D2
#print axioms free_quantBounded02
#print axioms srcBoundedAt
#print axioms srcBoundedAtSucc
#print axioms srcCrossLevel
#print axioms srcCrossLevelSucc
#print axioms translate_srcBoundedAt
#print axioms translate_srcBoundedAtSucc
#print axioms translate_srcCrossLevel
#print axioms translate_srcCrossLevel_formula
#print axioms translate_srcCrossLevelSucc
#print axioms translate_srcCrossLevelSucc_formula
#print axioms fvFree_srcBoundedAt
#print axioms fvFree_srcBoundedAtSucc
#print axioms fvFree_srcCrossLevel
#print axioms fvFree_srcCrossLevelSucc
#print axioms eval_srcBoundedAt
#print axioms eval_srcBoundedAtSucc
#print axioms eval_srcCrossLevel
#print axioms eval_srcCrossLevelSucc
#print axioms decided_of_srcCrossLevel
#print axioms decided_of_srcCrossLevelSucc
#print axioms levelLaws_of_srcCrossLevel

end LeanProofs.ZFCinPA.CrossLevelSourceAudit
