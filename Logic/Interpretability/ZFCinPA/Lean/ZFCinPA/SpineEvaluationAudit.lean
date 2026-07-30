import ZFCinPA.SpineEvaluation

/-!
# Audit for the closure spine's evaluation

Three things must stay visible.

* **The readings are goal 2's own predicates.**  `eval_srcClosStep`'s right
  side is `BoundedZFCConsistency.LevelClosed`, and `eval_srcJustRow`'s is
  `LevelJustified` — the very predicates
  `ZFCinPA.EnlargedFields.stepGood_of_levelLaws` and
  `ZFCinPA.LocalStepTransfer.localStepLaws_step` are stated over.  Nothing
  is approximated and nothing is weakened.
* **The previous level is the placeholder one.**  Every reading is over
  `TemplateEvaluation.templateLevel`, i.e.
  `∃ n C, Num n ∧ Clos n C ∧ ⟨c, e, b⟩ ∈ C`, which is the abstract
  ternary relation those theorems quantify over.  `eval_srcLvlInstP_triple`
  is the source-level counterpart of the hypothesis `hl` that goal 2's
  level `…_spec` theorems carry.
* **The environment clause is essential.**  `eval_srcJustRow` consumes
  `IsUnivEnv H (e 1)`, exactly as `fLevelJustifiedF_spec` consumes `hE`,
  and `eval_srcClosStep` therefore is a two-direction argument rather than
  a congruence.

The `#print axioms` lines must show only Lean's three standard classical
axioms.
-/

namespace LeanProofs.ZFCinPA.SpineEvaluationAudit

open LeanProofs.ZFCinPA
open LeanProofs.ZFCinPA.TemplateEvaluation

/-! ## The previous-level slot -/

#check @eval_srcLvlInstP
#check @eval_srcLvlInst
#check @eval_srcLvlInstP_triple

/-! ## The clauses, the row and the step -/

#check @eval_srcAllClause
#check @eval_srcExClause
#check @eval_srcJustRow
#check @eval_srcClosStep

/-! ## The goal-2 predicates they land on -/

#check @BoundedZFCConsistency.LevelJustified
#check @BoundedZFCConsistency.LevelClosed

/-! ## Assumption audit -/

#print axioms eval_srcLvlInstP
#print axioms eval_srcLvlInst
#print axioms eval_srcLvlInstP_triple
#print axioms eval_srcAllClause
#print axioms eval_srcExClause
#print axioms eval_srcJustRow
#print axioms eval_srcClosStep

end LeanProofs.ZFCinPA.SpineEvaluationAudit
