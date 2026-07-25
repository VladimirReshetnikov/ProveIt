import ZFCinPA.TarskiEvaluation

/-!
# Audit for the two Tarski certificate-field readings

Five things must stay visible.

* **Both Tarski fields are read, at both levels.**  `eval_srcTarskiElim`,
  `eval_srcTarskiElimSucc`, `eval_srcTarskiIntro` and
  `eval_srcTarskiIntroSucc` are *theorems*: in every template structure
  with genuine equality, the fixed source formulas
  `SuccessorSources.srcTarskiElim`, `srcTarskiElimSucc`, `srcTarskiIntro`
  and `srcTarskiIntroSucc` evaluate to `EnlargedFields.TarskiElim` /
  `TarskiIntro` at `templateLevel` and at `templateStepLevel`.
* **The bundles are the abstract ones.**  The right-hand sides are goal
  2's own `EnlargedFields.TarskiElim`/`TarskiIntro` at an *arbitrary*
  ternary relation — the very structures `EnlargedFields.LevelLaws`
  bundles and `EnlargedFields.stepGood_of_levelLaws` consumes.  Nothing
  is specialized to the real hierarchy, and no clause is weakened: read
  `#check @EnlargedFields.TarskiElim` and `@EnlargedFields.TarskiIntro`
  next to the readings.
* **The quantifier skeleton's premise order is real.**
  `eval_srcQuantSpine` is stated of an arbitrary body and proved as a
  nested implication, because `fEconsF_spec` consumes `IsUnivEnv.1`.  Its
  statement is the place to check that the fourth slot really is
  `econs d e` and the fifth premise is not silently dropped.
* **No arity side conditions.**  `PolarReading` quantifies over all
  `m w ci ei` with no `ci < m` / `ei < m` guard; that is legitimate only
  because `TemplateEvaluation.Corr` reads bound and free slots uniformly.
  The *translation* lemmas of `ZFCinPA.TarskiSources` do carry those
  guards, and they are unaffected.
* **Nothing new is assumed.**  This module adds no `crossLevel` source
  field, no source `CodeInduction`, no `Num`-uniqueness antecedent and no
  assembled source sentence; items 2–5 of `ZFCinPA.FieldEvaluation`'s
  residue are untouched, and the residue section of
  `ZFCinPA.TarskiEvaluation` restates that.

The `#print axioms` lines must show only Lean's three standard classical
axioms.
-/

namespace LeanProofs.ZFCinPA.TarskiEvaluationAudit

open LeanProofs.ZFCinPA
open LeanProofs.ZFCinPA.TemplateEvaluation

/-! ## The base correspondences -/

#check @corr2
#check @corr4
#check @corr5

/-! ## The three skeletons -/

#check @eval_srcConnSpine
#check @eval_srcQuantSpine
#check @eval_srcBotPiOf

/-! ## The polarized-gadget reading and the six row shapes -/

#check @PolarReading
#check @eval_connElimOr
#check @eval_connElimAnd
#check @eval_connIntroOr
#check @eval_connIntroAnd
#check @eval_quantElim
#check @eval_quantIntro
#check @eval_botPi

/-! ## The two fields, abstractly and at the two levels -/

#check @eval_srcTarskiElimOf
#check @eval_srcTarskiIntroOf
#check @eval_srcTarskiElim
#check @eval_srcTarskiElimSucc
#check @eval_srcTarskiIntro
#check @eval_srcTarskiIntroSucc

/-! ## The abstract bundles the readings land on -/

#check @EnlargedFields.TarskiElim
#check @EnlargedFields.TarskiIntro
#check @EnlargedFields.LevelLaws

/-! ## Assumption audit -/

#print axioms corr2
#print axioms corr4
#print axioms corr5
#print axioms eval_srcConnSpine
#print axioms eval_srcQuantSpine
#print axioms eval_srcBotPiOf
#print axioms PolarReading
#print axioms eval_connElimOr
#print axioms eval_connElimAnd
#print axioms eval_connIntroOr
#print axioms eval_connIntroAnd
#print axioms eval_quantElim
#print axioms eval_quantIntro
#print axioms eval_botPi
#print axioms eval_srcTarskiElimOf
#print axioms eval_srcTarskiIntroOf
#print axioms eval_srcTarskiElim
#print axioms eval_srcTarskiElimSucc
#print axioms eval_srcTarskiIntro
#print axioms eval_srcTarskiIntroSucc

end LeanProofs.ZFCinPA.TarskiEvaluationAudit
