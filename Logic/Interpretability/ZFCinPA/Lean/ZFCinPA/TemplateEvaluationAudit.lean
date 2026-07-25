import ZFCinPA.TemplateEvaluation

/-!
# Audit for the bottom of the evaluation bridge

Three things must stay visible.

* **Where equality is consumed.**  `lMap_setHom_eq_standard` is the single
  place in the bridge that uses `Structure.Eq srcL X`.  Everything above it
  works with the induced membership relation `templateMem` and never
  touches the structure again.
* **The bundle is genuine.**  `zfcAxioms_of_template` produces goal 2's
  own nine-axiom record over `templateMem X`, by
  `ZFCinPA.zfcAxioms_of_models` — not a weakened copy.
* **The environment invariant is the same one `eval_toSet` uses.**  `Corr`
  is exactly the hypothesis pair of `ZFCinPA.eval_toSet`, and `Corr.cons`
  is its binder step; `eval_liftP` is the composite.  No arity side
  condition appears, because the invariant reads bound and free Foundation
  slots into one repository environment uniformly.

The `#print axioms` lines must show only Lean's three standard classical
axioms.
-/

namespace LeanProofs.ZFCinPA.TemplateEvaluationAudit

open LeanProofs.ZFCinPA
open LeanProofs.ZFCinPA.TemplateEvaluation

/-! ## Structure setup -/

#check @templateMem
#check @templateSetStructure
#check @memRel_templateSetStructure
#check @lMap_setHom_eq_standard
#check @models_zfc_of_template
#check @zfcAxioms_of_template
#check @zfAxioms_of_template

/-! ## The environment invariant and the leaves -/

#check @Corr
#check @Corr.zero
#check @Corr.cons
#check @eval_liftP

/-! ## The placeholders and the induced previous level -/

#check @templateRel
#check @eval_srcPProp
#check @templateNum
#check @templateClos
#check @eval_srcNumAt
#check @eval_srcClsAt
#check @templateLevel

/-! ## Assumption audit -/

#print axioms lMap_setHom_eq_standard
#print axioms models_zfc_of_template
#print axioms zfcAxioms_of_template
#print axioms zfAxioms_of_template
#print axioms Corr.cons
#print axioms eval_liftP
#print axioms eval_srcPProp
#print axioms eval_srcNumAt
#print axioms eval_srcClsAt

end LeanProofs.ZFCinPA.TemplateEvaluationAudit
