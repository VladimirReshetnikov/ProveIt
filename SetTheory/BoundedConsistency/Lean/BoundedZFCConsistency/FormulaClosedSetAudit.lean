import BoundedZFCConsistency.FormulaClosedSet

/-!
# Kernel audit for the formula-closed set

This deliberately small module checks the public interface of
`BoundedZFCConsistency.FormulaClosedSet` and prints the axioms of its
substantive theorems.  Keeping the audit separate prevents diagnostic output
from becoming part of the library-facing module.
-/

namespace LeanProofs.BoundedZFCConsistency.FormulaClosedSetAudit

open SetTheory
open LeanProofs.BoundedZFCConsistency

/-! ## The reduction -/

#check @formulaClosed_of_pairClosed

/-! ## The pair image and the step operator -/

#check @psiKpF
#check @psiKpF_rel
#check @psiKpF_functional
#check @kpImg
#check @kpImg_spec
#check @psiPImgF
#check @psiPImgF_rel
#check @psiPImgF_functional
#check @pairImg
#check @pairImg_spec

#check @pairStep
#check @pairStep_spec
#check @pairStep_infl
#check @pairStep_mono
#check @kpair_mem_pairStep
#check @fPairStepF
#check @fPairStepF_spec
#check @psiStepF
#check @psiStepF_rel
#check @psiStepF_setLike
#check @exists_pairStepClosed

/-! ## The least step-closed set -/

#check @StepClosed
#check @fStepClosedF
#check @fStepClosedF_spec
#check @stepClosure
#check @stepClosure_spec
#check @omega_mem_stepClosure
#check @stepClosure_step
#check @stepClosure_ind
#check @stepClosure_omega_sub
#check @stepClosure_directed

/-! ## The existence theorems and the unconditional induction principles -/

#check @exists_pairClosed
#check @exists_formulaClosed
#check @isFormCodeSem_ind_form'
#check @isFormCodeSem_ind'

/-! ## Assumption audit

The internal set operators of `ZF.Zf` are carved out with `Exists.choose`, so
`Classical.choice` is expected throughout; nothing beyond Lean's three standard
axioms should appear, and in particular no `sorry` and no theory-specific
axiom.  The existence theorem and both induction principles are the ones that
matter: they are unconditional in the model, so any hidden assumption would
show up here. -/

#print axioms formulaClosed_of_pairClosed
#print axioms kpImg_spec
#print axioms pairImg_spec
#print axioms pairStep_spec
#print axioms fPairStepF_spec
#print axioms psiStepF_rel
#print axioms psiStepF_setLike
#print axioms exists_pairStepClosed
#print axioms fStepClosedF_spec
#print axioms stepClosure_spec
#print axioms stepClosure_ind
#print axioms stepClosure_omega_sub
#print axioms stepClosure_directed
#print axioms exists_pairClosed
#print axioms exists_formulaClosed
#print axioms isFormCodeSem_ind_form'
#print axioms isFormCodeSem_ind'

end LeanProofs.BoundedZFCConsistency.FormulaClosedSetAudit
