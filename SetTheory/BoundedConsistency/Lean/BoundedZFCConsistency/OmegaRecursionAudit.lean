import BoundedZFCConsistency.OmegaRecursion

/-!
# Kernel audit for recursion along the internal omega

This deliberately small module checks the public interface of
`BoundedZFCConsistency.OmegaRecursion` and prints the axioms of its substantive
theorems.  Keeping the audit separate prevents diagnostic output from becoming
part of the library-facing module.
-/

namespace LeanProofs.BoundedZFCConsistency.OmegaRecursionAudit

open SetTheory
open LeanProofs.BoundedZFCConsistency

/-! ## Internal linearity of the omega -/

#check @fSuccStepF
#check @fSuccStepF_spec
#check @succ_le_of_lt
#check @fZeroLeF
#check @fZeroLeF_spec
#check @vempty_le_nat
#check @fTrichF
#check @fTrichF_spec
#check @nat_linear

/-! ## The definable step -/

#check @defOp_functional
#check @fOpF
#check @fOpF_spec

/-! ## The parametrized approximations -/

#check @ApproxG
#check @fAppG5
#check @fAppG5_spec
#check @fApproxG
#check @fApproxG_spec
#check @ApproxG_base
#check @ApproxG_extend
#check @ApproxG_exists
#check @fApproxAgreeF
#check @fApproxAgreeF_spec
#check @ApproxG_agree

/-! ## The stage relation and the recursion set -/

#check @ThetaG
#check @fThetaG
#check @fThetaG_spec
#check @envRec
#check @thetaG_zero
#check @thetaG_succ
#check @thetaG_total
#check @thetaG_unique
#check @psiGraphG
#check @psiGraphG_rel
#check @psiGraphG_functional
#check @recFun
#check @recFun_spec
#check @recFun_pair

/-! ## Internal functions and application -/

#check @IsFunctionOn
#check @fFunOnF
#check @fFunOnF_spec
#check @applyV_exists
#check @applyV
#check @applyV_mem
#check @applyV_eq
#check @applyV_iff
#check @fApplyF
#check @fApplyF_spec

/-! ## Existence and uniqueness -/

#check @recFun_isFunctionOn
#check @recFun_apply_theta
#check @recFun_zero
#check @recFun_succ
#check @omega_recursion
#check @fAgreeF
#check @fAgreeF_spec
#check @omega_recursion_agree
#check @omega_recursion_unique

/-! ## Assumption audit

The internal set operators of `ZF.Zf` are carved out with `Exists.choose`, and
internal application is defined the same way, so `Classical.choice` is expected
throughout; nothing beyond Lean's three standard axioms should appear, and in
particular no `sorry` and no theory-specific axiom.  Linearity, existence, and
uniqueness are the ones that matter: they are unconditional in the model, so any
hidden assumption would show up here. -/

#print axioms succ_le_of_lt
#print axioms vempty_le_nat
#print axioms nat_linear

#print axioms defOp_functional
#print axioms fOpF_spec
#print axioms fAppG5_spec
#print axioms fApproxG_spec
#print axioms ApproxG_base
#print axioms ApproxG_extend
#print axioms ApproxG_exists
#print axioms ApproxG_agree

#print axioms fThetaG_spec
#print axioms thetaG_zero
#print axioms thetaG_succ
#print axioms thetaG_total
#print axioms thetaG_unique
#print axioms psiGraphG_rel
#print axioms psiGraphG_functional
#print axioms recFun_spec
#print axioms recFun_pair

#print axioms fFunOnF_spec
#print axioms applyV_mem
#print axioms applyV_eq
#print axioms applyV_iff
#print axioms fApplyF_spec

#print axioms recFun_isFunctionOn
#print axioms recFun_zero
#print axioms recFun_succ
#print axioms omega_recursion
#print axioms fAgreeF_spec
#print axioms omega_recursion_agree
#print axioms omega_recursion_unique

end LeanProofs.BoundedZFCConsistency.OmegaRecursionAudit
