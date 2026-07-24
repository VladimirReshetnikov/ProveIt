import BoundedZFCConsistency.CodePredicate

/-!
# Kernel audit for the "codes a formula" predicate

This deliberately small module checks the public interface of
`BoundedZFCConsistency.CodePredicate` and prints the axioms of its substantive
theorems.  Keeping the audit separate prevents diagnostic output from becoming
part of the library-facing module.
-/

namespace LeanProofs.BoundedZFCConsistency.CodePredicateAudit

open SetTheory
open LeanProofs.BoundedZFCConsistency

/-! ## The internal omega as an intersection -/

#check @omega_inductive
#check @mem_omega_iff

/-! ## The semantic predicate -/

#check @FormulaClosed
#check @FormulaClosed.memAtom
#check @FormulaClosed.eqAtom
#check @FormulaClosed.bot
#check @FormulaClosed.imp
#check @FormulaClosed.conj
#check @FormulaClosed.disj
#check @FormulaClosed.all
#check @FormulaClosed.ex
#check @IsFormCodeSem

#check @isFormCodeSem_memAtom
#check @isFormCodeSem_eqAtom
#check @isFormCodeSem_bot
#check @isFormCodeSem_imp
#check @isFormCodeSem_and
#check @isFormCodeSem_or
#check @isFormCodeSem_all
#check @isFormCodeSem_ex

/-! ## The two correctness facts -/

#check @formCode_isFormCodeSem
#check @isFormCodeSem_ind_form
#check @isFormCodeSem_ind

/-! ## The object-language predicate -/

#check @fNatF
#check @fNatF_spec
#check @fTagPairMemF
#check @fTagPairMemF_spec
#check @fTagMemF
#check @fTagMemF_spec
#check @fTagEmptyMemF
#check @fTagEmptyMemF_spec
#check @fClAtomF
#check @fClAtomF_spec
#check @fClBinF
#check @fClBinF_spec
#check @fClUnF
#check @fClUnF_spec
#check @fFormulaClosedF
#check @fFormulaClosedF_spec
#check @fIsFormCodeF
#check @fIsFormCodeF_spec
#check @fIsFormCodeF_formCode

/-! ## Assumption audit

The internal set operators of `ZF.Zf` are carved out with `Exists.choose`, so
`Classical.choice` is expected throughout; nothing beyond Lean's three standard
axioms should appear, and in particular no `sorry` and no theory-specific
axiom. -/

#print axioms omega_inductive
#print axioms mem_omega_iff
#print axioms formCode_isFormCodeSem
#print axioms isFormCodeSem_ind_form
#print axioms isFormCodeSem_ind
#print axioms fNatF_spec
#print axioms fTagPairMemF_spec
#print axioms fTagMemF_spec
#print axioms fTagEmptyMemF_spec
#print axioms fClAtomF_spec
#print axioms fClBinF_spec
#print axioms fClUnF_spec
#print axioms fFormulaClosedF_spec
#print axioms fIsFormCodeF_spec
#print axioms fIsFormCodeF_formCode

end LeanProofs.BoundedZFCConsistency.CodePredicateAudit
