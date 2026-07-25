import BoundedZFCConsistency.Coding

/-!
# Kernel audit for the internal coding of formulas

This deliberately small module checks the public interface of
`BoundedZFCConsistency.Coding` and prints the axioms of its substantive
theorems.  Keeping the audit separate prevents diagnostic output from becoming
part of the library-facing module.
-/

namespace LeanProofs.BoundedZFCConsistency.CodingAudit

open SetTheory
open LeanProofs.BoundedZFCConsistency

/-! ## Internal numerals -/

#check @natV
#check @natV_zero
#check @natV_succ
#check @natV_mem_omega
#check @vsucc_inj_omega
#check @natV_succ_ne_vempty
#check @natV_inj
#check @natV_ne

/-! ## Formula codes -/

#check @formCode
#check @formCode_fMem
#check @formCode_fEq
#check @formCode_fBot
#check @formCode_fImp
#check @formCode_fAnd
#check @formCode_fOr
#check @formCode_fAll
#check @formCode_fEx
#check @formCode_tag_ne
#check @formCode_inj
#check @formCode_inj_iff

/-! ## Object-language macros for the coding shapes -/

#check @fNumF
#check @fNumF_spec
#check @fTripleF
#check @fTripleF_spec
#check @fTaggedEmptyF
#check @fTaggedEmptyF_spec

/-! ## Assumption audit

The internal set operators of `ZF.Zf` are carved out with `Exists.choose`, so
`Classical.choice` is expected throughout; nothing beyond Lean's three standard
axioms should appear, and in particular no `sorry` and no theory-specific
axiom. -/

#print axioms natV_mem_omega
#print axioms vsucc_inj_omega
#print axioms natV_inj
#print axioms formCode_tag_ne
#print axioms formCode_inj
#print axioms formCode_inj_iff
#print axioms fNumF_spec
#print axioms fTripleF_spec
#print axioms fTaggedEmptyF_spec

end LeanProofs.BoundedZFCConsistency.CodingAudit
