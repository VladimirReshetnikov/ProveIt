import BoundedZFCConsistency.UniverseTruthZero

/-!
# Kernel audit for quantifier-free truth over the universe

This deliberately small module checks the public interface of
`BoundedZFCConsistency.UniverseTruthZero` and prints the axioms of its
substantive theorems.  Keeping the audit separate prevents diagnostic output
from becoming part of the library-facing module.
-/

namespace LeanProofs.BoundedZFCConsistency.UniverseTruthZeroAudit

open SetTheory
open LeanProofs.BoundedZFCConsistency

/-! ## Environments over the universe -/

#check @IsUnivEnv
#check @isUnivEnv_mem
#check @exists_isUnivEnv
#check @fUnivEnvF
#check @fUnivEnvF_spec

/-! ## The quantifier-free code domain -/

#check @QFClosed
#check @qfClosed_of_formulaClosed
#check @exists_qfClosed
#check @IsQFCodeSem
#check @isFormCodeSem_of_isQFCodeSem
#check @isQFCodeSem_memAtom
#check @isQFCodeSem_eqAtom
#check @isQFCodeSem_bot
#check @isQFCodeSem_imp
#check @isQFCodeSem_and
#check @isQFCodeSem_or
#check @fQFClosedF
#check @fQFClosedF_spec
#check @fIsQFCodeF
#check @fIsQFCodeF_spec
#check @isQFCodeSem_ind_form
#check @isQFCodeSem_ind

/-! ## Agreement with internal rank zero -/

#check @ranks_zero_of_isQFCodeSem
#check @quantBounded_zero_of_isQFCodeSem
#check @not_quantBounded_zero_all
#check @not_quantBounded_zero_ex
#check @fQFOfBoundF
#check @fQFOfBoundF_spec
#check @isQFCodeSem_of_quantBounded_zero
#check @isQFCodeSem_iff_quantBounded_zero

/-! ## The local step -/

#check @QFJustified
#check @fQFJustifiedF
#check @fQFJustifiedF_spec
#check @qfJustified_mono
#check @qfJustified_bit
#check @qfJustified_memAtom
#check @qfJustified_eqAtom
#check @qfJustified_bot
#check @qfJustified_imp
#check @qfJustified_and
#check @qfJustified_or

/-! ## Certificates -/

#check @QFSatClosed
#check @fQFSatClosedF
#check @fQFSatClosedF_spec
#check @QFCertifies
#check @QFCertifies.justified
#check @QFCertifies.envOn
#check @qfSatClosed_empty
#check @qfSatClosed_cup
#check @qfSatClosed_insert
#check @qfCertifies_of_step

/-! ## Single-valuedness and totality -/

#check @QFBitUnique
#check @fQFBitUniqueF
#check @fQFBitUniqueF_spec
#check @qfCertificate_bit_unique
#check @qfCertificate_functional
#check @QFTotal
#check @fQFTotalF
#check @fQFTotalF_spec
#check @qfCertificate_total

/-! ## The truth predicate and its Tarski clauses -/

#check @QFTrue
#check @qfTrue_iff_bit_eq_one
#check @qfCertifies_bit
#check @exists_qfCertifies
#check @qfTrue_memAtom
#check @qfTrue_eqAtom
#check @qfTrue_bot
#check @qfTrue_imp
#check @qfTrue_and
#check @qfTrue_or

/-! ## Agreement with the metatheory -/

#check @IsQuantFree
#check @isQuantFree_iff_quantifierBounded_zero
#check @formCode_isQFCodeSem
#check @qfTrue_formCode_iff
#check @qfTrue_formCode_iff_apply

/-! ## Assumption audit

The internal set operators of `ZF.Zf` are carved out with `Exists.choose`, the
Separation and Replacement images inherit that, and `vbit` branches on an
arbitrary proposition, so `Classical.choice` is expected throughout; nothing
beyond Lean's three standard axioms should appear, and in particular no
`sorry`, no `native_decide`, and no theory-specific axiom.

The ones that matter are the three unconditional `iff`s between a `Form` and
the property an induction carries — `fQFClosedF_spec`, `fQFBitUniqueF_spec`
and `fQFTotalF_spec` — where a hidden assumption would show up; the two halves
of the truth predicate, `qfCertificate_functional` and `qfCertificate_total`;
the rank agreement `isQFCodeSem_iff_quantBounded_zero`; the six Tarski clauses,
which are the interface later modules consume; and `qfTrue_formCode_iff`, the
bridge back to the metatheory. -/

#print axioms fUnivEnvF_spec
#print axioms exists_isUnivEnv

#print axioms exists_qfClosed
#print axioms fQFClosedF_spec
#print axioms fIsQFCodeF_spec
#print axioms isQFCodeSem_ind_form
#print axioms isQFCodeSem_ind

#print axioms ranks_zero_of_isQFCodeSem
#print axioms quantBounded_zero_of_isQFCodeSem
#print axioms not_quantBounded_zero_all
#print axioms not_quantBounded_zero_ex
#print axioms fQFOfBoundF_spec
#print axioms isQFCodeSem_of_quantBounded_zero
#print axioms isQFCodeSem_iff_quantBounded_zero

#print axioms fQFJustifiedF_spec
#print axioms qfJustified_mono
#print axioms qfJustified_bit
#print axioms qfJustified_memAtom
#print axioms qfJustified_eqAtom
#print axioms qfJustified_bot
#print axioms qfJustified_imp
#print axioms qfJustified_and
#print axioms qfJustified_or

#print axioms fQFSatClosedF_spec
#print axioms qfSatClosed_empty
#print axioms qfSatClosed_cup
#print axioms qfSatClosed_insert
#print axioms qfCertifies_of_step

#print axioms fQFBitUniqueF_spec
#print axioms qfCertificate_bit_unique
#print axioms qfCertificate_functional
#print axioms fQFTotalF_spec
#print axioms qfCertificate_total

#print axioms qfTrue_iff_bit_eq_one
#print axioms qfCertifies_bit
#print axioms exists_qfCertifies
#print axioms qfTrue_memAtom
#print axioms qfTrue_eqAtom
#print axioms qfTrue_bot
#print axioms qfTrue_imp
#print axioms qfTrue_and
#print axioms qfTrue_or

#print axioms isQuantFree_iff_quantifierBounded_zero
#print axioms formCode_isQFCodeSem
#print axioms qfTrue_formCode_iff
#print axioms qfTrue_formCode_iff_apply

end LeanProofs.BoundedZFCConsistency.UniverseTruthZeroAudit
