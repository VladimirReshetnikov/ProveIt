import BoundedZFCConsistency.InternalSatTotality

/-!
# Kernel audit for totality of satisfaction certificates

This deliberately small module checks the public interface of
`BoundedZFCConsistency.InternalSatTotality` and prints the axioms of its
substantive theorems.  Keeping the audit separate prevents diagnostic output
from becoming part of the library-facing module.
-/

namespace LeanProofs.BoundedZFCConsistency.InternalSatTotalityAudit

open SetTheory
open LeanProofs.BoundedZFCConsistency

/-! ## Monotonicity and two-valuedness of the step -/

#check @vbit_zero_or_one
#check @justified_bit
#check @justified_mono

/-! ## Step-closed sets -/

#check @satClosed_empty
#check @satClosed_cup

/-! ## The extension step -/

#check @envExtend
#check @psiNewF
#check @psiNewF_spec
#check @tripleBase
#check @tripleBound
#check @mem_tripleBase_of_mem
#check @mem_tripleBase_of_bit
#check @mem_tripleBase_code
#check @satTriple_mem_tripleBound
#check @newTriples
#check @newTriples_shape
#check @satTriple_mem_newTriples
#check @exists_extend

/-! ## Shifting a whole set of environments -/

#check @psiEconsF
#check @psiEconsF_rel
#check @psiEconsF_functional
#check @econsImg
#check @econsImg_spec
#check @chiShiftF
#check @chiShiftF_rel
#check @chiShiftF_setLike
#check @shiftEnvs
#check @shiftEnvs_spec
#check @econs_mem_shiftEnvs
#check @shiftEnvs_isEnvOn

/-! ## Totality -/

#check @TotalOn
#check @fTotalOnF
#check @envTotal
#check @fTotalOnF_spec
#check @totalOn_of_isFormCodeSem
#check @certificate_total

/-! ## The satisfaction relation -/

#check @SatIn
#check @satIn_iff_bit_eq_one
#check @certifies_bit
#check @exists_certifies

/-! ## The Tarski clauses -/

#check @satIn_memAtom
#check @satIn_eqAtom
#check @satIn_bot
#check @satIn_imp
#check @satIn_and
#check @satIn_or
#check @satIn_all
#check @satIn_ex

/-! ## Assumption audit

The internal set operators of `ZF.Zf` are carved out with `Exists.choose`, the
Replacement images and the one-step closure of this module inherit that, and
`vbit` branches on an arbitrary proposition, so `Classical.choice` is expected
throughout; nothing beyond Lean's three standard axioms should appear, and in
particular no `sorry`, no `native_decide`, and no theory-specific axiom.

The ones that matter are `fTotalOnF_spec` — an unconditional `iff` between a
`Form` and the property the induction carries, so a hidden assumption would
show up there — `certificate_total`, which is the module's theorem, and the
eight Tarski clauses, which are the interface later modules consume. -/

#print axioms justified_bit
#print axioms justified_mono
#print axioms satClosed_empty
#print axioms satClosed_cup

#print axioms psiNewF_spec
#print axioms satTriple_mem_tripleBound
#print axioms newTriples_shape
#print axioms satTriple_mem_newTriples
#print axioms exists_extend

#print axioms psiEconsF_rel
#print axioms econsImg_spec
#print axioms chiShiftF_rel
#print axioms chiShiftF_setLike
#print axioms shiftEnvs_spec
#print axioms econs_mem_shiftEnvs
#print axioms shiftEnvs_isEnvOn

#print axioms fTotalOnF_spec
#print axioms totalOn_of_isFormCodeSem
#print axioms certificate_total

#print axioms satIn_iff_bit_eq_one
#print axioms certifies_bit
#print axioms exists_certifies

#print axioms satIn_memAtom
#print axioms satIn_eqAtom
#print axioms satIn_bot
#print axioms satIn_imp
#print axioms satIn_and
#print axioms satIn_or
#print axioms satIn_all
#print axioms satIn_ex

end LeanProofs.BoundedZFCConsistency.InternalSatTotalityAudit
