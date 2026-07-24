import BoundedZFCConsistency.InternalSat

/-!
# Kernel audit for internal satisfaction by certificates

This deliberately small module checks the public interface of
`BoundedZFCConsistency.InternalSat` and prints the axioms of its substantive
theorems.  Keeping the audit separate prevents diagnostic output from becoming
part of the library-facing module.
-/

namespace LeanProofs.BoundedZFCConsistency.InternalSatAudit

open SetTheory
open LeanProofs.BoundedZFCConsistency

/-! ## Internal set structures -/

#check @IsSetStructure

/-! ## Case analysis on internal natural numbers -/

#check @fZeroOrSuccF
#check @fZeroOrSuccF_spec
#check @nat_zero_or_succ

/-! ## Internal environments -/

#check @IsEnvOn
#check @isEnvOn_apply
#check @psiConstEnvF
#check @psiConstEnvF_rel
#check @psiConstEnvF_functional
#check @constEnv
#check @constEnv_spec
#check @constEnv_isEnvOn
#check @exists_isEnvOn

/-! ## The shift -/

#check @psiShiftF
#check @psiShiftF_rel
#check @psiShiftF_functional
#check @shiftImg
#check @shiftImg_spec
#check @econs
#check @econs_spec
#check @econs_functional
#check @econs_isEnvOn
#check @econs_zero
#check @econs_succ
#check @fEconsF
#check @fEconsF_spec

/-! ## Environments in the object language -/

#check @fFunOnOmegaF
#check @fFunOnOmegaF_spec
#check @fEnvOnF
#check @fEnvOnF_spec

/-! ## Truth bits and evaluation triples -/

#check @vbit
#check @vbit_pos
#check @vbit_neg
#check @vbit_congr
#check @vbit_eq_one
#check @vbit_eq_zero
#check @satTriple
#check @satTriple_inj

/-! ## Macros for the step -/

#check @fTripleMemF
#check @fTripleMemF_spec
#check @fTagPairF
#check @fTagPairF_spec
#check @fTagUnF
#check @fTagUnF_spec
#check @fShiftTripleMemF
#check @fShiftTripleMemF_spec
#check @fBitOfF
#check @fBitOfF_spec

/-! ## The local Tarski step -/

#check @Justified
#check @fJustAtomF
#check @fJustAtomF_spec
#check @fJustBotF
#check @fJustBotF_spec
#check @fJustBinF
#check @fJustBinF_spec
#check @fJustQuantF
#check @fJustQuantF_spec
#check @fJustifiedF
#check @fJustifiedF_spec

/-! ## Certificates -/

#check @SatClosed
#check @fSatClosedF
#check @fSatClosedF_spec
#check @Certifies
#check @Certifies.justified
#check @Certifies.envOn

/-! ## Inverting the step at a known tag -/

#check @justified_memAtom
#check @justified_eqAtom
#check @justified_bot
#check @justified_imp
#check @justified_and
#check @justified_or
#check @justified_all
#check @justified_ex

/-! ## Functionality -/

#check @BitUnique
#check @fBitUniqueF
#check @envBitUnique
#check @fBitUniqueF_spec
#check @certificate_bit_unique
#check @certificate_functional

/-! ## Assumption audit

The internal set operators of `ZF.Zf` are carved out with `Exists.choose`,
internal application is defined the same way, and `vbit` branches on an
arbitrary proposition, so `Classical.choice` is expected throughout; nothing
beyond Lean's three standard axioms should appear, and in particular no
`sorry`, no `native_decide`, and no theory-specific axiom.

The ones that matter are the satisfaction specs — each is an unconditional
`iff` between a `Form` and its intended meaning, so a hidden assumption would
show up here — and functionality, which is the module's theorem. -/

#print axioms nat_zero_or_succ
#print axioms constEnv_spec
#print axioms constEnv_isEnvOn
#print axioms exists_isEnvOn

#print axioms psiShiftF_rel
#print axioms shiftImg_spec
#print axioms econs_spec
#print axioms econs_functional
#print axioms econs_isEnvOn
#print axioms econs_zero
#print axioms econs_succ
#print axioms fEconsF_spec

#print axioms fFunOnOmegaF_spec
#print axioms fEnvOnF_spec

#print axioms vbit_congr
#print axioms vbit_eq_one
#print axioms vbit_eq_zero
#print axioms satTriple_inj

#print axioms fTripleMemF_spec
#print axioms fTagPairF_spec
#print axioms fTagUnF_spec
#print axioms fShiftTripleMemF_spec
#print axioms fBitOfF_spec

#print axioms fJustAtomF_spec
#print axioms fJustBotF_spec
#print axioms fJustBinF_spec
#print axioms fJustQuantF_spec
#print axioms fJustifiedF_spec

#print axioms fSatClosedF_spec
#print axioms justified_memAtom
#print axioms justified_eqAtom
#print axioms justified_bot
#print axioms justified_imp
#print axioms justified_and
#print axioms justified_or
#print axioms justified_all
#print axioms justified_ex

#print axioms fBitUniqueF_spec
#print axioms certificate_bit_unique
#print axioms certificate_functional

end LeanProofs.BoundedZFCConsistency.InternalSatAudit
