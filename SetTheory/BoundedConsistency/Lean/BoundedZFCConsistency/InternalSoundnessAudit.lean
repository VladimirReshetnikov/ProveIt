import BoundedZFCConsistency.InternalSoundness

/-!
# Kernel audit for coded renaming and the substitution lemma

This deliberately small module checks the public interface of
`BoundedZFCConsistency.InternalSoundness` and prints the axioms of its
substantive theorems.  Keeping the audit separate prevents diagnostic output
from becoming part of the library-facing module.
-/

namespace LeanProofs.BoundedZFCConsistency.InternalSoundnessAudit

open SetTheory
open LeanProofs.BoundedZFCConsistency

/-! ## Internal function extensionality -/

#check @funOn_ext

/-! ## Variable maps and the binder shift -/

#check @IsVarMap
#check @isVarMap_apply
#check @isVarMap_functional
#check @isVarMap_mem
#check @fIsOmegaF
#check @fIsOmegaF_spec
#check @fVarMapF
#check @fVarMapF_spec
#check @psiSuccValF
#check @psiSuccValF_rel
#check @succVals
#check @succVals_mem
#check @succVals_isVarMap
#check @succVals_apply
#check @upV
#check @upV_isVarMap
#check @upV_zero
#check @upV_succ

/-! ## The three named variable maps -/

#check @idMap
#check @idMap_isVarMap
#check @idMap_apply
#check @succMap
#check @succMap_isVarMap
#check @succMap_apply
#check @instMap
#check @instMap_isVarMap
#check @instMap_zero
#check @instMap_succ

/-! ## Composition of an environment with a variable map -/

#check @psiCompF
#check @psiCompF_rel
#check @compV
#check @compV_mem
#check @compV_isEnvOn
#check @compV_apply
#check @compV_econs_upV
#check @compV_succMap
#check @compV_instMap

/-! ## The renaming graph -/

#check @RenStep
#check @renStep_mono
#check @RenClosed
#check @renClosed_empty
#check @renClosed_cup
#check @renClosed_insert
#check @RenCertifies
#check @Renames
#check @Renames.isVarMap
#check @renames_of_step

/-! ### Introduction and inversion -/

#check @renames_memAtom
#check @renames_eqAtom
#check @renames_bot
#check @renames_imp
#check @renames_and
#check @renames_or
#check @renames_all
#check @renames_ex

#check @renames_memAtom_inv
#check @renames_eqAtom_inv
#check @renames_bot_inv
#check @renames_imp_inv
#check @renames_and_inv
#check @renames_or_inv
#check @renames_all_inv
#check @renames_ex_inv

/-! ### The object-language rendering -/

#check @fSuccValsF
#check @fSuccValsF_spec
#check @fUpF
#check @fUpF_spec
#check @fRenAtomF
#check @fRenAtomF_spec
#check @fRenBinF
#check @fRenBinF_spec
#check @fRenQuantF
#check @fRenQuantF_spec
#check @fRenStepF
#check @fRenStepF_spec
#check @fRenClosedF
#check @fRenClosedF_spec
#check @fRenamesF
#check @fRenamesF_spec

/-! ## Totality, single-valuedness, and the operator -/

#check @RenTotal
#check @fRenTotalF_spec
#check @renTotal_of_isFormCodeSem
#check @RenUnique
#check @fRenUniqueF_spec
#check @renUnique_of_isFormCodeSem
#check @renameV
#check @renames_renameV
#check @renameV_eq
#check @renameV_memAtom
#check @renameV_eqAtom
#check @renameV_bot
#check @renameV_imp
#check @renameV_and
#check @renameV_or
#check @renameV_all
#check @renameV_ex
#check @renCode_of_isFormCodeSem
#check @renames_isFormCodeSem
#check @renameV_isFormCodeSem

/-! ## The substitution lemma -/

#check @fSatInF
#check @fSatInF_spec
#check @fCompF
#check @fCompF_spec
#check @SubstOK
#check @fSubstOKF
#check @fSubstOKF_spec
#check @substOK_of_isFormCodeSem
#check @satIn_renames
#check @satIn_renameV
#check @satIn_renameV_succMap
#check @satIn_renameV_instMap

/-! ## Agreement with external renamings -/

#check @AgreesWith
#check @upV_agreesWith
#check @succMap_agreesWith
#check @instMap_agreesWith
#check @renames_formCode
#check @renameV_formCode
#check @renameV_formCode_succMap
#check @renameV_formCode_instMap

/-! ## Assumption audit

The internal set operators of `ZF.Zf` are carved out with `Exists.choose`, the
Replacement images of this module inherit that, `applyV` and `renameV` are
conditional choices, and the code-induction property of the substitution lemma
mentions `vbit`, which branches on an arbitrary proposition.  `Classical.choice`
is therefore expected throughout; nothing beyond Lean's three standard axioms
should appear, and in particular no `sorry`, no `native_decide`, and no
theory-specific axiom.

The ones that matter are the four unconditional `iff`s between a `Form` and the
property an induction carries — `fRenamesF_spec`, `fRenTotalF_spec`,
`fRenUniqueF_spec` and `fSubstOKF_spec` — where a hidden assumption would show
up; the three composition identities, which are the equational content of the
binder bookkeeping; `renTotal_of_isFormCodeSem` and
`renUnique_of_isFormCodeSem`, which make renaming an operation at all; and
`satIn_renames` with its two specializations, which are the interface a later
module consumes. -/

#print axioms funOn_ext

#print axioms succVals_mem
#print axioms succVals_isVarMap
#print axioms succVals_apply
#print axioms upV_isVarMap
#print axioms upV_zero
#print axioms upV_succ

#print axioms idMap_apply
#print axioms succMap_apply
#print axioms instMap_zero
#print axioms instMap_succ

#print axioms compV_mem
#print axioms compV_isEnvOn
#print axioms compV_apply
#print axioms compV_econs_upV
#print axioms compV_succMap
#print axioms compV_instMap

#print axioms renStep_mono
#print axioms renClosed_cup
#print axioms renClosed_insert
#print axioms renames_of_step

#print axioms renames_memAtom
#print axioms renames_all
#print axioms renames_memAtom_inv
#print axioms renames_imp_inv
#print axioms renames_all_inv

#print axioms fSuccValsF_spec
#print axioms fUpF_spec
#print axioms fRenAtomF_spec
#print axioms fRenBinF_spec
#print axioms fRenQuantF_spec
#print axioms fRenStepF_spec
#print axioms fRenClosedF_spec
#print axioms fRenamesF_spec

#print axioms fRenTotalF_spec
#print axioms renTotal_of_isFormCodeSem
#print axioms fRenUniqueF_spec
#print axioms renUnique_of_isFormCodeSem
#print axioms renameV_eq
#print axioms renameV_imp
#print axioms renameV_all
#print axioms renCode_of_isFormCodeSem
#print axioms renameV_isFormCodeSem

#print axioms fSatInF_spec
#print axioms fCompF_spec
#print axioms fSubstOKF_spec
#print axioms substOK_of_isFormCodeSem
#print axioms satIn_renames
#print axioms satIn_renameV
#print axioms satIn_renameV_succMap
#print axioms satIn_renameV_instMap

#print axioms upV_agreesWith
#print axioms renames_formCode
#print axioms renameV_formCode
#print axioms renameV_formCode_succMap
#print axioms renameV_formCode_instMap

end LeanProofs.BoundedZFCConsistency.InternalSoundnessAudit
