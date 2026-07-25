import BoundedZFCConsistency.CodedDerivation

/-!
# Kernel audit for coded contexts, coded derivations, and internal soundness

This deliberately small module checks the public interface of
`BoundedZFCConsistency.CodedDerivation` and prints the axioms of its
substantive theorems.  Keeping the audit separate prevents diagnostic output
from becoming part of the library-facing module.
-/

namespace LeanProofs.BoundedZFCConsistency.CodedDerivationAudit

open SetTheory
open LeanProofs.BoundedZFCConsistency

/-! ## The order on numerals -/

#check @natV_lt

/-! ## Coded contexts -/

#check @ctxNil
#check @ctxCons
#check @ctxNil_ne_ctxCons
#check @ctxCons_inj

/-! ### Membership -/

#check @CtxMemStep
#check @ctxMemStep_mono
#check @CtxMemClosed
#check @ctxMemClosed_empty
#check @ctxMemClosed_insert
#check @CtxMemCertifies
#check @MemCtx
#check @memCtx_of_step
#check @memCtx_head
#check @memCtx_tail
#check @memCtx_nil
#check @memCtx_cons_inv
#check @memCtx_cons_iff

/-! ### Being a context -/

#check @CtxStep
#check @ctxStep_mono
#check @CtxClosed
#check @ctxClosed_empty
#check @ctxClosed_insert
#check @IsCtx
#check @isCtx_of_step
#check @isCtx_nil
#check @isCtx_cons
#check @isCtx_cons_inv

/-! ### The object-language rendering of contexts -/

#check @fCtxNilF
#check @fCtxNilF_spec
#check @fCtxConsF
#check @fCtxConsF_spec
#check @fCtxMemStepF
#check @fCtxMemStepF_spec
#check @fCtxMemClosedF
#check @fCtxMemClosedF_spec
#check @fMemCtxF
#check @fMemCtxF_spec
#check @fCtxStepF
#check @fCtxStepF_spec
#check @fCtxClosedF
#check @fCtxClosedF_spec
#check @fIsCtxF
#check @fIsCtxF_spec

/-! ### Quotation of external contexts -/

#check @ctxCode
#check @ctxCode_nil
#check @ctxCode_cons
#check @memCtx_ctxCode
#check @isCtx_ctxCode

/-! ## The context shift -/

#check @fIdMapF
#check @fIdMapF_spec
#check @fSuccMapF
#check @fSuccMapF_spec
#check @ShiftsCtx
#check @fShiftsCtxF
#check @fShiftsCtxF_spec
#check @shiftsCtx_ctxCode

/-! ## Coded derivations -/

#check @DerCite
#check @derCite_mono
#check @derCite_of_natV

#check @DAss
#check @DImpI
#check @DImpE
#check @DBotE
#check @DLem
#check @DAndI
#check @DAndE1
#check @DAndE2
#check @DOrI1
#check @DOrI2
#check @DOrE
#check @DAllI
#check @DAllE
#check @DExI
#check @DExE
#check @DEqRefl
#check @DEqElim

#check @DerStep
#check @derStep_ass
#check @derStep_impI
#check @derStep_impE
#check @derStep_botE
#check @derStep_lem
#check @derStep_andI
#check @derStep_andE1
#check @derStep_andE2
#check @derStep_orI1
#check @derStep_orI2
#check @derStep_orE
#check @derStep_allI
#check @derStep_allE
#check @derStep_exI
#check @derStep_exE
#check @derStep_eqRefl
#check @derStep_eqElim
#check @derStep_mono

#check @DerClosed
#check @derClosed_empty
#check @derClosed_cup
#check @derClosed_insert
#check @Derives
#check @Derives.isFormCodeSem
#check @derives_of_step

/-! ### The object-language rendering of derivations -/

#check @fInstMapF
#check @fInstMapF_spec
#check @fDerCiteF
#check @fDerCiteF_spec
#check @fDAssF
#check @fDAssF_spec
#check @fDImpIF
#check @fDImpIF_spec
#check @fDImpEF
#check @fDImpEF_spec
#check @fDBotEF
#check @fDBotEF_spec
#check @fDLemF
#check @fDLemF_spec
#check @fDAndIF
#check @fDAndIF_spec
#check @fDAndE1F
#check @fDAndE1F_spec
#check @fDAndE2F
#check @fDAndE2F_spec
#check @fDOrI1F
#check @fDOrI1F_spec
#check @fDOrI2F
#check @fDOrI2F_spec
#check @fDOrEF
#check @fDOrEF_spec
#check @fDAllIF
#check @fDAllIF_spec
#check @fDAllEF
#check @fDAllEF_spec
#check @fDExIF
#check @fDExIF_spec
#check @fDExEF
#check @fDExEF_spec
#check @fDEqReflF
#check @fDEqReflF_spec
#check @fDEqElimF
#check @fDEqElimF_spec
#check @fDerStepF
#check @fDerStepF_spec
#check @fDerClosedF
#check @fDerClosedF_spec
#check @fDerivesF
#check @fDerivesF_spec

/-! ### Quotation soundness -/

#check @provCode_of_prov
#check @derives_of_prov

/-! ## Internal soundness -/

#check @CtxSat
#check @ctxSat_cons
#check @ctxSat_shift
#check @SoundAt
#check @fCtxSatF
#check @fCtxSatF_spec
#check @fSoundAtF
#check @fSoundAtF_spec
#check @soundAt_step
#check @envSound
#check @fSoundBelowF
#check @fSoundBelowF_spec
#check @soundBelow
#check @soundAt_all
#check @derives_sound
#check @not_derives_bot
#check @prov_satIn

/-! ## Assumption audit

The internal set operators of `ZF.Zf` are carved out with `Exists.choose`, and
everything downstream — `applyV`, `renameV`, the Replacement images of the
satisfaction and renaming layers — inherits that, so `Classical.choice` is
expected throughout.  Nothing beyond Lean's three standard axioms should
appear, and in particular no `sorry`, no `native_decide`, and no
theory-specific axiom.

The ones that matter are the unconditional `iff`s between a `Form` and the
property it renders — `fMemCtxF_spec`, `fIsCtxF_spec`, `fShiftsCtxF_spec`,
`fDerStepF_spec`, `fDerClosedF_spec`, `fDerivesF_spec`, `fSoundAtF_spec` — where
a hidden assumption would show up; the two inversion lemmas for coded
membership, which are what make the certificate presentation of `MemCtx`
faithful; `derives_of_prov`, which is the only bridge from the external
calculus; and `soundAt_step` with `derives_sound` and `not_derives_bot`, which
are the interface a reflection layer consumes. -/

#print axioms natV_lt

#print axioms memCtx_head
#print axioms memCtx_tail
#print axioms memCtx_nil
#print axioms memCtx_cons_inv
#print axioms memCtx_cons_iff
#print axioms isCtx_cons
#print axioms isCtx_cons_inv

#print axioms fMemCtxF_spec
#print axioms fIsCtxF_spec
#print axioms fCtxMemStepF_spec
#print axioms fCtxMemClosedF_spec

#print axioms memCtx_ctxCode
#print axioms isCtx_ctxCode

#print axioms fIdMapF_spec
#print axioms fSuccMapF_spec
#print axioms fShiftsCtxF_spec
#print axioms shiftsCtx_ctxCode

#print axioms derStep_mono
#print axioms derClosed_cup
#print axioms derClosed_insert
#print axioms derives_of_step

#print axioms fInstMapF_spec
#print axioms fDerCiteF_spec
#print axioms fDImpIF_spec
#print axioms fDLemF_spec
#print axioms fDOrEF_spec
#print axioms fDAllIF_spec
#print axioms fDAllEF_spec
#print axioms fDExIF_spec
#print axioms fDExEF_spec
#print axioms fDEqElimF_spec
#print axioms fDerStepF_spec
#print axioms fDerClosedF_spec
#print axioms fDerivesF_spec

#print axioms provCode_of_prov
#print axioms derives_of_prov

#print axioms ctxSat_cons
#print axioms ctxSat_shift
#print axioms fCtxSatF_spec
#print axioms fSoundAtF_spec
#print axioms fSoundBelowF_spec
#print axioms soundAt_step
#print axioms soundBelow
#print axioms soundAt_all
#print axioms derives_sound
#print axioms not_derives_bot
#print axioms prov_satIn

end LeanProofs.BoundedZFCConsistency.CodedDerivationAudit
