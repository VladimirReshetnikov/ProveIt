import BusyBeaver.ZFC.BinaryPerm252
import BusyBeaver.ZFC.ConstructibleChoice

/-!
The literal 252-state blank machine against standard ZFC.

The Codex lane's closed endpoint `BinaryPerm252.blank_halts_iff_zf_refutation`
identifies blank halting of `machinePerm252` with a ZF refutation. The Choice
transport (`ConstructibleChoice`: the constructible class of a model of ZF is
a model of ZFC) identifies ZF refutations with ZFC refutations. Together:
**the blank machine never halts iff ZFC is consistent**.

Attribution as in `BinaryPerm252`: Mira-Cult's original machine, Jeff's
verification and Wade's compiler framework at upstream
`297ab8df7e5de329605c3875b4934643b371a5e3`; mira-emmy's public253 reduction.
-/

namespace SetTheory.BusyBeaver.ZFC.BinaryZFC252

open BinaryPerm252

/-- **The 252-state blank machine halts iff ZFC is refutable.** -/
theorem blank_halts_iff_zfc_refutation :
    BlankHalts machinePerm252 ↔ BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot :=
  blank_halts_iff_zf_refutation.trans ConstructibleChoice.zf_refutation_iff_zfc_refutation

/-- **The 252-state blank machine never halts iff ZFC is consistent.** -/
theorem nonhalting_iff_zfc_consistency :
    (¬ BlankHalts machinePerm252) ↔ ¬ BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot :=
  not_congr blank_halts_iff_zfc_refutation

end SetTheory.BusyBeaver.ZFC.BinaryZFC252

