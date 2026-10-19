import BusyBeaver.ZFC.DirtyProgram254
import BusyBeaver.ZFC.WFTheory
import BusyBeaver.ZFC.ChoiceCalibration254

/-!
Specialization of existing source-level theorems to the dirty seed produced
by the experimental shared-gm deletion initializer. This file deliberately
does not name a binary machine or assert that the deletion simulates the
source. The shared-gm deletion currently has an unresolved semantic issue.

The imported declarations were inspected at ProveIt commit
6d69a46dce1de15397a9d2448dcc946d08c90327. This specialization has not been
compiled in the current research checkout, which lacks the Lean dependency
closure. It is supplied as a small, reviewable integration artifact.
-/

namespace SetTheory.BusyBeaver.ZFC.DirtySeed35

theorem path_halts_iff_zfc_refutation :
    RegisterPath.Halts RMEquiv254.pathDag254
      ⟨[], L2.enc ⟨3, 0, 0, 0, 3, 0, 35, 0, 0⟩⟩ ↔
      BProv ZFCax_s [] Form.fBot :=
  (DirtyProgram254.six_nonformula_path_iff 3 0 3 35 0 0).trans
    (WFTheory.native_refutation_iff_zf.trans
      ChoiceCalibration254.zf_refutation_iff_zfc)

theorem nonhalting_iff_zfc_consistency :
    (¬ RegisterPath.Halts RMEquiv254.pathDag254
      ⟨[], L2.enc ⟨3, 0, 0, 0, 3, 0, 35, 0, 0⟩⟩) ↔
      ¬ BProv ZFCax_s [] Form.fBot :=
  not_congr path_halts_iff_zfc_refutation

end SetTheory.BusyBeaver.ZFC.DirtySeed35
