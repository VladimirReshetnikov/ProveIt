import BusyBeaver.ZFC.DirtyProgram254
import BusyBeaver.ZFC.Bisim254
import BusyBeaver.ZFC.WFTheory
import BusyBeaver.ZFC.ConstructibleChoice
import BusyBeaver.ZFC.RegisterPathClean

/-!
Logical calibration of the seed reported by the 246-state construction.
The actual decoder program is unchanged. This module identifies its halting
from the reported logical seed with ZFC refutation, using the existing
dirty-root, program-bisimulation, well-founded-part and Choice proofs.
It does not identify this seed with any binary execution or internalize the
comparison in PA. Attribution: source63 of intake162, Mira-Cult/Jeff/Wade's
original program and the maintained ProveIt calibration proofs.
-/
namespace SetTheory.BusyBeaver.ZFC.LogicalSeed246

def seed : L2.AS := ⟨3, 0, 0, 0, 3, 0, 0, 0, 0⟩
def registers : RegisterPath.Registers := L2.enc seed
def initial : RegisterPath.Configuration := ⟨[], registers⟩

theorem primary_values :
    (List.range 9).map registers = [3, 0, 0, 0, 3, 0, 0, 0, 0] := by
  decide +kernel

theorem tail_zero (i : Nat) : registers (i + 9) = 0 :=
  DirtyProgram254.enc_tail seed i

theorem root_clean : RegisterPathClean.Clean Prog254.program initial.path :=
  RegisterPathClean.clean_nil Prog254.program

theorem halts_iff_native_refutation :
    RegisterPath.Halts Prog254.program initial ↔
      BProv NativeTheory254.NativeAx [] Form.fBot :=
  (Bisim254.prog254_halts_iff registers).trans
    (DirtyProgram254.six_nonformula_path_iff 3 0 3 0 0 0)

theorem halts_iff_zf_refutation :
    RegisterPath.Halts Prog254.program initial ↔ BProv ZFax_s [] Form.fBot :=
  halts_iff_native_refutation.trans WFTheory.native_refutation_iff_zf

theorem halts_iff_zfc_refutation :
    RegisterPath.Halts Prog254.program initial ↔
      BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot :=
  halts_iff_zf_refutation.trans ConstructibleChoice.zf_refutation_iff_zfc_refutation

theorem nonhalting_iff_zfc_consistency :
    (¬ RegisterPath.Halts Prog254.program initial) ↔
      ¬ BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot :=
  not_congr halts_iff_zfc_refutation

end SetTheory.BusyBeaver.ZFC.LogicalSeed246
