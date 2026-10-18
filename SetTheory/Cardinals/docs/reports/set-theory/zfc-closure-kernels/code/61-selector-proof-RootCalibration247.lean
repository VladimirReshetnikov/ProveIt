import BusyBeaver.ZFC.Bisim254
import BusyBeaver.ZFC.DirtyProgram254
import BusyBeaver.ZFC.WFTheory
import BusyBeaver.ZFC.ConstructibleChoice

/-!
Source-level specialization of the maintained logical calibration to the
247-state candidate's independently certified startup register vector.

Reference revision: ProveIt e0b512a63e2c1ca6a1698fa437b8568f1643ff6b.
This standalone source was checked against the imported theorem statements,
but has NOT been run through a Lean kernel in this delivery environment.
It intentionally makes no binary-runtime or blank-initialization claim.
-/

namespace SetTheory.BusyBeaver.ZFC.Prefix247Root

def registers : RegisterPath.Registers := L2.enc ⟨3, 0, 0, 0, 3, 0, 0, 0, 0⟩

theorem literal_halts_iff_native_refutation :
    RegisterPath.Halts Prog254.program ⟨[], registers⟩ ↔
      BProv NativeTheory254.NativeAx [] Form.fBot :=
  (Bisim254.prog254_halts_iff registers).trans
    (DirtyProgram254.six_nonformula_path_iff 3 0 3 0 0 0)

theorem literal_halts_iff_zfc_refutation :
    RegisterPath.Halts Prog254.program ⟨[], registers⟩ ↔
      BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot :=
  literal_halts_iff_native_refutation.trans
    (WFTheory.native_refutation_iff_zf.trans
      ConstructibleChoice.zf_refutation_iff_zfc_refutation)

end SetTheory.BusyBeaver.ZFC.Prefix247Root
