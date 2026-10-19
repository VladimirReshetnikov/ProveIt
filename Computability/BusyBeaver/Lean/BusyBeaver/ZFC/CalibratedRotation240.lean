import BusyBeaver.ZFC.SourceRotation240
import BusyBeaver.ZFC.CalibratedRotation244

/-!
External logical calibration of the exact rotation240 register program. Its
complete register-file source equivalence is composed with the checked
rotation244 calibration and the established logical seed. This does not identify any
binary-machine run or blank tape with that seed and is not an internal PA proof.
-/
set_option autoImplicit false
namespace SetTheory.BusyBeaver.ZFC.CalibratedRotation240

theorem program_halts_iff_original (R : RegisterPath.Registers) :
    RegisterPath.Halts SourceRotation240.program ⟨[], R⟩ ↔
      RegisterPath.Halts Prog254.program ⟨[], R⟩ :=
  (SourceRotation240.program_halts_iff R).trans
    (CalibratedRotation244.program_halts_iff_original R)

theorem seed_halts_iff_original :
    RegisterPath.Halts SourceRotation240.program LogicalSeed246.initial ↔
      RegisterPath.Halts Prog254.program LogicalSeed246.initial :=
  program_halts_iff_original LogicalSeed246.registers

theorem halts_iff_native_refutation :
    RegisterPath.Halts SourceRotation240.program LogicalSeed246.initial ↔
      BProv NativeTheory254.NativeAx [] Form.fBot :=
  seed_halts_iff_original.trans LogicalSeed246.halts_iff_native_refutation

theorem halts_iff_zf_refutation :
    RegisterPath.Halts SourceRotation240.program LogicalSeed246.initial ↔
      BProv ZFax_s [] Form.fBot :=
  seed_halts_iff_original.trans LogicalSeed246.halts_iff_zf_refutation

theorem halts_iff_zfc_refutation :
    RegisterPath.Halts SourceRotation240.program LogicalSeed246.initial ↔
      BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot :=
  seed_halts_iff_original.trans LogicalSeed246.halts_iff_zfc_refutation

theorem nonhalting_iff_zf_consistency :
    (¬ RegisterPath.Halts SourceRotation240.program LogicalSeed246.initial) ↔
      ¬ BProv ZFax_s [] Form.fBot :=
  not_congr halts_iff_zf_refutation

theorem nonhalting_iff_zfc_consistency :
    (¬ RegisterPath.Halts SourceRotation240.program LogicalSeed246.initial) ↔
      ¬ BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot :=
  not_congr halts_iff_zfc_refutation

end SetTheory.BusyBeaver.ZFC.CalibratedRotation240
