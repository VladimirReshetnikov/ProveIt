import BusyBeaver.ZFC.SourceRotation244
import BusyBeaver.ZFC.BisimRouting245
import BusyBeaver.ZFC.LogicalSeed246

/-!
External logical calibration of the rotated register program. The complete
register-file source equivalence is composed with the checked routed-program
bisimulation and the established logical seed. This does not identify any
binary-machine run or blank tape with that seed and is not an internal PA proof.
-/
set_option autoImplicit false
namespace SetTheory.BusyBeaver.ZFC.CalibratedRotation244

theorem program_halts_iff_original (R : RegisterPath.Registers) :
    RegisterPath.Halts ProgramRotation244.program ⟨[], R⟩ ↔
      RegisterPath.Halts Prog254.program ⟨[], R⟩ :=
  (SourceRotation244.program_halts_iff R).trans
    (BisimRouting245.program_halts_iff R)

theorem seed_halts_iff_original :
    RegisterPath.Halts ProgramRotation244.program LogicalSeed246.initial ↔
      RegisterPath.Halts Prog254.program LogicalSeed246.initial :=
  program_halts_iff_original LogicalSeed246.registers

theorem halts_iff_native_refutation :
    RegisterPath.Halts ProgramRotation244.program LogicalSeed246.initial ↔
      BProv NativeTheory254.NativeAx [] Form.fBot :=
  seed_halts_iff_original.trans LogicalSeed246.halts_iff_native_refutation

theorem halts_iff_zf_refutation :
    RegisterPath.Halts ProgramRotation244.program LogicalSeed246.initial ↔
      BProv ZFax_s [] Form.fBot :=
  seed_halts_iff_original.trans LogicalSeed246.halts_iff_zf_refutation

theorem halts_iff_zfc_refutation :
    RegisterPath.Halts ProgramRotation244.program LogicalSeed246.initial ↔
      BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot :=
  seed_halts_iff_original.trans LogicalSeed246.halts_iff_zfc_refutation

theorem nonhalting_iff_zf_consistency :
    (¬ RegisterPath.Halts ProgramRotation244.program LogicalSeed246.initial) ↔
      ¬ BProv ZFax_s [] Form.fBot :=
  not_congr halts_iff_zf_refutation

theorem nonhalting_iff_zfc_consistency :
    (¬ RegisterPath.Halts ProgramRotation244.program LogicalSeed246.initial) ↔
      ¬ BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot :=
  not_congr halts_iff_zfc_refutation

end SetTheory.BusyBeaver.ZFC.CalibratedRotation244
