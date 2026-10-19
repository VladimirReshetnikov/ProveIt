import BusyBeaver.ZFC.CalibratedRotation244
open SetTheory SetTheory.BusyBeaver.ZFC
open CalibratedRotation244

#print axioms SetTheory.BusyBeaver.ZFC.CalibratedRotation244.program_halts_iff_original
#print axioms SetTheory.BusyBeaver.ZFC.CalibratedRotation244.seed_halts_iff_original
#print axioms SetTheory.BusyBeaver.ZFC.CalibratedRotation244.halts_iff_native_refutation
#print axioms SetTheory.BusyBeaver.ZFC.CalibratedRotation244.halts_iff_zf_refutation
#print axioms SetTheory.BusyBeaver.ZFC.CalibratedRotation244.halts_iff_zfc_refutation
#print axioms SetTheory.BusyBeaver.ZFC.CalibratedRotation244.nonhalting_iff_zf_consistency
#print axioms SetTheory.BusyBeaver.ZFC.CalibratedRotation244.nonhalting_iff_zfc_consistency

example (R : RegisterPath.Registers) :
    RegisterPath.Halts ProgramRotation244.program ⟨[], R⟩ ↔
      RegisterPath.Halts Prog254.program ⟨[], R⟩ := program_halts_iff_original R
example :
    RegisterPath.Halts ProgramRotation244.program LogicalSeed246.initial ↔
      RegisterPath.Halts Prog254.program LogicalSeed246.initial := seed_halts_iff_original
example :
    RegisterPath.Halts ProgramRotation244.program LogicalSeed246.initial ↔
      BProv NativeTheory254.NativeAx [] Form.fBot := halts_iff_native_refutation
example :
    RegisterPath.Halts ProgramRotation244.program LogicalSeed246.initial ↔
      BProv ZFax_s [] Form.fBot := halts_iff_zf_refutation
example :
    RegisterPath.Halts ProgramRotation244.program LogicalSeed246.initial ↔
      BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot := halts_iff_zfc_refutation
example :
    (¬ RegisterPath.Halts ProgramRotation244.program LogicalSeed246.initial) ↔
      ¬ BProv ZFax_s [] Form.fBot := nonhalting_iff_zf_consistency
example :
    (¬ RegisterPath.Halts ProgramRotation244.program LogicalSeed246.initial) ↔
      ¬ BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot := nonhalting_iff_zfc_consistency
example (h : RegisterPath.Halts ProgramRotation244.program LogicalSeed246.initial) :
    BProv ZFax_s [] Form.fBot := halts_iff_zf_refutation.mp h
example (h : BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot) :
    RegisterPath.Halts ProgramRotation244.program LogicalSeed246.initial :=
  halts_iff_zfc_refutation.mpr h
