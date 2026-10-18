import BusyBeaver.ZFC.LogicalSeed246

open SetTheory SetTheory.BusyBeaver.ZFC
open LogicalSeed246

#print axioms SetTheory.BusyBeaver.ZFC.LogicalSeed246.primary_values
#print axioms SetTheory.BusyBeaver.ZFC.LogicalSeed246.tail_zero
#print axioms SetTheory.BusyBeaver.ZFC.LogicalSeed246.root_clean
#print axioms SetTheory.BusyBeaver.ZFC.LogicalSeed246.halts_iff_native_refutation
#print axioms SetTheory.BusyBeaver.ZFC.LogicalSeed246.halts_iff_zf_refutation
#print axioms SetTheory.BusyBeaver.ZFC.LogicalSeed246.halts_iff_zfc_refutation
#print axioms SetTheory.BusyBeaver.ZFC.LogicalSeed246.nonhalting_iff_zfc_consistency

example :
    (List.range 9).map registers = [3, 0, 0, 0, 3, 0, 0, 0, 0] := primary_values

example (i : Nat) : registers (i + 9) = 0 := tail_zero i

example : RegisterPathClean.Clean Prog254.program initial.path := root_clean

example :
    RegisterPath.Halts Prog254.program initial ↔
      BProv NativeTheory254.NativeAx [] Form.fBot := halts_iff_native_refutation

example :
    RegisterPath.Halts Prog254.program initial ↔ BProv ZFax_s [] Form.fBot := halts_iff_zf_refutation

example :
    RegisterPath.Halts Prog254.program initial ↔
      BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot := halts_iff_zfc_refutation

example :
    (¬ RegisterPath.Halts Prog254.program initial) ↔
      ¬ BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot := nonhalting_iff_zfc_consistency

