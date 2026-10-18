import BusyBeaver.ZFC.BinaryPrefix246

open SetTheory SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RuntimePerm252 RuntimeInstancePrefix246 BinaryPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.BinaryPrefix246.blank_initial_config
#print axioms SetTheory.BusyBeaver.ZFC.BinaryPrefix246.actual_coverage
#print axioms SetTheory.BusyBeaver.ZFC.BinaryPrefix246.boot_related
#print axioms SetTheory.BusyBeaver.ZFC.BinaryPrefix246.blank_after_prefix_iff
#print axioms SetTheory.BusyBeaver.ZFC.BinaryPrefix246.blank_halts_iff_register
#print axioms SetTheory.BusyBeaver.ZFC.BinaryPrefix246.blank_halts_iff_zf_refutation
#print axioms SetTheory.BusyBeaver.ZFC.BinaryPrefix246.blank_halts_iff_zfc_refutation
#print axioms SetTheory.BusyBeaver.ZFC.BinaryPrefix246.nonhalting_iff_zf_consistency
#print axioms SetTheory.BusyBeaver.ZFC.BinaryPrefix246.nonhalting_iff_zfc_consistency

example : initial 246 = ({ state := some ⟨0, by decide⟩, head := 0, tape := [] } : Config 246) :=
  blank_initial_config
example : Covered Prog254.program := actual_coverage
example : Related Prog254.program LogicalSeed246.initial (machinePrefix246.run 410735) := boot_related
example {n : Nat} (M : Machine n) (k : Nat) : BinaryHalts M (M.run k) ↔ BlankHalts M :=
  blank_after_prefix_iff M k
example : BlankHalts machinePrefix246 ↔ RegisterPath.Halts Prog254.program LogicalSeed246.initial :=
  blank_halts_iff_register
example : BlankHalts machinePrefix246 ↔ BProv ZFax_s [] Form.fBot := blank_halts_iff_zf_refutation
example : BlankHalts machinePrefix246 ↔ BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot :=
  blank_halts_iff_zfc_refutation
example : (¬ BlankHalts machinePrefix246) ↔ ¬ BProv ZFax_s [] Form.fBot := nonhalting_iff_zf_consistency
example : (¬ BlankHalts machinePrefix246) ↔ ¬ BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot :=
  nonhalting_iff_zfc_consistency
