import BusyBeaver.ZFC.BinaryRouting245

open SetTheory SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RuntimePerm252 RuntimeInstanceRouting245 BinaryRouting245

#print axioms SetTheory.BusyBeaver.ZFC.BinaryRouting245.blank_initial_config
#print axioms SetTheory.BusyBeaver.ZFC.BinaryRouting245.actual_coverage
#print axioms SetTheory.BusyBeaver.ZFC.BinaryRouting245.boot_related
#print axioms SetTheory.BusyBeaver.ZFC.BinaryRouting245.blank_after_prefix_iff
#print axioms SetTheory.BusyBeaver.ZFC.BinaryRouting245.routed_seed_halts_iff_original
#print axioms SetTheory.BusyBeaver.ZFC.BinaryRouting245.blank_halts_iff_routed_register
#print axioms SetTheory.BusyBeaver.ZFC.BinaryRouting245.blank_halts_iff_register
#print axioms SetTheory.BusyBeaver.ZFC.BinaryRouting245.blank_halts_iff_zf_refutation
#print axioms SetTheory.BusyBeaver.ZFC.BinaryRouting245.blank_halts_iff_zfc_refutation
#print axioms SetTheory.BusyBeaver.ZFC.BinaryRouting245.nonhalting_iff_zf_consistency
#print axioms SetTheory.BusyBeaver.ZFC.BinaryRouting245.nonhalting_iff_zfc_consistency

example : initial 245 =
    ({ state := some ⟨0, by decide⟩, head := 0, tape := [] } : Config 245) := blank_initial_config
example : Covered ProgramRouting245.program := actual_coverage
example : Related ProgramRouting245.program LogicalSeed246.initial (machineRouting245.run 407915) :=
  boot_related
example {states : Nat} (M : Machine states) (n : Nat) :
    BinaryHalts M (M.run n) ↔ BlankHalts M := blank_after_prefix_iff M n
example : RegisterPath.Halts ProgramRouting245.program LogicalSeed246.initial ↔
    RegisterPath.Halts Prog254.program LogicalSeed246.initial := routed_seed_halts_iff_original
example : BlankHalts machineRouting245 ↔
    RegisterPath.Halts ProgramRouting245.program LogicalSeed246.initial := blank_halts_iff_routed_register
example : BlankHalts machineRouting245 ↔
    RegisterPath.Halts Prog254.program LogicalSeed246.initial := blank_halts_iff_register
example : BlankHalts machineRouting245 ↔ BProv ZFax_s [] Form.fBot := blank_halts_iff_zf_refutation
example : BlankHalts machineRouting245 ↔
    BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot := blank_halts_iff_zfc_refutation
example : (¬ BlankHalts machineRouting245) ↔ ¬ BProv ZFax_s [] Form.fBot := nonhalting_iff_zf_consistency
example : (¬ BlankHalts machineRouting245) ↔
    ¬ BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot := nonhalting_iff_zfc_consistency
