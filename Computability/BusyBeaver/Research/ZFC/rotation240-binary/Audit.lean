import BusyBeaver.ZFC.BinaryRotation240

open SetTheory SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RuntimePerm252 RuntimeInstanceRotation240

#print axioms SetTheory.BusyBeaver.ZFC.BinaryRotation240.blank_initial_config
#print axioms SetTheory.BusyBeaver.ZFC.BinaryRotation240.actual_coverage
#print axioms SetTheory.BusyBeaver.ZFC.BinaryRotation240.boot_related
#print axioms SetTheory.BusyBeaver.ZFC.BinaryRotation240.blank_after_prefix_iff
#print axioms SetTheory.BusyBeaver.ZFC.BinaryRotation240.blank_halts_iff_rotation_register
#print axioms SetTheory.BusyBeaver.ZFC.BinaryRotation240.blank_halts_iff_zf_refutation
#print axioms SetTheory.BusyBeaver.ZFC.BinaryRotation240.blank_halts_iff_zfc_refutation
#print axioms SetTheory.BusyBeaver.ZFC.BinaryRotation240.nonhalting_iff_zf_consistency
#print axioms SetTheory.BusyBeaver.ZFC.BinaryRotation240.nonhalting_iff_zfc_consistency

example : initial 240 =
    ({ state := some ⟨0, by decide⟩, head := 0, tape := [] } : Config 240) :=
  BinaryRotation240.blank_initial_config
example : Covered SourceRotation240.program := BinaryRotation240.actual_coverage
example : Related SourceRotation240.program LogicalSeed246.initial
    (machineRotation240.run 409691) := BinaryRotation240.boot_related
example {states : Nat} (M : Machine states) (n : Nat) :
    BinaryHalts M (M.run n) ↔ ∃ t, (M.run t).state = none :=
  BinaryRotation240.blank_after_prefix_iff M n
example : (∃ t, (machineRotation240.run t).state = none) ↔
    RegisterPath.Halts SourceRotation240.program LogicalSeed246.initial :=
  BinaryRotation240.blank_halts_iff_rotation_register
example : (∃ t, (machineRotation240.run t).state = none) ↔ BProv ZFax_s [] Form.fBot :=
  BinaryRotation240.blank_halts_iff_zf_refutation
example : (∃ t, (machineRotation240.run t).state = none) ↔
    BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot :=
  BinaryRotation240.blank_halts_iff_zfc_refutation
example : (¬ ∃ t, (machineRotation240.run t).state = none) ↔ ¬ BProv ZFax_s [] Form.fBot :=
  BinaryRotation240.nonhalting_iff_zf_consistency
example : (¬ ∃ t, (machineRotation240.run t).state = none) ↔
    ¬ BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot :=
  BinaryRotation240.nonhalting_iff_zfc_consistency
