import BusyBeaver.ZFC.BinaryCompensated244

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open SetTheory.BusyBeaver.ZFC.BinaryRouting245

#print axioms SetTheory.BusyBeaver.ZFC.BinaryCompensated244.blank_initial_config
#print axioms SetTheory.BusyBeaver.ZFC.BinaryCompensated244.blank_halts_iff_routing245
#print axioms SetTheory.BusyBeaver.ZFC.BinaryCompensated244.blank_halts_iff_zf_refutation
#print axioms SetTheory.BusyBeaver.ZFC.BinaryCompensated244.blank_halts_iff_zfc_refutation
#print axioms SetTheory.BusyBeaver.ZFC.BinaryCompensated244.nonhalting_iff_zf_consistency
#print axioms SetTheory.BusyBeaver.ZFC.BinaryCompensated244.nonhalting_iff_zfc_consistency

example : initial 244 = ({ state := some ⟨0, by decide⟩, head := 0, tape := [] } : Config 244) :=
  BinaryCompensated244.blank_initial_config
example : BlankHalts machineCompensated244 ↔ BlankHalts machineRouting245 :=
  BinaryCompensated244.blank_halts_iff_routing245
example : BlankHalts machineCompensated244 ↔ BProv ZFax_s [] Form.fBot :=
  BinaryCompensated244.blank_halts_iff_zf_refutation
example : BlankHalts machineCompensated244 ↔
    BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot :=
  BinaryCompensated244.blank_halts_iff_zfc_refutation
example : (¬ BlankHalts machineCompensated244) ↔ ¬ BProv ZFax_s [] Form.fBot :=
  BinaryCompensated244.nonhalting_iff_zf_consistency
example : (¬ BlankHalts machineCompensated244) ↔
    ¬ BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot :=
  BinaryCompensated244.nonhalting_iff_zfc_consistency
