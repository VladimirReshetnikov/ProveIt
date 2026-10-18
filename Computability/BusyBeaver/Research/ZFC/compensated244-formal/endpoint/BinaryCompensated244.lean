import BusyBeaver.ZFC.Compensated244Simulation
import BusyBeaver.ZFC.BinaryRouting245

/-!
External consistency calibration for the exact compensated244 machine.
The local binary simulation transfers the closed Routing245 endpoint without
changing the encoded proof search, source theory, or blank-start convention.
This is not an internal PA derivation or an unconditional nonhalting theorem.
The submitted compensated fold and the original Mira-Cult/Jeff Ketchersid/
Andrew James Wade construction retain their attribution.
-/
namespace SetTheory.BusyBeaver.ZFC.BinaryCompensated244

open BinaryRouting245

theorem blank_initial_config :
    initial 244 = ({ state := some ⟨0, by decide⟩, head := 0, tape := [] } : Config 244) := rfl

theorem blank_halts_iff_routing245 :
    BlankHalts machineCompensated244 ↔ BlankHalts machineRouting245 :=
  Compensated244Simulation.blank_halts_iff.symm

theorem blank_halts_iff_zf_refutation :
    BlankHalts machineCompensated244 ↔ BProv ZFax_s [] Form.fBot :=
  blank_halts_iff_routing245.trans BinaryRouting245.blank_halts_iff_zf_refutation

theorem blank_halts_iff_zfc_refutation :
    BlankHalts machineCompensated244 ↔
      BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot :=
  blank_halts_iff_routing245.trans BinaryRouting245.blank_halts_iff_zfc_refutation

theorem nonhalting_iff_zf_consistency :
    (¬ BlankHalts machineCompensated244) ↔ ¬ BProv ZFax_s [] Form.fBot :=
  not_congr blank_halts_iff_zf_refutation

theorem nonhalting_iff_zfc_consistency :
    (¬ BlankHalts machineCompensated244) ↔
      ¬ BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot :=
  not_congr blank_halts_iff_zfc_refutation

end SetTheory.BusyBeaver.ZFC.BinaryCompensated244
