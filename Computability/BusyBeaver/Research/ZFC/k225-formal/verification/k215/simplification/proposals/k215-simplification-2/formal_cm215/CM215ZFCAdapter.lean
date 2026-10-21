import CM215Core
import BusyBeaver.ZFC.KEndpoint215

/-!
Repository integration adapter. The independent packet freshly compiles the
exact-machine transfer CM215Core.blank_halts_iff_primary. This final adapter
requires the already verified full repository ZFC development and is kept
separate from the small build. Rebuild this file in the repository to obtain
the alternative's end-to-end theorem in the same trusted environment.
-/
namespace SetTheory.BusyBeaver.ZFC.CM215Endpoint
open KDenseBridge LeanProofs.BoundedZFCConsistency

theorem blank_halts_iff_zfc_refutation :
    BlankHalts CM215Core.machineCM215 ↔ BProv ZFCax_s [] Form.fBot :=
  CM215Core.blank_halts_iff_primary.trans KEndpoint215.blank_halts_iff_zfc_refutation

theorem nonhalting_iff_zfc_consistency :
    (¬ BlankHalts CM215Core.machineCM215) ↔ ¬ BProv ZFCax_s [] Form.fBot :=
  not_congr blank_halts_iff_zfc_refutation

#print axioms blank_halts_iff_zfc_refutation
end SetTheory.BusyBeaver.ZFC.CM215Endpoint
