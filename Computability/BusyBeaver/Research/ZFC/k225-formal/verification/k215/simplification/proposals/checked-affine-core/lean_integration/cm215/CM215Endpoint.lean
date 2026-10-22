import BusyBeaver.ZFC.KEndpoint215
import CM215Dense

/-!
Integration wrapper for the existing ProveIt K215 endpoint.

The standalone packet freshly checks `CM215Dense` and its exact Core-machine
transport.  This wrapper imports the full existing K215 endpoint; it is
provided for checking in the repository and is not included in the packet's
claim of a fresh standalone compilation.  No assumption is introduced here.
-/

namespace SetTheory.BusyBeaver.ZFC.CM215Endpoint

open LeanProofs.BoundedZFCConsistency

theorem blank_halts_iff_zfc_refutation :
    KDenseBridge.BlankHalts CM215.CoreBridge.machineCM215 ↔
      BProv ZFCax_s [] Form.fBot :=
  CM215.CoreBridge.calibration_transfer KEndpoint215.blank_halts_iff_zfc_refutation

theorem nonhalting_iff_zfc_consistency :
    (¬ KDenseBridge.BlankHalts CM215.CoreBridge.machineCM215) ↔
      ¬ BProv ZFCax_s [] Form.fBot :=
  not_congr blank_halts_iff_zfc_refutation

#print axioms blank_halts_iff_zfc_refutation
#print axioms nonhalting_iff_zfc_consistency

end SetTheory.BusyBeaver.ZFC.CM215Endpoint
