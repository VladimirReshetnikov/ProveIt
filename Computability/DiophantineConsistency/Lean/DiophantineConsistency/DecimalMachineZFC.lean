import DiophantineConsistency.DecimalMachine215
import DiophantineConsistency.Bridge
import BusyBeaver.ZFC.KEndpoint215

/-!
# The literal decimal machine and syntactic ZFC consistency

The actual 715-digit decoder is conjugate to the checked dense215 table.
Composing that theorem with the current KEndpoint215 closes the machine
endpoint for the repository's exact ZFC axiom predicate and ConZFC definition.
This module does not assert that a Diophantine equation encodes this machine;
the current arithmetic-to-tableau calibration remains a separate obligation.
-/

namespace DiophantineConsistency.DecimalMachineZFC

open SetTheory SetTheory.BusyBeaver.ZFC LeanProofs.BoundedZFCConsistency

/-- The literal decimal-decoded machine halts on blank tape exactly when the
repository's actual ZFC axiom set admits a finite refutation. -/
theorem blank_halts_iff_zfc_refutation :
    KDenseBridge.BlankHalts DecimalMachine215.machine ↔ BProv ZFCax_s [] Form.fBot :=
  DecimalMachine215.blank_halts_iff_dense.trans KEndpoint215.blank_halts_iff_zfc_refutation

/-- This uses the existing ConZFC definition, with no replacement consistency predicate. -/
theorem blank_nonhalting_iff_conZFC :
    (¬ KDenseBridge.BlankHalts DecimalMachine215.machine) ↔ ConZFC :=
  not_congr blank_halts_iff_zfc_refutation

end DiophantineConsistency.DecimalMachineZFC
