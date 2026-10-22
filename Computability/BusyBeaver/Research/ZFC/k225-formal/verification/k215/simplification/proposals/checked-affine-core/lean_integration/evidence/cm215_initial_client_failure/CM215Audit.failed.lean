import CM215Endpoint

namespace CM215.IntegrationAudit

open SetTheory.BusyBeaver
open SetTheory.BusyBeaver.ZFC
open LeanProofs.BoundedZFCConsistency

/-- The public endpoint is about the exact finite-run predicate. -/
theorem exact_finite_run_endpoint :
    (∃ t : Nat, (CM215.CoreBridge.machineCM215.run t).state = none) ↔
      BProv ZFCax_s [] Form.fBot :=
  CM215Endpoint.blank_halts_iff_zfc_refutation

/-- The companion statement has no consistency assumption. -/
theorem exact_nonhalting_endpoint :
    (¬ ∃ t : Nat, (CM215.CoreBridge.machineCM215.run t).state = none) ↔
      ¬ BProv ZFCax_s [] Form.fBot :=
  CM215Endpoint.nonhalting_iff_zfc_consistency

/-- The transition table contains both binary rows for 215 working controls. -/
theorem literal_rows : CM215.newRows.length = 215 * 2 := rfl

/-- The machine's dependent type fixes its working-state count. -/
def exact_machine : Machine 215 := CM215.CoreBridge.machineCM215

#print axioms exact_finite_run_endpoint
#print axioms exact_nonhalting_endpoint
#print axioms literal_rows

end CM215.IntegrationAudit
