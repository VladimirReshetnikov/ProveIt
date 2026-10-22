import BusyBeaver.ZFC.KResidualSites215

namespace SetTheory.BusyBeaver.ZFC.KResidualAudit
open KZip KRuntimeCore KSim RegisterPath RMBisim KTableCore

set_option maxHeartbeats 0
set_option maxRecDepth 65536

def leaves : Tree → Nat
  | .none => 0
  | .leaf _ => 1
  | .node a b => leaves a + leaves b

def guards : Tree → Nat
  | .none => 0
  | .leaf (.decnz _) => 2
  | .leaf _ => 1
  | .node a b => guards a + guards b

/-- Counts are tied directly to the maintained literal tree. -/
theorem concrete_counts : leaves KSource215.t215 = 4751 ∧ guards KSource215.t215 = 6176 := by
  decide +kernel

/-- Exact original API retained by the inherited semantic-interface refactor. -/
theorem old_simulation_api {M : TMN} (B : BoxLemmas M) {p : Program}
    (hcov : Covered M p) (hNH : ∀ b, M 230 b = none)
    {c : Configuration} {T : Conf} (hc : Rel p c T) :
    RegisterPath.Halts p c ↔ KZip.Halts M T :=
  KSim.halts_iff B hcov hNH hc

/-- Same relation and both directions for the exact K215 source and table. -/
theorem residual_simulation_api (B : BoxLemmas tm215)
    (hNH : ∀ b, tm215 230 b = none) {c : Configuration} {T : Conf}
    (hc : Rel KSource215.p215 c T) :
    RegisterPath.Halts KSource215.p215 c ↔ KZip.Halts tm215 T :=
  KResidualSites215.halts_iff B hNH hc

theorem rejects_empty : KResidual215.residualTest tm215 [] .halt = false := rfl

#print axioms concrete_counts
#print axioms old_simulation_api
#print axioms residual_simulation_api
#print axioms rejects_empty
end SetTheory.BusyBeaver.ZFC.KResidualAudit
