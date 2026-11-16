import DARC.DemandBlueprint
import DARC.TraceBlueprint
import DARC.RelationalBlueprint

/-! Blueprint for the global query-specialized DARC compiler. -/
namespace LeanProofs.IPRA.DARC

open LeanProofs.ConciseIPRA
open scoped Fm

/-- Metalevel plan: every node has a finite resource summary and a local
ordinary-iPRA contract.  The plan itself is not quantified over inside iPRA. -/
structure Plan where
  scope : ℕ
  resources : ResourceShape
  nodeCount : ℕ
  goal : Fm PTm scope
  residuals : Demand resources → List (Fm PTm scope)
  active : Demand resources → Fin nodeCount → Bool
  localGoal : Fin nodeCount → Fm PTm scope
  deps : Fin nodeCount → List (Fin nodeCount)
  transfer : Demand resources → Demand resources
  transfer_mono : Monotone[Demand.LE, Demand.LE] transfer
  localProof : ∀ d v, active d v = true →
    ((deps v).map localGoal ++ residuals d) ⊢[PRAAx] localGoal v
  outputNode : Fin nodeCount
  output_eq : localGoal outputNode = goal

/-- The query seed is compiled to the least demand state. -/
def Plan.closedDemand (P : Plan) (seed : Demand P.resources) : Demand P.resources :=
  Demand.close P.transfer seed

/-- Soundness of the generated simultaneous-cut schedule. -/
theorem compile (P : Plan) (seed : Demand P.resources)
    (schedule : SoundSchedule P (P.closedDemand seed)) :
    P.residuals (P.closedDemand seed) ⊢[PRAAx] P.goal := by
  sorry

/-- Relative minimality: any resource state sound for the declared transfer
summaries and above the public seed contains the compiled demand. -/
theorem demand_minimal (P : Plan) (seed candidate : Demand P.resources)
    (hseed : Demand.LE seed candidate)
    (hpre : Demand.LE (P.transfer candidate) candidate) :
    Demand.LE (P.closedDemand seed) candidate := by
  exact Demand.close_least P.transfer P.transfer_mono seed candidate hseed hpre

end LeanProofs.IPRA.DARC
