import DiophantineConsistency.Sign33LiftNorm0
import DiophantineConsistency.Sign33LiftNorm1
import DiophantineConsistency.Sign33LiftNorm2
import DiophantineConsistency.Sign33LiftNorm3
import DiophantineConsistency.Sign33LiftNorm4

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33LiftFiveNorms
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing SharingGateModel
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem five_norms (ports : Fin 4 → V) (v : Fin 34 → V)
    (hc : Sign33ResidualAssembly.AllCuts ports v) :
    NormAssignment38.fiveNorms ι ports (Sign33Lift38.lift v) := by
  exact ⟨Sign33LiftNorm0.norm ports v hc, Sign33LiftNorm1.norm ports v hc,
    Sign33LiftNorm2.norm ports v hc, Sign33LiftNorm3.norm ports v hc,
    Sign33LiftNorm4.norm ports v hc⟩
end DiophantineConsistency.Sign33LiftFiveNorms
#print axioms DiophantineConsistency.Sign33LiftFiveNorms.five_norms
