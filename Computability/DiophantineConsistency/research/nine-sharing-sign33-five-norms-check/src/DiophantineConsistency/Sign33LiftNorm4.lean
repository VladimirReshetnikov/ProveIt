import DiophantineConsistency.Sign33Lift38
import DiophantineConsistency.NormAssignment38

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33LiftNorm4
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing SharingGateModel
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem norm (ports : Fin 4 → V) (v : Fin 34 → V)
    (hc : Sign33ResidualAssembly.AllCuts ports v) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 80) = pairValue ι (a 36) := by
  have h := hc.batch07.2.2
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute,
    map_add, map_mul, map_ofNat]
  convert h using 1 <;> ring
end DiophantineConsistency.Sign33LiftNorm4
#print axioms DiophantineConsistency.Sign33LiftNorm4.norm
