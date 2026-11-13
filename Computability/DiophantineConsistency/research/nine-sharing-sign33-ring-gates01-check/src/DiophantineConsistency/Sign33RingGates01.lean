import DiophantineConsistency.Sign33Lift38
import DiophantineConsistency.NormAssignment38

/-! Next three ring-value gate equations for the canonical lift. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33RingGates01
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing SharingGateModel
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem gate24 (ports : Fin 4 → V) (v : Fin 34 → V)
    (hc : Sign33ResidualAssembly.AllCuts ports v) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 24) = ringCompute GateOp.mul (pairValue ι (a 23)) (pairValue ι (a 22)) := by
  have h := hc.batch00.2.1
  simpa [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, Sign33ResidualBatch00.q] using h

theorem gate25 (ports : Fin 4 → V) (v : Fin 34 → V)
    (hc : Sign33ResidualAssembly.AllCuts ports v) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 25) = ringCompute GateOp.mul (pairValue ι (a 8)) (pairValue ι (a 22)) := by
  have h := hc.batch00.2.2
  simpa [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, Sign33ResidualBatch00.q] using h

theorem gate26 (ports : Fin 4 → V) (v : Fin 34 → V)
    (hc : Sign33ResidualAssembly.AllCuts ports v) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 26) = ringCompute GateOp.mul (pairValue ι (a 7)) (pairValue ι (a 24)) := by
  have h := hc.batch01.1
  simpa [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, Sign33ResidualBatch00.q] using h

end DiophantineConsistency.Sign33RingGates01
#print axioms DiophantineConsistency.Sign33RingGates01.gate24
#print axioms DiophantineConsistency.Sign33RingGates01.gate25
#print axioms DiophantineConsistency.Sign33RingGates01.gate26
