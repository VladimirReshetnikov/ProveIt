import DiophantineConsistency.Sign33Lift38
import DiophantineConsistency.NormAssignment38

/-! First three ring-value gate equations for the canonical lift. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33RingGates00
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing SharingGateModel
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem gate21 (ports : Fin 4 → V) (v : Fin 34 → V) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 21) = ringCompute GateOp.mul (pairValue ι (a 14)) (pairValue ι (a 0)) := by
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul]

theorem gate22 (ports : Fin 4 → V) (v : Fin 34 → V) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 22) = ringCompute GateOp.add (pairValue ι (a 21)) (pairValue ι (a 18)) := by
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul]

theorem gate23 (ports : Fin 4 → V) (v : Fin 34 → V)
    (hc : Sign33ResidualAssembly.AllCuts ports v) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 23) = ringCompute GateOp.mul (pairValue ι (a 22)) (pairValue ι (a 22)) := by
  have h := hc.batch00.1
  simpa [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, Sign33ResidualBatch00.q] using h
end DiophantineConsistency.Sign33RingGates00
#print axioms DiophantineConsistency.Sign33RingGates00.gate21
#print axioms DiophantineConsistency.Sign33RingGates00.gate22
#print axioms DiophantineConsistency.Sign33RingGates00.gate23
