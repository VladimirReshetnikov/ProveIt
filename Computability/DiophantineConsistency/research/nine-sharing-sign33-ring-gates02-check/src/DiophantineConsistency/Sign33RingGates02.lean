import DiophantineConsistency.Sign33Lift38
import DiophantineConsistency.NormAssignment38

/-! Next three ring-value gate equations for the canonical lift. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33RingGates02
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing SharingGateModel
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem gate27 (ports : Fin 4 → V) (v : Fin 34 → V)
    (hc : Sign33ResidualAssembly.AllCuts ports v) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 27) = ringCompute GateOp.mul (pairValue ι (a 25)) (pairValue ι (a 26)) := by
  have h := hc.batch01.2.1
  simpa [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul] using h

theorem gate28 (ports : Fin 4 → V) (v : Fin 34 → V) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 28) = ringCompute GateOp.add (pairValue ι (a 10)) (pairValue ι (a 11)) := by
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul]

theorem gate29 (ports : Fin 4 → V) (v : Fin 34 → V)
    (hc : Sign33ResidualAssembly.AllCuts ports v) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 29) = ringCompute GateOp.mul (pairValue ι (a 28)) (pairValue ι (a 26)) := by
  have h := hc.batch01.2.2
  simpa [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul] using h

end DiophantineConsistency.Sign33RingGates02
#print axioms DiophantineConsistency.Sign33RingGates02.gate27
#print axioms DiophantineConsistency.Sign33RingGates02.gate28
#print axioms DiophantineConsistency.Sign33RingGates02.gate29
