import DiophantineConsistency.Sign33Lift38
import DiophantineConsistency.NormAssignment38

/-! Six ring-value gate equations for the canonical lift. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33RingGates10
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing SharingGateModel
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem gate72 (ports : Fin 4 → V) (v : Fin 34 → V)
    (hc : Sign33ResidualAssembly.AllCuts ports v) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 72) = ringCompute GateOp.mul (pairValue ι (a 5)) (pairValue ι (a 42)) := by
  have h := hc.batch06.2.1
  simpa [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat] using h

theorem gate73 (ports : Fin 4 → V) (v : Fin 34 → V)
    (hc : Sign33ResidualAssembly.AllCuts ports v) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 73) = ringCompute GateOp.mul (pairValue ι (a 72)) (pairValue ι (a 72)) := by
  have h := hc.batch06.2.2
  simpa [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat] using h

theorem gate74 (ports : Fin 4 → V) (v : Fin 34 → V) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 74) = ringCompute GateOp.mul (pairValue ι (a 71)) (pairValue ι (a 71)) := by
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat] <;> ring

theorem gate75 (ports : Fin 4 → V) (v : Fin 34 → V) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 75) = ringCompute GateOp.mul (pairValue ι (a 12)) (pairValue ι (a 12)) := by
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat] <;> ring

theorem gate76 (ports : Fin 4 → V) (v : Fin 34 → V)
    (hc : Sign33ResidualAssembly.AllCuts ports v) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 76) = ringCompute GateOp.sub (pairValue ι (a 74)) (pairValue ι (a 75)) := by
  have h := hc.batch07.1
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat]
  rw [h]
  ring

theorem gate77 (ports : Fin 4 → V) (v : Fin 34 → V) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 77) = ringCompute GateOp.mul (pairValue ι (a 73)) (pairValue ι (a 76)) := by
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat] <;> ring

end DiophantineConsistency.Sign33RingGates10
#print axioms DiophantineConsistency.Sign33RingGates10.gate72
#print axioms DiophantineConsistency.Sign33RingGates10.gate73
#print axioms DiophantineConsistency.Sign33RingGates10.gate74
#print axioms DiophantineConsistency.Sign33RingGates10.gate75
#print axioms DiophantineConsistency.Sign33RingGates10.gate76
#print axioms DiophantineConsistency.Sign33RingGates10.gate77
