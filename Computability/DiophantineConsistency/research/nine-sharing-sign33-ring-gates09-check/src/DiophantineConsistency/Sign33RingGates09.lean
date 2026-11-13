import DiophantineConsistency.Sign33Lift38
import DiophantineConsistency.NormAssignment38

/-! Six ring-value gate equations for the canonical lift. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33RingGates09
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing SharingGateModel
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem gate66 (ports : Fin 4 → V) (v : Fin 34 → V) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 66) = ringCompute GateOp.sub (pairValue ι (a 64)) (pairValue ι (a 65)) := by
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat] <;> ring

theorem gate67 (ports : Fin 4 → V) (v : Fin 34 → V)
    (hc : Sign33ResidualAssembly.AllCuts ports v) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 67) = ringCompute GateOp.mul (pairValue ι (a 4)) (pairValue ι (a 4)) := by
  have h := hc.batch05.2.1
  simpa [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat] using h

theorem gate68 (ports : Fin 4 → V) (v : Fin 34 → V) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 68) = ringCompute GateOp.mul (pairValue ι (a 31)) (pairValue ι (a 6)) := by
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat] <;> ring

theorem gate69 (ports : Fin 4 → V) (v : Fin 34 → V)
    (hc : Sign33ResidualAssembly.AllCuts ports v) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 69) = ringCompute GateOp.sub (pairValue ι (a 68)) (pairValue ι (a 54)) := by
  have h := hc.batch05.2.2
  simp only [Sign33ResidualBatch05.q, Sign33ResidualBatch05.t] at h
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat]
  rw [h]
  ring

theorem gate70 (ports : Fin 4 → V) (v : Fin 34 → V) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 70) = ringCompute GateOp.mul (pairValue ι (a 67)) (pairValue ι (a 69)) := by
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat] <;> ring

theorem gate71 (ports : Fin 4 → V) (v : Fin 34 → V)
    (hc : Sign33ResidualAssembly.AllCuts ports v) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 71) = ringCompute GateOp.sub (pairValue ι (a 70)) (pairValue ι (a 31)) := by
  have h := hc.batch06.1
  simpa [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat] using h

end DiophantineConsistency.Sign33RingGates09
#print axioms DiophantineConsistency.Sign33RingGates09.gate66
#print axioms DiophantineConsistency.Sign33RingGates09.gate67
#print axioms DiophantineConsistency.Sign33RingGates09.gate68
#print axioms DiophantineConsistency.Sign33RingGates09.gate69
#print axioms DiophantineConsistency.Sign33RingGates09.gate70
#print axioms DiophantineConsistency.Sign33RingGates09.gate71
