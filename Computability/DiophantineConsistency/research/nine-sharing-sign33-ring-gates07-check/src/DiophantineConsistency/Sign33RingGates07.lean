import DiophantineConsistency.Sign33Lift38
import DiophantineConsistency.NormAssignment38

/-! Six ring-value gate equations for the canonical lift. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33RingGates07
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing SharingGateModel
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem gate54 (ports : Fin 4 → V) (v : Fin 34 → V) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 54) = ringCompute GateOp.add (pairValue ι (a 50)) (pairValue ι (a 53)) := by
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat] <;> ring

theorem gate55 (ports : Fin 4 → V) (v : Fin 34 → V) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 55) = ringCompute GateOp.mul (pairValue ι (a 27)) (pairValue ι (a 9)) := by
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat] <;> ring

theorem gate56 (ports : Fin 4 → V) (v : Fin 34 → V) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 56) = ringCompute GateOp.add (pairValue ι (a 55)) (pairValue ι (a 28)) := by
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat] <;> ring

theorem gate57 (ports : Fin 4 → V) (v : Fin 34 → V)
    (hc : Sign33ResidualAssembly.AllCuts ports v) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 57) = ringCompute GateOp.sub (pairValue ι (a 56)) (pairValue ι (a 54)) := by
  have h := hc.batch04.2.1
  simp only [Sign33ResidualBatch04.q, Sign33ResidualBatch04.t] at h
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat]
  rw [h]
  ring

theorem gate58 (ports : Fin 4 → V) (v : Fin 34 → V) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 58) = ringCompute GateOp.mul (pairValue ι (a 57)) (pairValue ι (a 57)) := by
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat] <;> ring

theorem gate59 (ports : Fin 4 → V) (v : Fin 34 → V) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 59) = ringCompute GateOp.add (pairValue ι (a 30)) (pairValue ι (a 28)) := by
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat] <;> ring

end DiophantineConsistency.Sign33RingGates07
#print axioms DiophantineConsistency.Sign33RingGates07.gate54
#print axioms DiophantineConsistency.Sign33RingGates07.gate55
#print axioms DiophantineConsistency.Sign33RingGates07.gate56
#print axioms DiophantineConsistency.Sign33RingGates07.gate57
#print axioms DiophantineConsistency.Sign33RingGates07.gate58
#print axioms DiophantineConsistency.Sign33RingGates07.gate59
