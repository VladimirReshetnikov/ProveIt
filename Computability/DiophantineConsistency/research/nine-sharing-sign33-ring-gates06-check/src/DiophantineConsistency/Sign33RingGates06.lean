import DiophantineConsistency.Sign33Lift38
import DiophantineConsistency.NormAssignment38

/-! Six ring-value gate equations for the canonical lift. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33RingGates06
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing SharingGateModel
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem gate48 (ports : Fin 4 → V) (v : Fin 34 → V)
    (hc : Sign33ResidualAssembly.AllCuts ports v) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 48) = ringCompute GateOp.add (pairValue ι (a 47)) (pairValue ι (a 2)) := by
  have h := hc.batch04.1
  simp only [Sign33ResidualBatch04.t] at h
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat]
  rw [h]
  ring

theorem gate49 (ports : Fin 4 → V) (v : Fin 34 → V) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 49) = ringCompute GateOp.sub (pairValue ι (a 23)) (pairValue ι (a 18)) := by
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat] <;> ring

theorem gate50 (ports : Fin 4 → V) (v : Fin 34 → V) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 50) = ringCompute GateOp.mul (pairValue ι (a 48)) (pairValue ι (a 49)) := by
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat] <;> ring

theorem gate51 (ports : Fin 4 → V) (v : Fin 34 → V) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 51) = ringCompute GateOp.mul (pairValue ι (a 22)) (pairValue ι (a 17)) := by
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat] <;> ring

theorem gate52 (ports : Fin 4 → V) (v : Fin 34 → V) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 52) = ringCompute GateOp.add (pairValue ι (a 16)) (pairValue ι (a 51)) := by
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat] <;> ring

theorem gate53 (ports : Fin 4 → V) (v : Fin 34 → V) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 53) = ringCompute GateOp.mul (pairValue ι (a 52)) (pairValue ι (a 0)) := by
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat] <;> ring

end DiophantineConsistency.Sign33RingGates06
#print axioms DiophantineConsistency.Sign33RingGates06.gate48
#print axioms DiophantineConsistency.Sign33RingGates06.gate49
#print axioms DiophantineConsistency.Sign33RingGates06.gate50
#print axioms DiophantineConsistency.Sign33RingGates06.gate51
#print axioms DiophantineConsistency.Sign33RingGates06.gate52
#print axioms DiophantineConsistency.Sign33RingGates06.gate53
