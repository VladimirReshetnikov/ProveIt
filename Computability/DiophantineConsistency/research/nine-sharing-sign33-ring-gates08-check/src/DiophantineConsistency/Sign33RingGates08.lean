import DiophantineConsistency.Sign33Lift38
import DiophantineConsistency.NormAssignment38

/-! Six ring-value gate equations for the canonical lift. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33RingGates08
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing SharingGateModel
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem gate60 (ports : Fin 4 → V) (v : Fin 34 → V) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 60) = ringCompute GateOp.mul (pairValue ι (a 30)) (pairValue ι (a 59)) := by
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat] <;> ring

theorem gate61 (ports : Fin 4 → V) (v : Fin 34 → V) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 61) = ringCompute GateOp.sub (pairValue ι (a 58)) (pairValue ι (a 60)) := by
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat] <;> ring

theorem gate62 (ports : Fin 4 → V) (v : Fin 34 → V) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 62) = ringCompute GateOp.add (pairValue ι (a 15)) (pairValue ι (a 8)) := by
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat] <;> ring

theorem gate63 (ports : Fin 4 → V) (v : Fin 34 → V) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 63) = ringCompute GateOp.mul (pairValue ι (a 62)) (pairValue ι (a 46)) := by
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat] <;> ring

theorem gate64 (ports : Fin 4 → V) (v : Fin 34 → V) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 64) = ringCompute GateOp.add (pairValue ι (a 63)) (pairValue ι (a 45)) := by
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat] <;> ring

theorem gate65 (ports : Fin 4 → V) (v : Fin 34 → V) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 65) = ringCompute GateOp.mul (pairValue ι (a 3)) (pairValue ι (a 21)) := by
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat] <;> ring

end DiophantineConsistency.Sign33RingGates08
#print axioms DiophantineConsistency.Sign33RingGates08.gate60
#print axioms DiophantineConsistency.Sign33RingGates08.gate61
#print axioms DiophantineConsistency.Sign33RingGates08.gate62
#print axioms DiophantineConsistency.Sign33RingGates08.gate63
#print axioms DiophantineConsistency.Sign33RingGates08.gate64
#print axioms DiophantineConsistency.Sign33RingGates08.gate65
