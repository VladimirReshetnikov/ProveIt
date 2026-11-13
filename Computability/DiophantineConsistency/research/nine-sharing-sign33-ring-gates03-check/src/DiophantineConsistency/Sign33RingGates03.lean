import DiophantineConsistency.Sign33Lift38
import DiophantineConsistency.NormAssignment38

/-! Six ring-value gate equations for the canonical lift. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33RingGates03
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing SharingGateModel
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem gate30 (ports : Fin 4 → V) (v : Fin 34 → V)
    (hc : Sign33ResidualAssembly.AllCuts ports v) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 30) = ringCompute GateOp.mul (pairValue ι (a 27)) (pairValue ι (a 29)) := by
  have h := hc.batch02.1
  simpa [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat] using h

theorem gate31 (ports : Fin 4 → V) (v : Fin 34 → V) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 31) = ringCompute GateOp.add (pairValue ι (a 29)) (pairValue ι (a 10)) := by
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat]

theorem gate32 (ports : Fin 4 → V) (v : Fin 34 → V) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 32) = ringCompute GateOp.add (pairValue ι (a 27)) (pairValue ι (a 26)) := by
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat]

theorem gate33 (ports : Fin 4 → V) (v : Fin 34 → V) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 33) = ringCompute GateOp.mul (pairValue ι (a 20)) (pairValue ι (a 32)) := by
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat]

theorem gate34 (ports : Fin 4 → V) (v : Fin 34 → V) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 34) = ringCompute GateOp.add (pairValue ι (a 33)) (pairValue ι (a 19)) := by
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat]

theorem gate35 (ports : Fin 4 → V) (v : Fin 34 → V) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 35) = ringCompute GateOp.mul (pairValue ι (a 32)) (pairValue ι (a 32)) := by
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat]

end DiophantineConsistency.Sign33RingGates03
#print axioms DiophantineConsistency.Sign33RingGates03.gate30
#print axioms DiophantineConsistency.Sign33RingGates03.gate31
#print axioms DiophantineConsistency.Sign33RingGates03.gate32
#print axioms DiophantineConsistency.Sign33RingGates03.gate33
#print axioms DiophantineConsistency.Sign33RingGates03.gate34
#print axioms DiophantineConsistency.Sign33RingGates03.gate35
