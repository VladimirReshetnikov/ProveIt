import DiophantineConsistency.Sign33Lift38
import DiophantineConsistency.NormAssignment38

/-! Six ring-value gate equations for the canonical lift. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33RingGates04
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing SharingGateModel
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem gate36 (ports : Fin 4 → V) (v : Fin 34 → V)
    (hc : Sign33ResidualAssembly.AllCuts ports v) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 36) = ringCompute GateOp.add (pairValue ι (a 35)) (pairValue ι (a 34)) := by
  have h := hc.batch02.2.1
  simpa [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat] using h

theorem gate37 (ports : Fin 4 → V) (v : Fin 34 → V) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 37) = ringCompute GateOp.mul (pairValue ι (a 32)) (pairValue ι (a 31)) := by
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat]

theorem gate38 (ports : Fin 4 → V) (v : Fin 34 → V) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 38) = ringCompute GateOp.add (pairValue ι (a 25)) (pairValue ι (a 37)) := by
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat]

theorem gate39 (ports : Fin 4 → V) (v : Fin 34 → V) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 39) = ringCompute GateOp.mul (pairValue ι (a 13)) (pairValue ι (a 34)) := by
  simp [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat]

theorem gate40 (ports : Fin 4 → V) (v : Fin 34 → V)
    (hc : Sign33ResidualAssembly.AllCuts ports v) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 40) = ringCompute GateOp.add (pairValue ι (a 38)) (pairValue ι (a 39)) := by
  have h := hc.batch02.2.2
  simpa [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat] using h

theorem gate41 (ports : Fin 4 → V) (v : Fin 34 → V)
    (hc : Sign33ResidualAssembly.AllCuts ports v) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    pairValue ι (a 41) = ringCompute GateOp.mul (pairValue ι (a 31)) (pairValue ι (a 31)) := by
  have h := hc.batch03.1
  simpa [NormAssignment38.assignment, Sign33Lift38.lift, pairValue, pairCompute, ringCompute,
    map_add, map_mul, map_ofNat] using h

end DiophantineConsistency.Sign33RingGates04
#print axioms DiophantineConsistency.Sign33RingGates04.gate36
#print axioms DiophantineConsistency.Sign33RingGates04.gate37
#print axioms DiophantineConsistency.Sign33RingGates04.gate38
#print axioms DiophantineConsistency.Sign33RingGates04.gate39
#print axioms DiophantineConsistency.Sign33RingGates04.gate40
#print axioms DiophantineConsistency.Sign33RingGates04.gate41
