import DiophantineConsistency.NormAssignment38
import DiophantineConsistency.ForwardWitness38
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38ForwardGates
open SharingGateModel
variable {S R : Type*} [CommSemiring S] [CommRing R]

/-- Proposed natural-constructor component equations for gate 76. -/
theorem forwardGate76 (embed : S →+* R) (ports : Fin 4 → S) (u : Fin 14 → S) :
    let v := NormAssignment38.assignment ports (SharingForward38.witnessCoordinates ports u)
    positiveResidual embed GateOp.sub (v 74) (v 75) (v 76) = 0 ∧
      negativeResidual embed GateOp.sub (v 74) (v 75) (v 76) = 0 := by
  simp [NormAssignment38.assignment, SharingForward38.witnessCoordinates,
    positiveResidual, negativeResidual, pairCompute, map_add, map_mul, map_ofNat]

/-- Proposed natural-constructor component equations for gate 77. -/
theorem forwardGate77 (embed : S →+* R) (ports : Fin 4 → S) (u : Fin 14 → S) :
    let v := NormAssignment38.assignment ports (SharingForward38.witnessCoordinates ports u)
    positiveResidual embed GateOp.mul (v 73) (v 76) (v 77) = 0 ∧
      negativeResidual embed GateOp.mul (v 73) (v 76) (v 77) = 0 := by
  simp [NormAssignment38.assignment, SharingForward38.witnessCoordinates,
    positiveResidual, negativeResidual, pairCompute, map_add, map_mul, map_ofNat]

/-- Proposed natural-constructor component equations for gate 78. -/
theorem forwardGate78 (embed : S →+* R) (ports : Fin 4 → S) (u : Fin 14 → S) :
    let v := NormAssignment38.assignment ports (SharingForward38.witnessCoordinates ports u)
    positiveResidual embed GateOp.add (v 77) (v 75) (v 78) = 0 ∧
      negativeResidual embed GateOp.add (v 77) (v 75) (v 78) = 0 := by
  simp [NormAssignment38.assignment, SharingForward38.witnessCoordinates,
    positiveResidual, negativeResidual, pairCompute, map_add, map_mul, map_ofNat]

/-- Proposed natural-constructor component equations for gate 79. -/
theorem forwardGate79 (embed : S →+* R) (ports : Fin 4 → S) (u : Fin 14 → S) :
    let v := NormAssignment38.assignment ports (SharingForward38.witnessCoordinates ports u)
    positiveResidual embed GateOp.mul (v 36) (v 67) (v 79) = 0 ∧
      negativeResidual embed GateOp.mul (v 36) (v 67) (v 79) = 0 := by
  simp [NormAssignment38.assignment, SharingForward38.witnessCoordinates,
    positiveResidual, negativeResidual, pairCompute, map_add, map_mul, map_ofNat]

/-- Proposed natural-constructor component equations for gate 80. -/
theorem forwardGate80 (embed : S →+* R) (ports : Fin 4 → S) (u : Fin 14 → S) :
    let v := NormAssignment38.assignment ports (SharingForward38.witnessCoordinates ports u)
    positiveResidual embed GateOp.sub (v 79) (v 73) (v 80) = 0 ∧
      negativeResidual embed GateOp.sub (v 79) (v 73) (v 80) = 0 := by
  simp [NormAssignment38.assignment, SharingForward38.witnessCoordinates,
    positiveResidual, negativeResidual, pairCompute, map_add, map_mul, map_ofNat]


end DiophantineConsistency.Norm38ForwardGates
