import DiophantineConsistency.NormAssignment38
import DiophantineConsistency.ForwardWitness38
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38ForwardGates
open SharingGateModel
variable {S R : Type*} [CommSemiring S] [CommRing R]

/-- Proposed natural-constructor component equations for gate 66. -/
theorem forwardGate66 (embed : S →+* R) (ports : Fin 4 → S) (u : Fin 14 → S) :
    let v := NormAssignment38.assignment ports (SharingForward38.witnessCoordinates ports u)
    positiveResidual embed GateOp.sub (v 64) (v 65) (v 66) = 0 ∧
      negativeResidual embed GateOp.sub (v 64) (v 65) (v 66) = 0 := by
  simp [NormAssignment38.assignment, SharingForward38.witnessCoordinates,
    positiveResidual, negativeResidual, pairCompute, map_add, map_mul, map_ofNat]

/-- Proposed natural-constructor component equations for gate 67. -/
theorem forwardGate67 (embed : S →+* R) (ports : Fin 4 → S) (u : Fin 14 → S) :
    let v := NormAssignment38.assignment ports (SharingForward38.witnessCoordinates ports u)
    positiveResidual embed GateOp.mul (v 4) (v 4) (v 67) = 0 ∧
      negativeResidual embed GateOp.mul (v 4) (v 4) (v 67) = 0 := by
  simp [NormAssignment38.assignment, SharingForward38.witnessCoordinates,
    positiveResidual, negativeResidual, pairCompute, map_add, map_mul, map_ofNat]

/-- Proposed natural-constructor component equations for gate 68. -/
theorem forwardGate68 (embed : S →+* R) (ports : Fin 4 → S) (u : Fin 14 → S) :
    let v := NormAssignment38.assignment ports (SharingForward38.witnessCoordinates ports u)
    positiveResidual embed GateOp.mul (v 31) (v 6) (v 68) = 0 ∧
      negativeResidual embed GateOp.mul (v 31) (v 6) (v 68) = 0 := by
  simp [NormAssignment38.assignment, SharingForward38.witnessCoordinates,
    positiveResidual, negativeResidual, pairCompute, map_add, map_mul, map_ofNat]

/-- Proposed natural-constructor component equations for gate 69. -/
theorem forwardGate69 (embed : S →+* R) (ports : Fin 4 → S) (u : Fin 14 → S) :
    let v := NormAssignment38.assignment ports (SharingForward38.witnessCoordinates ports u)
    positiveResidual embed GateOp.sub (v 68) (v 54) (v 69) = 0 ∧
      negativeResidual embed GateOp.sub (v 68) (v 54) (v 69) = 0 := by
  simp [NormAssignment38.assignment, SharingForward38.witnessCoordinates,
    positiveResidual, negativeResidual, pairCompute, map_add, map_mul, map_ofNat]

/-- Proposed natural-constructor component equations for gate 70. -/
theorem forwardGate70 (embed : S →+* R) (ports : Fin 4 → S) (u : Fin 14 → S) :
    let v := NormAssignment38.assignment ports (SharingForward38.witnessCoordinates ports u)
    positiveResidual embed GateOp.mul (v 67) (v 69) (v 70) = 0 ∧
      negativeResidual embed GateOp.mul (v 67) (v 69) (v 70) = 0 := by
  simp [NormAssignment38.assignment, SharingForward38.witnessCoordinates,
    positiveResidual, negativeResidual, pairCompute, map_add, map_mul, map_ofNat]


end DiophantineConsistency.Norm38ForwardGates
