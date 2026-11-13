import DiophantineConsistency.NormAssignment38
import DiophantineConsistency.ForwardWitness38
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38ForwardGates
open SharingGateModel
variable {S R : Type*} [CommSemiring S] [CommRing R]

/-- Proposed natural-constructor component equations for gate 51. -/
theorem forwardGate51 (embed : S →+* R) (ports : Fin 4 → S) (u : Fin 14 → S) :
    let v := NormAssignment38.assignment ports (SharingForward38.witnessCoordinates ports u)
    positiveResidual embed GateOp.mul (v 22) (v 17) (v 51) = 0 ∧
      negativeResidual embed GateOp.mul (v 22) (v 17) (v 51) = 0 := by
  simp [NormAssignment38.assignment, SharingForward38.witnessCoordinates,
    positiveResidual, negativeResidual, pairCompute, map_add, map_mul, map_ofNat]

/-- Proposed natural-constructor component equations for gate 52. -/
theorem forwardGate52 (embed : S →+* R) (ports : Fin 4 → S) (u : Fin 14 → S) :
    let v := NormAssignment38.assignment ports (SharingForward38.witnessCoordinates ports u)
    positiveResidual embed GateOp.add (v 16) (v 51) (v 52) = 0 ∧
      negativeResidual embed GateOp.add (v 16) (v 51) (v 52) = 0 := by
  simp [NormAssignment38.assignment, SharingForward38.witnessCoordinates,
    positiveResidual, negativeResidual, pairCompute, map_add, map_mul, map_ofNat]

/-- Proposed natural-constructor component equations for gate 53. -/
theorem forwardGate53 (embed : S →+* R) (ports : Fin 4 → S) (u : Fin 14 → S) :
    let v := NormAssignment38.assignment ports (SharingForward38.witnessCoordinates ports u)
    positiveResidual embed GateOp.mul (v 52) (v 0) (v 53) = 0 ∧
      negativeResidual embed GateOp.mul (v 52) (v 0) (v 53) = 0 := by
  simp [NormAssignment38.assignment, SharingForward38.witnessCoordinates,
    positiveResidual, negativeResidual, pairCompute, map_add, map_mul, map_ofNat]

/-- Proposed natural-constructor component equations for gate 54. -/
theorem forwardGate54 (embed : S →+* R) (ports : Fin 4 → S) (u : Fin 14 → S) :
    let v := NormAssignment38.assignment ports (SharingForward38.witnessCoordinates ports u)
    positiveResidual embed GateOp.add (v 50) (v 53) (v 54) = 0 ∧
      negativeResidual embed GateOp.add (v 50) (v 53) (v 54) = 0 := by
  simp [NormAssignment38.assignment, SharingForward38.witnessCoordinates,
    positiveResidual, negativeResidual, pairCompute, map_add, map_mul, map_ofNat]

/-- Proposed natural-constructor component equations for gate 55. -/
theorem forwardGate55 (embed : S →+* R) (ports : Fin 4 → S) (u : Fin 14 → S) :
    let v := NormAssignment38.assignment ports (SharingForward38.witnessCoordinates ports u)
    positiveResidual embed GateOp.mul (v 27) (v 9) (v 55) = 0 ∧
      negativeResidual embed GateOp.mul (v 27) (v 9) (v 55) = 0 := by
  simp [NormAssignment38.assignment, SharingForward38.witnessCoordinates,
    positiveResidual, negativeResidual, pairCompute, map_add, map_mul, map_ofNat]


end DiophantineConsistency.Norm38ForwardGates
