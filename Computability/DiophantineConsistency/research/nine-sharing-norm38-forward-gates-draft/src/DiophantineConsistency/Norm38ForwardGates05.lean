import DiophantineConsistency.NormAssignment38
import DiophantineConsistency.ForwardWitness38
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38ForwardGates
open SharingGateModel
variable {S R : Type*} [CommSemiring S] [CommRing R]

/-- Proposed natural-constructor component equations for gate 46. -/
theorem forwardGate46 (embed : S →+* R) (ports : Fin 4 → S) (u : Fin 14 → S) :
    let v := NormAssignment38.assignment ports (SharingForward38.witnessCoordinates ports u)
    positiveResidual embed GateOp.sub (v 45) (v 2) (v 46) = 0 ∧
      negativeResidual embed GateOp.sub (v 45) (v 2) (v 46) = 0 := by
  simp [NormAssignment38.assignment, SharingForward38.witnessCoordinates,
    positiveResidual, negativeResidual, pairCompute, map_add, map_mul, map_ofNat]

/-- Proposed natural-constructor component equations for gate 47. -/
theorem forwardGate47 (embed : S →+* R) (ports : Fin 4 → S) (u : Fin 14 → S) :
    let v := NormAssignment38.assignment ports (SharingForward38.witnessCoordinates ports u)
    positiveResidual embed GateOp.mul (v 21) (v 45) (v 47) = 0 ∧
      negativeResidual embed GateOp.mul (v 21) (v 45) (v 47) = 0 := by
  simp [NormAssignment38.assignment, SharingForward38.witnessCoordinates,
    positiveResidual, negativeResidual, pairCompute, map_add, map_mul, map_ofNat]

/-- Proposed natural-constructor component equations for gate 48. -/
theorem forwardGate48 (embed : S →+* R) (ports : Fin 4 → S) (u : Fin 14 → S) :
    let v := NormAssignment38.assignment ports (SharingForward38.witnessCoordinates ports u)
    positiveResidual embed GateOp.add (v 47) (v 2) (v 48) = 0 ∧
      negativeResidual embed GateOp.add (v 47) (v 2) (v 48) = 0 := by
  simp [NormAssignment38.assignment, SharingForward38.witnessCoordinates,
    positiveResidual, negativeResidual, pairCompute, map_add, map_mul, map_ofNat]

/-- Proposed natural-constructor component equations for gate 49. -/
theorem forwardGate49 (embed : S →+* R) (ports : Fin 4 → S) (u : Fin 14 → S) :
    let v := NormAssignment38.assignment ports (SharingForward38.witnessCoordinates ports u)
    positiveResidual embed GateOp.sub (v 23) (v 18) (v 49) = 0 ∧
      negativeResidual embed GateOp.sub (v 23) (v 18) (v 49) = 0 := by
  simp [NormAssignment38.assignment, SharingForward38.witnessCoordinates,
    positiveResidual, negativeResidual, pairCompute, map_add, map_mul, map_ofNat]

/-- Proposed natural-constructor component equations for gate 50. -/
theorem forwardGate50 (embed : S →+* R) (ports : Fin 4 → S) (u : Fin 14 → S) :
    let v := NormAssignment38.assignment ports (SharingForward38.witnessCoordinates ports u)
    positiveResidual embed GateOp.mul (v 48) (v 49) (v 50) = 0 ∧
      negativeResidual embed GateOp.mul (v 48) (v 49) (v 50) = 0 := by
  simp [NormAssignment38.assignment, SharingForward38.witnessCoordinates,
    positiveResidual, negativeResidual, pairCompute, map_add, map_mul, map_ofNat]


end DiophantineConsistency.Norm38ForwardGates
