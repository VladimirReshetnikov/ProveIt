import DiophantineConsistency.NormAssignment38
import DiophantineConsistency.ForwardWitness38
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38ForwardGates
open SharingGateModel
variable {S R : Type*} [CommSemiring S] [CommRing R]

/-- Proposed natural-constructor component equations for gate 31. -/
theorem forwardGate31 (embed : S →+* R) (ports : Fin 4 → S) (u : Fin 14 → S) :
    let v := NormAssignment38.assignment ports (SharingForward38.witnessCoordinates ports u)
    positiveResidual embed GateOp.add (v 29) (v 10) (v 31) = 0 ∧
      negativeResidual embed GateOp.add (v 29) (v 10) (v 31) = 0 := by
  simp [NormAssignment38.assignment, SharingForward38.witnessCoordinates,
    positiveResidual, negativeResidual, pairCompute, map_add, map_mul, map_ofNat]

/-- Proposed natural-constructor component equations for gate 32. -/
theorem forwardGate32 (embed : S →+* R) (ports : Fin 4 → S) (u : Fin 14 → S) :
    let v := NormAssignment38.assignment ports (SharingForward38.witnessCoordinates ports u)
    positiveResidual embed GateOp.add (v 27) (v 26) (v 32) = 0 ∧
      negativeResidual embed GateOp.add (v 27) (v 26) (v 32) = 0 := by
  simp [NormAssignment38.assignment, SharingForward38.witnessCoordinates,
    positiveResidual, negativeResidual, pairCompute, map_add, map_mul, map_ofNat]

/-- Proposed natural-constructor component equations for gate 33. -/
theorem forwardGate33 (embed : S →+* R) (ports : Fin 4 → S) (u : Fin 14 → S) :
    let v := NormAssignment38.assignment ports (SharingForward38.witnessCoordinates ports u)
    positiveResidual embed GateOp.mul (v 20) (v 32) (v 33) = 0 ∧
      negativeResidual embed GateOp.mul (v 20) (v 32) (v 33) = 0 := by
  simp [NormAssignment38.assignment, SharingForward38.witnessCoordinates,
    positiveResidual, negativeResidual, pairCompute, map_add, map_mul, map_ofNat]

/-- Proposed natural-constructor component equations for gate 34. -/
theorem forwardGate34 (embed : S →+* R) (ports : Fin 4 → S) (u : Fin 14 → S) :
    let v := NormAssignment38.assignment ports (SharingForward38.witnessCoordinates ports u)
    positiveResidual embed GateOp.add (v 33) (v 19) (v 34) = 0 ∧
      negativeResidual embed GateOp.add (v 33) (v 19) (v 34) = 0 := by
  simp [NormAssignment38.assignment, SharingForward38.witnessCoordinates,
    positiveResidual, negativeResidual, pairCompute, map_add, map_mul, map_ofNat]

/-- Proposed natural-constructor component equations for gate 35. -/
theorem forwardGate35 (embed : S →+* R) (ports : Fin 4 → S) (u : Fin 14 → S) :
    let v := NormAssignment38.assignment ports (SharingForward38.witnessCoordinates ports u)
    positiveResidual embed GateOp.mul (v 32) (v 32) (v 35) = 0 ∧
      negativeResidual embed GateOp.mul (v 32) (v 32) (v 35) = 0 := by
  simp [NormAssignment38.assignment, SharingForward38.witnessCoordinates,
    positiveResidual, negativeResidual, pairCompute, map_add, map_mul, map_ofNat]


end DiophantineConsistency.Norm38ForwardGates
