import DiophantineConsistency.Norm38EachSlot
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38GateExtraction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel Norm38SlotExtraction
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Proposed component equations for gate 51. -/
theorem gate51 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    let v := NormAssignment38.assignment ports w
    positiveResidual ι GateOp.mul (v 22) (v 17) (v 51) = 0 ∧
      negativeResidual ι GateOp.mul (v 22) (v 17) (v 51) = 0 := by
  simp [NormAssignment38.assignment, positiveResidual, negativeResidual, pairCompute, map_ofNat]

/-- Proposed component equations for gate 52. -/
theorem gate52 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    let v := NormAssignment38.assignment ports w
    positiveResidual ι GateOp.add (v 16) (v 51) (v 52) = 0 ∧
      negativeResidual ι GateOp.add (v 16) (v 51) (v 52) = 0 := by
  simp [NormAssignment38.assignment, positiveResidual, negativeResidual, pairCompute, map_ofNat]

/-- Proposed component equations for gate 53. -/
theorem gate53 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    let v := NormAssignment38.assignment ports w
    positiveResidual ι GateOp.mul (v 52) (v 0) (v 53) = 0 ∧
      negativeResidual ι GateOp.mul (v 52) (v 0) (v 53) = 0 := by
  simp [NormAssignment38.assignment, positiveResidual, negativeResidual, pairCompute, map_ofNat]

/-- Proposed component equations for gate 54. -/
theorem gate54 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    let v := NormAssignment38.assignment ports w
    positiveResidual ι GateOp.add (v 50) (v 53) (v 54) = 0 ∧
      negativeResidual ι GateOp.add (v 50) (v 53) (v 54) = 0 := by
  simp [NormAssignment38.assignment, positiveResidual, negativeResidual, pairCompute, map_ofNat]

/-- Proposed component equations for gate 55. -/
theorem gate55 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    let v := NormAssignment38.assignment ports w
    positiveResidual ι GateOp.mul (v 27) (v 9) (v 55) = 0 ∧
      negativeResidual ι GateOp.mul (v 27) (v 9) (v 55) = 0 := by
  simp [NormAssignment38.assignment, positiveResidual, negativeResidual, pairCompute, map_ofNat]


end DiophantineConsistency.Norm38GateExtraction
