import DiophantineConsistency.Norm38EachSlot
import DiophantineConsistency.Norm38Slots06
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38GateExtraction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel Norm38SlotExtraction
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Proposed component equations for gate 66. -/
theorem gate66 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    let v := NormAssignment38.assignment ports w
    positiveResidual ι GateOp.sub (v 64) (v 65) (v 66) = 0 ∧
      negativeResidual ι GateOp.sub (v 64) (v 65) (v 66) = 0 := by
  simp [NormAssignment38.assignment, positiveResidual, negativeResidual, pairCompute, map_ofNat]

/-- Proposed component equations for gate 67. -/
theorem gate67 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    let v := NormAssignment38.assignment ports w
    positiveResidual ι GateOp.mul (v 4) (v 4) (v 67) = 0 ∧
      negativeResidual ι GateOp.mul (v 4) (v 4) (v 67) = 0 := by
  have h18 := each_slot_zero p w hz 18
  rw [slot18 p ports w hp] at h18
  refine ⟨h18, ?_⟩
  simp [NormAssignment38.assignment, negativeResidual, pairCompute, map_ofNat]

/-- Proposed component equations for gate 68. -/
theorem gate68 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    let v := NormAssignment38.assignment ports w
    positiveResidual ι GateOp.mul (v 31) (v 6) (v 68) = 0 ∧
      negativeResidual ι GateOp.mul (v 31) (v 6) (v 68) = 0 := by
  simp [NormAssignment38.assignment, positiveResidual, negativeResidual, pairCompute, map_ofNat]

/-- Proposed component equations for gate 69. -/
theorem gate69 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    let v := NormAssignment38.assignment ports w
    positiveResidual ι GateOp.sub (v 68) (v 54) (v 69) = 0 ∧
      negativeResidual ι GateOp.sub (v 68) (v 54) (v 69) = 0 := by
  have h19 := each_slot_zero p w hz 19
  rw [slot19 p ports w hp] at h19
  have h20 := each_slot_zero p w hz 20
  rw [slot20 p ports w hp] at h20
  exact ⟨h19, h20⟩

/-- Proposed component equations for gate 70. -/
theorem gate70 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    let v := NormAssignment38.assignment ports w
    positiveResidual ι GateOp.mul (v 67) (v 69) (v 70) = 0 ∧
      negativeResidual ι GateOp.mul (v 67) (v 69) (v 70) = 0 := by
  simp [NormAssignment38.assignment, positiveResidual, negativeResidual, pairCompute, map_ofNat]


end DiophantineConsistency.Norm38GateExtraction
