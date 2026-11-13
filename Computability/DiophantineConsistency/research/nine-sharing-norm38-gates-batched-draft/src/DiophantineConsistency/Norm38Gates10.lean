import DiophantineConsistency.Norm38EachSlot
import DiophantineConsistency.Norm38Slots07
import DiophantineConsistency.Norm38Slots08
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38GateExtraction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel Norm38SlotExtraction
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Proposed component equations for gate 71. -/
theorem gate71 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    let v := NormAssignment38.assignment ports w
    positiveResidual ι GateOp.sub (v 70) (v 31) (v 71) = 0 ∧
      negativeResidual ι GateOp.sub (v 70) (v 31) (v 71) = 0 := by
  have h21 := each_slot_zero p w hz 21
  rw [slot21 p ports w hp] at h21
  have h22 := each_slot_zero p w hz 22
  rw [slot22 p ports w hp] at h22
  exact ⟨h21, h22⟩

/-- Proposed component equations for gate 72. -/
theorem gate72 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    let v := NormAssignment38.assignment ports w
    positiveResidual ι GateOp.mul (v 5) (v 42) (v 72) = 0 ∧
      negativeResidual ι GateOp.mul (v 5) (v 42) (v 72) = 0 := by
  have h23 := each_slot_zero p w hz 23
  rw [slot23 p ports w hp] at h23
  refine ⟨h23, ?_⟩
  simp [NormAssignment38.assignment, negativeResidual, pairCompute, map_ofNat]

/-- Proposed component equations for gate 73. -/
theorem gate73 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    let v := NormAssignment38.assignment ports w
    positiveResidual ι GateOp.mul (v 72) (v 72) (v 73) = 0 ∧
      negativeResidual ι GateOp.mul (v 72) (v 72) (v 73) = 0 := by
  have h24 := each_slot_zero p w hz 24
  rw [slot24 p ports w hp] at h24
  refine ⟨h24, ?_⟩
  simp [NormAssignment38.assignment, negativeResidual, pairCompute, map_ofNat]

/-- Proposed component equations for gate 74. -/
theorem gate74 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    let v := NormAssignment38.assignment ports w
    positiveResidual ι GateOp.mul (v 71) (v 71) (v 74) = 0 ∧
      negativeResidual ι GateOp.mul (v 71) (v 71) (v 74) = 0 := by
  simp [NormAssignment38.assignment, positiveResidual, negativeResidual, pairCompute, map_ofNat]

/-- Proposed component equations for gate 75. -/
theorem gate75 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    let v := NormAssignment38.assignment ports w
    positiveResidual ι GateOp.mul (v 12) (v 12) (v 75) = 0 ∧
      negativeResidual ι GateOp.mul (v 12) (v 12) (v 75) = 0 := by
  simp [NormAssignment38.assignment, positiveResidual, negativeResidual, pairCompute, map_ofNat]


end DiophantineConsistency.Norm38GateExtraction
