import DiophantineConsistency.Norm38EachSlot
import DiophantineConsistency.Norm38Slots01
import DiophantineConsistency.Norm38Slots02
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38GateExtraction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel Norm38SlotExtraction
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Proposed component equations for gate 26. -/
theorem gate26 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    let v := NormAssignment38.assignment ports w
    positiveResidual ι GateOp.mul (v 7) (v 24) (v 26) = 0 ∧
      negativeResidual ι GateOp.mul (v 7) (v 24) (v 26) = 0 := by
  have h03 := each_slot_zero p w hz 3
  rw [slot03 p ports w hp] at h03
  refine ⟨h03, ?_⟩
  simp [NormAssignment38.assignment, negativeResidual, pairCompute, map_ofNat]

/-- Proposed component equations for gate 27. -/
theorem gate27 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    let v := NormAssignment38.assignment ports w
    positiveResidual ι GateOp.mul (v 25) (v 26) (v 27) = 0 ∧
      negativeResidual ι GateOp.mul (v 25) (v 26) (v 27) = 0 := by
  have h04 := each_slot_zero p w hz 4
  rw [slot04 p ports w hp] at h04
  refine ⟨h04, ?_⟩
  simp [NormAssignment38.assignment, negativeResidual, pairCompute, map_ofNat]

/-- Proposed component equations for gate 28. -/
theorem gate28 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    let v := NormAssignment38.assignment ports w
    positiveResidual ι GateOp.add (v 10) (v 11) (v 28) = 0 ∧
      negativeResidual ι GateOp.add (v 10) (v 11) (v 28) = 0 := by
  simp [NormAssignment38.assignment, positiveResidual, negativeResidual, pairCompute, map_ofNat]

/-- Proposed component equations for gate 29. -/
theorem gate29 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    let v := NormAssignment38.assignment ports w
    positiveResidual ι GateOp.mul (v 28) (v 26) (v 29) = 0 ∧
      negativeResidual ι GateOp.mul (v 28) (v 26) (v 29) = 0 := by
  have h05 := each_slot_zero p w hz 5
  rw [slot05 p ports w hp] at h05
  refine ⟨h05, ?_⟩
  simp [NormAssignment38.assignment, negativeResidual, pairCompute, map_ofNat]

/-- Proposed component equations for gate 30. -/
theorem gate30 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    let v := NormAssignment38.assignment ports w
    positiveResidual ι GateOp.mul (v 27) (v 29) (v 30) = 0 ∧
      negativeResidual ι GateOp.mul (v 27) (v 29) (v 30) = 0 := by
  have h06 := each_slot_zero p w hz 6
  rw [slot06 p ports w hp] at h06
  refine ⟨h06, ?_⟩
  simp [NormAssignment38.assignment, negativeResidual, pairCompute, map_ofNat]


end DiophantineConsistency.Norm38GateExtraction
