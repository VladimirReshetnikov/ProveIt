import DiophantineConsistency.Norm38EachSlot
import DiophantineConsistency.Norm38Slots00
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38GateExtraction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel Norm38SlotExtraction
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Proposed component equations for gate 21. -/
theorem gate21 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    let v := NormAssignment38.assignment ports w
    positiveResidual ι GateOp.mul (v 14) (v 0) (v 21) = 0 ∧
      negativeResidual ι GateOp.mul (v 14) (v 0) (v 21) = 0 := by
  simp [NormAssignment38.assignment, positiveResidual, negativeResidual, pairCompute, map_ofNat]

/-- Proposed component equations for gate 22. -/
theorem gate22 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    let v := NormAssignment38.assignment ports w
    positiveResidual ι GateOp.add (v 21) (v 18) (v 22) = 0 ∧
      negativeResidual ι GateOp.add (v 21) (v 18) (v 22) = 0 := by
  simp [NormAssignment38.assignment, positiveResidual, negativeResidual, pairCompute, map_ofNat]

/-- Proposed component equations for gate 23. -/
theorem gate23 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    let v := NormAssignment38.assignment ports w
    positiveResidual ι GateOp.mul (v 22) (v 22) (v 23) = 0 ∧
      negativeResidual ι GateOp.mul (v 22) (v 22) (v 23) = 0 := by
  have h00 := each_slot_zero p w hz 0
  rw [slot00 p ports w hp] at h00
  refine ⟨h00, ?_⟩
  simp [NormAssignment38.assignment, negativeResidual, pairCompute, map_ofNat]

/-- Proposed component equations for gate 24. -/
theorem gate24 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    let v := NormAssignment38.assignment ports w
    positiveResidual ι GateOp.mul (v 23) (v 22) (v 24) = 0 ∧
      negativeResidual ι GateOp.mul (v 23) (v 22) (v 24) = 0 := by
  have h01 := each_slot_zero p w hz 1
  rw [slot01 p ports w hp] at h01
  refine ⟨h01, ?_⟩
  simp [NormAssignment38.assignment, negativeResidual, pairCompute, map_ofNat]

/-- Proposed component equations for gate 25. -/
theorem gate25 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    let v := NormAssignment38.assignment ports w
    positiveResidual ι GateOp.mul (v 8) (v 22) (v 25) = 0 ∧
      negativeResidual ι GateOp.mul (v 8) (v 22) (v 25) = 0 := by
  have h02 := each_slot_zero p w hz 2
  rw [slot02 p ports w hp] at h02
  refine ⟨h02, ?_⟩
  simp [NormAssignment38.assignment, negativeResidual, pairCompute, map_ofNat]


end DiophantineConsistency.Norm38GateExtraction
