import DiophantineConsistency.Norm38EachSlot
import DiophantineConsistency.Norm38Slots02
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38GateExtraction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel Norm38SlotExtraction
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Proposed component equations for gate 36. -/
theorem gate36 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    let v := NormAssignment38.assignment ports w
    positiveResidual ι GateOp.add (v 35) (v 34) (v 36) = 0 ∧
      negativeResidual ι GateOp.add (v 35) (v 34) (v 36) = 0 := by
  have h07 := each_slot_zero p w hz 7
  rw [slot07 p ports w hp] at h07
  refine ⟨h07, ?_⟩
  simp [NormAssignment38.assignment, negativeResidual, pairCompute, map_ofNat]

/-- Proposed component equations for gate 37. -/
theorem gate37 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    let v := NormAssignment38.assignment ports w
    positiveResidual ι GateOp.mul (v 32) (v 31) (v 37) = 0 ∧
      negativeResidual ι GateOp.mul (v 32) (v 31) (v 37) = 0 := by
  simp [NormAssignment38.assignment, positiveResidual, negativeResidual, pairCompute, map_ofNat]

/-- Proposed component equations for gate 38. -/
theorem gate38 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    let v := NormAssignment38.assignment ports w
    positiveResidual ι GateOp.add (v 25) (v 37) (v 38) = 0 ∧
      negativeResidual ι GateOp.add (v 25) (v 37) (v 38) = 0 := by
  simp [NormAssignment38.assignment, positiveResidual, negativeResidual, pairCompute, map_ofNat]

/-- Proposed component equations for gate 39. -/
theorem gate39 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    let v := NormAssignment38.assignment ports w
    positiveResidual ι GateOp.mul (v 13) (v 34) (v 39) = 0 ∧
      negativeResidual ι GateOp.mul (v 13) (v 34) (v 39) = 0 := by
  simp [NormAssignment38.assignment, positiveResidual, negativeResidual, pairCompute, map_ofNat]

/-- Proposed component equations for gate 40. -/
theorem gate40 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    let v := NormAssignment38.assignment ports w
    positiveResidual ι GateOp.add (v 38) (v 39) (v 40) = 0 ∧
      negativeResidual ι GateOp.add (v 38) (v 39) (v 40) = 0 := by
  have h08 := each_slot_zero p w hz 8
  rw [slot08 p ports w hp] at h08
  refine ⟨h08, ?_⟩
  simp [NormAssignment38.assignment, negativeResidual, pairCompute, map_ofNat]


end DiophantineConsistency.Norm38GateExtraction
