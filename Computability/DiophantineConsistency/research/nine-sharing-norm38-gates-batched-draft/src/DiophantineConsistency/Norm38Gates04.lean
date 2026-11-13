import DiophantineConsistency.Norm38EachSlot
import DiophantineConsistency.Norm38Slots03
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38GateExtraction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel Norm38SlotExtraction
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Proposed component equations for gate 41. -/
theorem gate41 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    let v := NormAssignment38.assignment ports w
    positiveResidual ι GateOp.mul (v 31) (v 31) (v 41) = 0 ∧
      negativeResidual ι GateOp.mul (v 31) (v 31) (v 41) = 0 := by
  have h09 := each_slot_zero p w hz 9
  rw [slot09 p ports w hp] at h09
  refine ⟨h09, ?_⟩
  simp [NormAssignment38.assignment, negativeResidual, pairCompute, map_ofNat]

/-- Proposed component equations for gate 42. -/
theorem gate42 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    let v := NormAssignment38.assignment ports w
    positiveResidual ι GateOp.mul (v 36) (v 41) (v 42) = 0 ∧
      negativeResidual ι GateOp.mul (v 36) (v 41) (v 42) = 0 := by
  have h10 := each_slot_zero p w hz 10
  rw [slot10 p ports w hp] at h10
  refine ⟨h10, ?_⟩
  simp [NormAssignment38.assignment, negativeResidual, pairCompute, map_ofNat]

/-- Proposed component equations for gate 43. -/
theorem gate43 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    let v := NormAssignment38.assignment ports w
    positiveResidual ι GateOp.mul (v 40) (v 40) (v 43) = 0 ∧
      negativeResidual ι GateOp.mul (v 40) (v 40) (v 43) = 0 := by
  simp [NormAssignment38.assignment, positiveResidual, negativeResidual, pairCompute, map_ofNat]

/-- Proposed component equations for gate 44. -/
theorem gate44 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    let v := NormAssignment38.assignment ports w
    positiveResidual ι GateOp.sub (v 43) (v 42) (v 44) = 0 ∧
      negativeResidual ι GateOp.sub (v 43) (v 42) (v 44) = 0 := by
  simp [NormAssignment38.assignment, positiveResidual, negativeResidual, pairCompute, map_ofNat]

/-- Proposed component equations for gate 45. -/
theorem gate45 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    let v := NormAssignment38.assignment ports w
    positiveResidual ι GateOp.sub (v 22) (v 1) (v 45) = 0 ∧
      negativeResidual ι GateOp.sub (v 22) (v 1) (v 45) = 0 := by
  simp [NormAssignment38.assignment, positiveResidual, negativeResidual, pairCompute, map_ofNat]


end DiophantineConsistency.Norm38GateExtraction
