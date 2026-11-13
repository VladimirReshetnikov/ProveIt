import CompactPulsePackedCell
import CompactPulsePreservationRetry

/-! Eliminate the separate low-mask pulse premise for represented packed
cells with dummy input zero. Other packing obligations remain explicit. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactPackedPulsePreservation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticBinaryCarry ArithmeticPackingBlocks ArithmeticPacking
open CompactPackedCell CompactCanonicalPerturbation CompactPulsePreservationRetry CompactPulsePackedCell

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The low-mask pulse follows from the base packing and the actual packed
cell's empty dummy bit. Product/block and high-mask assumptions are retained. -/
theorem packing_of_packed_pulse {d K HP N s : V} (row δ : V → V)
    (h0 : PackingInput d K CompactConcreteIncrement.mask HP N s
      (fun j => packedCell (row j) 0))
    (hbool : ∀ j, δ j ≤ 1)
    (hpos : ∀ j, δ j ≠ 0 → 0 < j)
    (hhi : ∀ j < N, K * perturb (fun j => packedCell (row j) 0) δ j < Exp.exp d * Exp.exp d)
    (hcell : ∀ j < N, perturb (fun j => packedCell (row j) 0) δ j +
      blk d K N s (perturb (fun j => packedCell (row j) 0) δ) j < Exp.exp d)
    (hblk : 0 < blk d K N s (perturb (fun j => packedCell (row j) 0) δ) 0)
    (hhigh0 : NoCarry (blk d K N s (perturb (fun j => packedCell (row j) 0) δ) 0) (HP - 1))
    (hhigh : ∀ j < N, 0 < j →
      NoCarry (blk d K N s (perturb (fun j => packedCell (row j) 0) δ) j) HP) :
    PackingInput d K CompactConcreteIncrement.mask HP N s
      (perturb (fun j => packedCell (row j) 0) δ) := by
  apply packing_of_pulse h0 hbool hpos
  · intro j hj hjpos
    exact packedCell_pulse_noCarry (row j) (h0.low j hj hjpos)
  · exact hhi
  · exact hcell
  · exact hblk
  · exact hhigh0
  · exact hhigh

#print axioms CompactPackedPulsePreservation.packing_of_packed_pulse
end CompactPackedPulsePreservation
