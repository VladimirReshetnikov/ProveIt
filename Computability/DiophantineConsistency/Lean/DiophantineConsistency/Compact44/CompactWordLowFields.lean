import DiophantineConsistency.Compact44.CompactOriginLowNoCarry
import DiophantineConsistency.Compact44.CompactPulsePackedCell

/-! Origin and low-mask fields for a compact word and Boolean perturbation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactWordLowFields
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticBinaryCarry ArithmeticWindowDigits
open CompactMarkedTransport CompactPackedCell CompactBaseLowNoCarry
open CompactOriginLowNoCarry CompactPulsePackedCell

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def baseCell (row : V → V) (j : V) : V := packedCell (row j) 0
def pulsedCell (row δ : V → V) (j : V) : V :=
  baseCell row j + Exp.exp (67*1063) * δ j

/-- Exactly the origin and local low-mask fields for the base word. -/
theorem base_low_fields {row : V → V} {N s : V} (hw : CompactWord row N s) :
    1 ≤ baseCell row 0 ∧
    NoCarry (baseCell row 0 - 1) (CompactConcreteIncrement.mask + 1) ∧
    (∀ j < N, NoCarry (baseCell row j) CompactConcreteIncrement.mask) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold baseCell
    rw [hw.marker]
    exact packedCell_origin 0 (by simp)
  · unfold baseCell
    rw [hw.marker]
    exact origin_low_noCarry
  · intro j hj
    exact base_noCarry (row j) (hw.tile_ne j hj)

/-- The same fields after any Boolean perturbation away from the origin.
This statement does not supply the product, block or high-mask fields. -/
theorem pulsed_low_fields {row δ : V → V} {N s : V} (hw : CompactWord row N s)
    (hbool : ∀ j, δ j ≤ 1) (hpos : ∀ j, δ j ≠ 0 → 0 < j) :
    1 ≤ pulsedCell row δ 0 ∧
    NoCarry (pulsedCell row δ 0 - 1) (CompactConcreteIncrement.mask + 1) ∧
    (∀ j < N, NoCarry (pulsedCell row δ j) CompactConcreteIncrement.mask) := by
  have hz : δ 0 = 0 := by
    by_contra hne
    exact (Arithmetic.lt_irrefl (0 : V)) (hpos 0 hne)
  have h0 : pulsedCell row δ 0 = baseCell row 0 := by
    simp only [pulsedCell, hz, mul_zero, add_zero]
  obtain ⟨ho, hlo, hlow⟩ := base_low_fields hw
  refine ⟨?_, ?_, ?_⟩
  · rw [h0]; exact ho
  · rw [h0]; exact hlo
  · intro j hj
    rcases le_one_iff_eq_zero_or_one.mp (hbool j) with hzero | hone
    · simpa only [pulsedCell, hzero, mul_zero, add_zero] using hlow j hj
    · have hbase := hlow j hj
      have hp := packedCell_pulse_noCarry (row j) hbase
      simpa only [pulsedCell, baseCell, hone, mul_one] using hp

#print axioms CompactWordLowFields.base_low_fields
#print axioms CompactWordLowFields.pulsed_low_fields
end CompactWordLowFields
