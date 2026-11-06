import DiophantineConsistency.ArithmeticPellHalfIndex
import DiophantineConsistency.ModelDifferenceRing

/-! Rebuild the absdiff-square embedding on the current sign33 model provider. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33AbsDiffSquare
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticPellHalfIndex
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem cast_tsub {a b : V} (h : b ≤ a) : ι (a-b) = ι a-ι b := by
  rw [eq_sub_iff_add_eq, ← map_add, tsub_add_cancel_of_le h]

theorem absdiff_sq (x y : V) :
    ι (absdiff x y) * ι (absdiff x y) = (ι x-ι y)*(ι x-ι y) := by
  rcases le_total y x with h | h
  · have h0 : y-x = 0 := tsub_eq_zero_of_le h
    simp only [absdiff, h0, add_zero]
    rw [cast_tsub h]
  · have h0 : x-y = 0 := tsub_eq_zero_of_le h
    simp only [absdiff, h0, zero_add]
    rw [cast_tsub h]
    ring
end DiophantineConsistency.Sign33AbsDiffSquare
#print axioms DiophantineConsistency.Sign33AbsDiffSquare.absdiff_sq
