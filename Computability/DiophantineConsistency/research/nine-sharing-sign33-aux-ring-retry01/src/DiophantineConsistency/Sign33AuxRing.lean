import DiophantineConsistency.Sign33AbsDiffSquare
import Sign33OrderedRing

/-! Transport an explicit natural auxiliary norm to a difference-ring sign. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33AuxRing
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticPellHalfIndex
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem aux_difference_of_norm (S x z y : V)
    (hS : 0<S) (hy : 0<y)
    (haux : S*S*(absdiff x z)*(absdiff x z)+y*y=1+S*S*y*y) :
    (ι x-ι z)*(ι x-ι z)-ι y*ι y ≤ 0 := by
  have hSring : (0 : DiffRing V) < ι S := by
    simpa only [map_zero] using (ι_lt_ι.mpr hS)
  have hyring : (1 : DiffRing V) ≤ ι y := by
    simpa only [map_one] using (ι_le_ι.mpr (pos_iff_one_le.mp hy))
  have he := congrArg (ι : V →+* DiffRing V) haux
  simp only [map_add, map_mul, map_one] at he
  have hsq := Sign33AbsDiffSquare.absdiff_sq x z
  have hauxring : ι S*ι S*((ι x-ι z)*(ι x-ι z)-ι y*ι y)+ι y*ι y=1 := by
    rw [← hsq]
    nlinarith [he]
  exact Sign33OrderedRing.auxiliary_difference_sign (ι S) (ι x-ι z) (ι y) hSring hyring hauxring
end DiophantineConsistency.Sign33AuxRing
#print axioms DiophantineConsistency.Sign33AuxRing.aux_difference_of_norm
