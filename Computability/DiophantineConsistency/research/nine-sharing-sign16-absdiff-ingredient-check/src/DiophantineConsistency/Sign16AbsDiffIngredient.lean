import DiophantineConsistency.Sign33AbsDiffSquare

/-! SOURCE-ONLY non-circular square identity and auxiliary norm transport. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign16AbsDiffIngredient
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticPellHalfIndex
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem absdiff_V_square (f c T r inner : V)
    (hinner : ι inner = ι c * ι T - ι r) :
    ι (absdiff (f*f*c*T) (f*f*r+c)) * ι (absdiff (f*f*c*T) (f*f*r+c)) =
      (ι f*ι f*ι inner-ι c) * (ι f*ι f*ι inner-ι c) := by
  rw [Sign33AbsDiffSquare.absdiff_sq]
  simp only [map_add, map_mul]
  rw [hinner]
  ring

theorem auxiliary_norm_of_signed (f c T r inner S y : V)
    (hinner : ι inner = ι c * ι T - ι r)
    (hNa : ι y*ι y - (ι S*ι S)*((ι y*ι y) -
      (ι f*ι f*ι inner-ι c)*(ι f*ι f*ι inner-ι c)) - 1 = 0) :
    S*S*(absdiff (f*f*c*T) (f*f*r+c))*(absdiff (f*f*c*T) (f*f*r+c)) + y*y =
      1 + S*S*y*y := by
  have hs := absdiff_V_square f c T r inner hinner
  apply ι_injective
  simp only [map_add, map_mul, map_one]
  linear_combination hNa + (ι S)*(ι S)*hs
end DiophantineConsistency.Sign16AbsDiffIngredient
#print axioms DiophantineConsistency.Sign16AbsDiffIngredient.absdiff_V_square
#print axioms DiophantineConsistency.Sign16AbsDiffIngredient.auxiliary_norm_of_signed
