import DiophantineConsistency.Sign33AbsDiffSquare

/-! SOURCE-ONLY auxiliary norm without a natural inner witness. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign15SignedAux
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticPellHalfIndex
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem absdiff_signed_square (f c T r : V) :
    ι (absdiff (f*f*c*T) (f*f*r+c)) * ι (absdiff (f*f*c*T) (f*f*r+c)) =
      (ι f*ι f*(ι c*ι T-ι r)-ι c) * (ι f*ι f*(ι c*ι T-ι r)-ι c) := by
  rw [Sign33AbsDiffSquare.absdiff_sq]
  simp only [map_add, map_mul]
  ring

theorem auxiliary_norm_of_signed (f c T r S y : V)
    (hNa : ι y*ι y - (ι S*ι S)*((ι y*ι y) -
      (ι f*ι f*(ι c*ι T-ι r)-ι c)*(ι f*ι f*(ι c*ι T-ι r)-ι c)) - 1 = 0) :
    S*S*(absdiff (f*f*c*T) (f*f*r+c))*(absdiff (f*f*c*T) (f*f*r+c)) + y*y =
      1 + S*S*y*y := by
  have hs := absdiff_signed_square f c T r
  apply ι_injective
  simp only [map_add, map_mul, map_one]
  have hdiff : (ι S*ι S) *
      (ι (absdiff (f*f*c*T) (f*f*r+c)) * ι (absdiff (f*f*c*T) (f*f*r+c)) -
        (ι f*ι f*(ι c*ι T-ι r)-ι c)*(ι f*ι f*(ι c*ι T-ι r)-ι c)) = 0 := by
    rw [hs, _root_.sub_self, mul_zero]
  apply sub_eq_zero.mp
  calc
    _ = (ι y*ι y - (ι S*ι S)*((ι y*ι y) -
          (ι f*ι f*(ι c*ι T-ι r)-ι c)*(ι f*ι f*(ι c*ι T-ι r)-ι c)) - 1) +
        (ι S*ι S) *
          (ι (absdiff (f*f*c*T) (f*f*r+c)) * ι (absdiff (f*f*c*T) (f*f*r+c)) -
            (ι f*ι f*(ι c*ι T-ι r)-ι c)*(ι f*ι f*(ι c*ι T-ι r)-ι c)) := by ring
    _ = 0 := by rw [hNa, hdiff]; simp
end DiophantineConsistency.Sign15SignedAux
#print axioms DiophantineConsistency.Sign15SignedAux.absdiff_signed_square
#print axioms DiophantineConsistency.Sign15SignedAux.auxiliary_norm_of_signed
