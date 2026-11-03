import CompactAuxOrdinateOrder
import DiophantineConsistency.ArithmeticPellAuxiliarySeed

/-! The exact auxiliary seed hypotheses supply its natural order. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactSeedOrdinateOrder
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticPellRecurrence CompactAuxOrdinateOrder
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem seed_ordinate_ge (a R i w y : V) (hR : 0 < R) (hi : 0 < i) (hy : 0 < y)
    (hnorm : let c := ycoord R a
      let I := delta a*i*c*c
      I*I*w*w+y*y=1+I*I*y*y) : w≤y := by
  let c := ycoord R a
  let I := delta a*i*c*c
  have hc : 0 < c := lt_of_lt_of_le hR (time_le_y R a)
  have hd : 0 < delta a := by unfold delta; exact mul_pos (by simp) (by simp)
  have hI : 0 < I := mul_pos (mul_pos (mul_pos hd hi) hc) hc
  exact ordinate_ge I w y hI hy hnorm

#print axioms CompactSeedOrdinateOrder.seed_ordinate_ge
end CompactSeedOrdinateOrder
