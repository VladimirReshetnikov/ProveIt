import DiophantineConsistency.ArithmeticAdaptiveConstructionStrong2011

/-! Positive auxiliary difference for the reverse adaptive witness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionAux2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A nontrivial ordinate in the maintained auxiliary norm is strictly larger
than its absolute-difference coordinate. No positivity of the multiplier is
needed. -/
theorem ordinate_gt_difference (I u y : V) (hy : 2≤y)
    (h : I*I*u*u+y*y=1+I*I*y*y) : u<y := by
  by_contra hn
  have hyu : y≤u := le_of_not_gt hn
  have hsq : y*y≤u*u := mul_le_mul hyu hyu (by simp) (by simp)
  have hm : I*I*(y*y)≤I*I*(u*u) := mul_le_mul_of_nonneg_left hsq (by simp)
  have hs : y*y+I*I*(y*y)≤1+I*I*(y*y) := calc
    _≤y*y+I*I*(u*u) := (add_le_add_iff_left _).mpr hm
    _=1+I*I*(y*y) := by simpa only [mul_assoc, add_comm] using h
  have hy2 : y*y≤1 := (add_le_add_iff_right _).mp hs
  have hfour : (4:V)≤y*y := by
    simpa only [show (2:V)*2=4 by norm_num] using mul_le_mul hy hy (by simp) (by simp)
  have : (4:V)≤1 := le_trans hfour hy2
  norm_num at this

/-- This positivity justifies choosing the adaptive coordinate `y-u`. -/
theorem positive_auxiliary_witness (I u y : V) (hy : 2≤y)
    (h : I*I*u*u+y*y=1+I*I*y*y) :
    0<y-u ∧ (y-u)+u=y := by
  have hlt := ordinate_gt_difference I u y hy h
  exact ⟨tsub_pos_iff_lt.mpr hlt, tsub_add_cancel_of_le (le_of_lt hlt)⟩
end DiophantineConsistency.ArithmeticAdaptiveConstructionAux2011
