import DiophantineConsistency.ArithmeticPellFirstIndex
import DiophantineConsistency.ModelDifferenceRing

/-! The strong norm implies f ≥ 2, with all original hypotheses. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33StrongF
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellFirstIndex
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem strong_norm_f_ge_two (a c f i : V)
    (hc : 0<c) (hf : 0<f) (hi : 0<i)
    (hstrict : f*f=1+delta a*(i*c*c)*(i*c*c)) : 2≤f := by
  have hd : 0<delta a := by
    unfold delta
    exact mul_pos (by simp) (by simp)
  have hI : 0<i*c*c := mul_pos (mul_pos hi hc) hc
  have hp : 0<delta a*(i*c*c)*(i*c*c) := mul_pos (mul_pos hd hI) hI
  have hfprod : 1<f*f := by rw [hstrict]; exact lt_add_of_pos_right 1 hp
  have hone : 1≤f := pos_iff_one_le.mp hf
  have hgt : 1<f := by
    by_contra hn
    have he : f=1 := le_antisymm (le_of_not_gt hn) hone
    rw [he] at hfprod
    simpa using hfprod
  simpa only [one_add_one_eq_two] using lt_iff_succ_le.mp hgt

end DiophantineConsistency.Sign33StrongF
#print axioms DiophantineConsistency.Sign33StrongF.strong_norm_f_ge_two
