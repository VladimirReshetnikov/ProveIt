import Absorb88Conditional

/-! Draft: necessary lower bounds on the checked normalization guard. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace Absorb88GuardObstruction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem guard_requires_large_inputs (b D F alpha j u Fnew anew t : V)
    (hF : 0<Fnew) (ha : 0<anew) (ht : 0<t)
    (hFsplit : F=Fnew+b*j) (hasplit : alpha=anew+b*b*j)
    (htsplit : D*j=u+t) :
    1+b≤F ∧ 1+b*b≤alpha := by
  have hDj : 0<D*j := by rw [htsplit]; exact add_pos_of_nonneg_of_pos (by simp) ht
  have hj : 0<j := pos_of_mul_pos_right hDj (by simp)
  have hj1 : 1≤j := pos_iff_one_le.mp hj
  have hf1 : 1≤Fnew := pos_iff_one_le.mp hF
  have ha1 : 1≤anew := pos_iff_one_le.mp ha
  constructor
  · rw [hFsplit]
    exact add_le_add hf1 (le_mul_of_one_le_right (by simp) hj1)
  · rw [hasplit]
    exact add_le_add ha1 (le_mul_of_one_le_right (by simp) hj1)

#print axioms Absorb88GuardObstruction.guard_requires_large_inputs
end Absorb88GuardObstruction
