import DiophantineConsistency.RotationIndexBounds
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace RotationCoverageBounded
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem quot_eq (q r : V) (hr : r<67) : (67*q+r)/67=q := by
  rw [show 67*q+r=q*67+r by ring, div_mul_add _ _ hr]

theorem coverage (n e k : V) (hk : k<n) (heL : e<67*n) :
    (∃ q r u, q<n ∧ r<67 ∧ 67*k=e+(67*q+r) ∧ 67*n=e+(67*q+r+67+u)) ∨
    (∃ u q r, q<n ∧ e=67*k+67+u ∧ 67*n-e+67*k=67*q+r ∧ r<67) ∨
    (∃ a t q r, 0<a ∧ a<67 ∧ q<n ∧ e=67*k+a ∧ 67*n=e+((67-a)+t) ∧
      67*n-e+67*k=67*q+r ∧ r<67) := by
  rcases RotationCoverage67.coverage n e k hk with ⟨q,r,u,hr,hk',hL⟩ | ⟨u,q,r,he,hi,hr⟩ | ⟨a,t,q,r,ha,he,hL,hi,hr⟩
  · have hs := RotationIndexBounds.no_wrap_source_lt n e k (67*q+r) hk hk'
    have hq := RotationIndexBounds.q_lt n (67*q+r) hs
    rw [quot_eq q r hr] at hq
    exact Or.inl ⟨q,r,u,hq,hr,hk',hL⟩
  · have hb : 67*k<e := by rw [he]; have : (0:V)<67+u := by norm_num; exact lt_add_of_pos_right _ this
    have hs := RotationIndexBounds.wrap_source_lt n e k heL hb
    have hq := RotationIndexBounds.q_lt n (67*n-e+67*k) hs
    rw [hi,quot_eq q r hr] at hq
    exact Or.inr (Or.inl ⟨u,q,r,hq,he,hi,hr⟩)
  · by_cases ha0 : 0<a
    · have hb : 67*k<e := by rw [he]; exact lt_add_of_pos_right _ ha0
      have hs := RotationIndexBounds.wrap_source_lt n e k heL hb
      have hq := RotationIndexBounds.q_lt n (67*n-e+67*k) hs
      rw [hi,quot_eq q r hr] at hq
      exact Or.inr (Or.inr ⟨a,t,q,r,ha0,ha,hq,he,hL,hi,hr⟩)
    · have haz : a=0 := by simpa only [not_lt, nonpos_iff_eq_zero] using ha0
      have hn : 0<n := lt_of_le_of_lt (by simp : (0:V)≤k) hk
      left
      refine ⟨0,0,t,hn,by norm_num,?_,?_⟩
      · simpa only [haz,add_zero,mul_zero] using he.symm
      · simpa only [haz,tsub_zero,mul_zero,zero_add] using hL
#print axioms RotationCoverageBounded.quot_eq
#print axioms RotationCoverageBounded.coverage
end RotationCoverageBounded
