import DiophantineConsistency.RotationCoverage
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace RotationCoverage67
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem coverage (n e k : V) (hk : k<n) :
    (∃ q r u, r<67 ∧ 67*k=e+(67*q+r) ∧ 67*n=e+(67*q+r+67+u)) ∨
    (∃ u q r, e=67*k+67+u ∧ 67*n-e+67*k=67*q+r ∧ r<67) ∨
    (∃ a t q r, a<67 ∧ e=67*k+a ∧ 67*n=e+((67-a)+t) ∧
      67*n-e+67*k=67*q+r ∧ r<67) := by
  have hw : 67*k+67 ≤ 67*n := by
    have h := mul_le_mul_of_nonneg_left (lt_iff_succ_le.mp hk) (by norm_num : (0:V)≤67)
    simpa only [mul_add,mul_one] using h
  rcases RotationCoverage.coverage (67*n) e (67*k) 67 hw with ⟨s,u,hk',hL⟩ | ⟨u,he⟩ | ⟨a,t,ha,he,hL⟩
  · obtain ⟨q,r,hs,hr⟩ := RotationCoverage.digit_index s
    left
    exact ⟨q,r,u,hr,by simpa only [hs] using hk',by simpa only [hs] using hL⟩
  · obtain ⟨q,r,hi,hr⟩ := RotationCoverage.digit_index (67*n-e+67*k)
    exact Or.inr (Or.inl ⟨u,q,r,he,hi,hr⟩)
  · obtain ⟨q,r,hi,hr⟩ := RotationCoverage.digit_index (67*n-e+67*k)
    exact Or.inr (Or.inr ⟨a,t,q,r,ha,he,hL,hi,hr⟩)
#print axioms RotationCoverage67.coverage
end RotationCoverage67
