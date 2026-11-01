import DiophantineConsistency.ArithmeticAdaptiveQuotients2011
import DiophantineConsistency.ArithmeticSignedPairExpressions
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 3000000
noncomputable section
namespace DiophantineConsistency.AdaptiveZ46Orientation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveQuotients2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem magnitude_quotient (p n s tau : V) (hs : 0 < s)
    (h : magnitude (p,n) * magnitude (p,n) = s*s*(1+tau)) :
    ∃ t : V, 0 < magnitude (p,n) ∧ magnitude (p,n) = s*t := by
  obtain ⟨t,ht,_⟩ := scaled_quotient s (magnitude (p,n)) (1+tau) hs h
  refine ⟨t, ?_, ht⟩
  have hz : 0 < magnitude (p,n)*magnitude (p,n) := by
    rw [h]
    exact mul_pos (mul_pos hs hs) (by simpa only [add_comm] using (lt_of_le_of_lt (Arithmetic.zero_le tau) (lt_add_one tau)))
  exact pos_of_mul_pos_left hz (Arithmetic.zero_le _)

theorem orient (p n s t r : V) (h : magnitude (p,n)=s*t) :
    ∃ r' : V, r ≤ r' ∧
      Equivalent (plus (p,n) (natural (s*r'))) (natural (magnitude (p,n)+s*r)) := by
  by_cases hn : n ≤ p
  · refine ⟨r, le_refl _, ?_⟩
    have he : p = n + magnitude (p,n) := by
      have hsub : p-n+n=p := tsub_add_cancel_of_le hn
      have hm : magnitude (p,n)=p-n := by simp [magnitude, tsub_eq_zero_of_le hn]
      rw [hm]
      exact hsub.symm.trans (add_comm _ _)
    have he' : p = n+s*t := by rw [← h]; exact he
    change p+s*r+0 = n+0+(magnitude (p,n)+s*r)
    rw [h,he']
    ring
  · have hp : p ≤ n := le_of_not_ge hn
    refine ⟨r+(t+t), by simp, ?_⟩
    have he : n = p + magnitude (p,n) := by
      have hsub : n-p+p=n := tsub_add_cancel_of_le hp
      have hm : magnitude (p,n)=n-p := by simp [magnitude, tsub_eq_zero_of_le hp]
      rw [hm]
      exact hsub.symm.trans (add_comm _ _)
    have he' : n = p+s*t := by rw [← h]; exact he
    change p+s*(r+(t+t))+0 = n+0+(magnitude (p,n)+s*r)
    rw [h,he']
    ring
#print axioms magnitude_quotient
#print axioms orient
end DiophantineConsistency.AdaptiveZ46Orientation
