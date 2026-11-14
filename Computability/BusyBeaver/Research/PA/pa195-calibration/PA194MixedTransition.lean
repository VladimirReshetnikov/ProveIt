import PA194MixedVector
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace PA194MixedTransition
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194MixedVector
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem mixed_transition (k m : V) :
    termSubstVec ℒₒᵣ (k+1+m) (mixedVec k 1)
      (termShiftVec ℒₒᵣ (k+1+m) (mixedVec (k+1) m)) = mixedVec k (m+1) := by
  obtain ⟨hv,hvb,hvf⟩ := mixed_shape (k+1) m
  obtain ⟨hw,hwb,hwf⟩ := mixed_shape k (1 : V)
  obtain ⟨hu,hub,huf⟩ := mixed_shape k (m+1)
  have hlen : k+1+m = k+(m+1) := by simp [add_assoc,add_comm,add_left_comm]
  apply nth_ext' (k+1+m)
  · exact len_termSubstVec hv.termShiftVec.isUTerm
  · simpa [hlen] using hu.lh
  intro t ht
  rw [nth_termSubstVec hv.termShiftVec.isUTerm ht,nth_termShiftVec hv.isUTerm ht]
  by_cases htk : t < k
  · rw [hvb t (lt_trans htk (lt_add_one k)),termShift_bvar,termSubst_bvar,hwb t htk,hub t htk]
  · by_cases hteq : t = k
    · subst t
      have hk : k < k+1 := lt_add_one k
      rw [hvb k hk,termShift_bvar,termSubst_bvar]
      simpa using (hwf 0 (by simp)).trans (huf 0 (by simp)).symm
    · have hklt : k < t := lt_of_le_of_ne (le_of_not_gt htk) (Ne.symm hteq)
      have hk1 : k+1 ≤ t := succ_le_iff_lt.mpr hklt
      let j := t-(k+1)
      have htval : t = (k+1)+j := by simpa [j] using (add_tsub_cancel_of_le hk1).symm
      have hj : j < m := by
        apply (add_lt_add_iff_left (k+1)).mp
        simpa [← htval] using ht
      rw [htval,hvf j hj,termShift_fvar,termSubst_fvar]
      have hj1 : j+1 < m+1 := by simpa [add_comm] using add_lt_add_right hj 1
      have heq : k+1+j = k+(j+1) := by simp [add_assoc,add_comm,add_left_comm]
      rw [heq,huf (j+1) hj1]
#print axioms mixed_transition
end PA194MixedTransition
