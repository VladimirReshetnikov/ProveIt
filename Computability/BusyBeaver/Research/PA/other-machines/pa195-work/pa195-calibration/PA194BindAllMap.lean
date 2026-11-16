import PA194BindAllTerm
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PA194BindAllMap
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
def GoodMap (d N w : V) : Prop := IsSemitermVec ℒₒᵣ (d+N) d w ∧
  (∀ z < d, w.[z] = ^#z) ∧ (∀ x < N, w.[d+x] = ^&x)
lemma goodMap_qVec (d N w : V) (h : GoodMap d N w) : GoodMap (d+1) N (qVec ℒₒᵣ w) := by
  obtain ⟨hw,hbound,hfree⟩ := h
  refine ⟨?_,?_,?_⟩
  · simpa [add_assoc,add_comm,add_left_comm] using hw.qVec
  · intro z hz
    rcases zero_or_succ z with (rfl | ⟨z,rfl⟩)
    · simp [qVec]
    · have hzd : z < d := (add_lt_add_iff_right 1).mp hz
      have hzlen : z < d+N := lt_of_lt_of_le hzd le_self_add
      simp only [qVec,nth_adjoin_succ,hw.lh]
      rw [nth_termBShiftVec (i := z) hw.isUTerm hzlen,hbound z hzd,termBShift_bvar]
  · intro x hx
    have hlen : d+x < d+N := by simpa [add_comm] using add_lt_add_left hx d
    have he : d+1+x = (d+x)+1 := by simp [add_assoc,add_comm,add_left_comm]
    rw [he]
    simp only [qVec,nth_adjoin_succ,hw.lh]
    rw [nth_termBShiftVec (i := d+x) hw.isUTerm hlen,hfree x hx,termBShift_fvar]
lemma goodMap_fvarVec (N : V) : GoodMap 0 N (fvarVec N) := by
  refine ⟨?_,?_,?_⟩
  · apply IsSemitermVec.iff.mpr
    refine ⟨by simpa using len_fvarVec N,?_⟩
    intro i hi
    have hiN : i<N := by simpa using hi
    rw [nth_fvarVec N i hiN]
    simp
  · intro z hz; exact False.elim (not_lt_zero hz)
  · intro x hx; simpa using nth_fvarVec N x hx
#print axioms goodMap_qVec
#print axioms goodMap_fvarVec
end PA194BindAllMap
