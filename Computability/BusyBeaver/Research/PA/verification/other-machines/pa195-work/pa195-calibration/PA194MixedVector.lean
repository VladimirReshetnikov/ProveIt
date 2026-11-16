import PA194QVecHistory
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace PA194MixedVector
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
@[irreducible] noncomputable def genericIter (k z : V) : V := PA194QVecHistory.openingConstruction.result ![z] k
noncomputable def mixedVec (k m : V) : V := genericIter k (fvarVec m)
@[simp] lemma mixed_zero (m : V) : mixedVec (0 : V) m = fvarVec m := by
  simp [mixedVec, genericIter, PA194QVecHistory.openingConstruction]
@[simp] lemma mixed_succ (k m : V) : mixedVec (k+1) m = qVec ℒₒᵣ (mixedVec k m) := by
  simp [mixedVec,genericIter,PA194QVecHistory.openingConstruction, PA194QVecHistory.opener]
instance mixedVec_definable : 𝚺₁-Function₂ (mixedVec (V := V)) := by
  haveI : 𝚺₁-Function₂ (genericIter (V := V)) := by
    unfold genericIter
    change 𝚺₁.DefinableFunction (fun v : Fin 2 → V => PA194QVecHistory.openingConstruction.result ![v 1] (v 0))
    convert PA194QVecHistory.openingConstruction.result_definable using 1
    funext v
    congr 1
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  unfold mixedVec
  definability
lemma fvarVec_wf (m : V) : IsSemitermVec ℒₒᵣ m 0 (fvarVec m) := by
  apply IsSemitermVec.iff.mpr
  refine ⟨len_fvarVec m,?_⟩
  intro i hi
  rw [nth_fvarVec m i hi]
  simp

theorem mixed_shape (k m : V) : IsSemitermVec ℒₒᵣ (k+m) k (mixedVec k m) ∧
    (∀ j < k, (mixedVec k m).[j] = ^#j) ∧
    (∀ j < m, (mixedVec k m).[k+j] = ^&j) := by
  have hd : 𝚺₁-Predicate (fun k : V => IsSemitermVec ℒₒᵣ (k+m) k (mixedVec k m) ∧
      (∀ j < k, (mixedVec k m).[j] = ^#j) ∧
      (∀ j < m, (mixedVec k m).[k+j] = ^&j)) := by definability
  induction k using ISigma1.sigma1_succ_induction
  · exact hd
  case zero =>
    refine ⟨?_,?_,?_⟩
    · simpa using fvarVec_wf m
    · intro j hj; exact False.elim (not_lt_zero hj)
    · intro j hj; simpa using nth_fvarVec m j hj
  case succ k ih =>
    obtain ⟨hv,hbound,hfree⟩ := ih
    refine ⟨?_,?_,?_⟩
    · simpa [add_assoc,add_comm,add_left_comm] using hv.qVec
    · intro j hj
      rcases zero_or_succ j with (rfl | ⟨j,rfl⟩)
      · simp [mixed_succ,qVec]
      · have hjk : j < k := (add_lt_add_iff_right 1).mp hj
        rw [mixed_succ]
        simp only [qVec,nth_adjoin_succ,hv.lh]
        rw [nth_termBShiftVec (i := j) hv.isUTerm (lt_of_lt_of_le hjk le_self_add), hbound j hjk,termBShift_bvar]
    · intro j hj
      have hjlen : k+j < k+m := by simpa [add_comm] using add_lt_add_left hj k
      rw [mixed_succ]
      have he : k+1+j = (k+j)+1 := by simp [add_assoc,add_comm,add_left_comm]
      rw [he]
      simp only [qVec,nth_adjoin_succ,hv.lh]
      rw [nth_termBShiftVec (i := k+j) hv.isUTerm hjlen, hfree j hj,termBShift_fvar]
#print axioms mixed_shape
end PA194MixedVector
