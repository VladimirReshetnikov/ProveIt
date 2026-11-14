import PA194QVecHistory
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PA194QVecBasis
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem qvec_basis (s n : V)
    (hzero : znth s 0 = ?[^&0])
    (hrec : ∀ i < n, znth s (i+1) = qVec ℒₒᵣ (znth s i)) :
    ∀ i ≤ n, IsSemitermVec ℒₒᵣ (i+1) i (znth s i) ∧
      (∀ j < i, (znth s i).[j] = ^#j) ∧ (znth s i).[i] = ^&0 := by
  have hd : 𝚺₁-Predicate (fun i : V => i ≤ n → IsSemitermVec ℒₒᵣ (i+1) i (znth s i) ∧
      (∀ j < i, (znth s i).[j] = ^#j) ∧ (znth s i).[i] = ^&0) := by definability
  intro i
  induction i using ISigma1.sigma1_succ_induction
  · exact hd
  case zero =>
    intro _
    rw [hzero]
    simp
  case succ i ih =>
    intro hi
    have hin : i < n := succ_le_iff_lt.mp hi
    obtain ⟨hv,hentries,hlast⟩ := ih (le_of_lt hin)
    rw [hrec i hin]
    refine ⟨hv.qVec, ?_, ?_⟩
    · intro j hj
      rcases zero_or_succ j with (rfl | ⟨j,rfl⟩)
      · simp [qVec]
      · have hji : j < i := (add_lt_add_iff_right 1).mp hj
        simp only [qVec,nth_adjoin_succ,hv.lh]
        rw [nth_termBShiftVec (i := j) hv.isUTerm (lt_trans hji (lt_add_one i)), hentries j hji, termBShift_bvar]
    · simp only [qVec,nth_adjoin_succ,hv.lh]
      rw [nth_termBShiftVec (i := i) hv.isUTerm (lt_add_one i), hlast, termBShift_fvar]
#print axioms qvec_basis
end PA194QVecBasis
