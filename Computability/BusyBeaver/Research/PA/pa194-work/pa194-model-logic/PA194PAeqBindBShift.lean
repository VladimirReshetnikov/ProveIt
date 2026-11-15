import PA194PAeqBindSubstTerm
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def TermBindBShift (t : V) : Prop := ∀ k : V, IsSemiterm PA194PAeq.language k t →
  bindTerm (k+1) (termBShift PA194PAeq.language t) = termBShift PA194PAeq.language (bindTerm k t)

theorem termBindBShift_definable : 𝚷₁-Predicate (TermBindBShift : V → Prop) := by
  haveI : 𝚺₁-Function₂ (bindTerm : V → V → V) := bindTerm_defined.to_definable
  unfold TermBindBShift
  definability

theorem termBindBShift {t : V} (ht : IsUTerm PA194PAeq.language t) : TermBindBShift t := by
  apply IsUTerm.induction 𝚷 termBindBShift_definable ?_ ?_ ?_ t ht
  · intro i k hs
    simp
  · intro i k hs
    rcases zero_or_succ i with rfl | ⟨j,rfl⟩
    · simp [bindFree]
    · simp [bindFree]
  · intro ar f ts hf hts ih k hs
    have hst := ((IsSemiterm.func).mp hs).2
    have hvb := bindTermVec_uterm (k := k) hts
    rw [termBShift_func hf hts,bindTerm_func hf hts.termBShiftVec,bindTerm_func hf hts,termBShift_func hf hvb]
    congr 1
    apply nth_ext' ar (by simpa [bindTermVec] using (termConstruction.resultVec_lh PA194PAeq.language ![k+1] hts.termBShiftVec)) (by simp [hvb])
    intro i hi
    rw [bindTermVec_nth hts.termBShiftVec hi,nth_termBShiftVec hts hi,
      nth_termBShiftVec hvb hi,bindTermVec_nth hts hi]
    exact ih i hi k (hst.nth hi)
#print axioms termBindBShift
end PA194PAeqBind
