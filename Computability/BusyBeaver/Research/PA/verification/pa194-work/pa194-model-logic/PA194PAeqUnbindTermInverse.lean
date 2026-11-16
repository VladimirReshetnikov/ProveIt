import PA194PAeqUnbindTerm
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
def TermBindInverse (t : V) : Prop := ∀ k, IsSemiterm PA194PAeq.language k t → unbindTerm k (bindTerm k t) = t
theorem TermBindInverse_definable : 𝚷₁-Predicate (TermBindInverse : V → Prop) := by
  haveI : 𝚺₁-Function₂ (bindTerm : V → V → V) := bindTerm_defined.to_definable
  haveI : 𝚺₁-Function₂ (unbindTerm : V → V → V) := unbindTerm_defined.to_definable
  unfold TermBindInverse
  definability
theorem unbindTerm_bind {t : V} (ht : IsUTerm PA194PAeq.language t) : TermBindInverse t := by
  apply IsUTerm.induction 𝚷 TermBindInverse_definable ?_ ?_ ?_ t ht
  · intro i k hk
    have hi : i<k := by simpa using hk
    simp [unbindBound,hi]
  · intro i k hk
    rcases zero_or_succ i with rfl | ⟨j,rfl⟩
    · simp [bindFree,unbindBound]
    · simp [bindFree]
  · intro ar f v hf hv ih k hs
    have hsv := ((IsSemiterm.func).mp hs).2
    have hvb := bindTermVec_uterm (k := k) hv
    rw [bindTerm_func hf hv,unbindTerm_func hf hvb]
    congr 1
    apply nth_ext' ar (by simpa [unbindTermVec] using (unbindTermConstruction.resultVec_lh PA194PAeq.language ![k] hvb)) hv.lh.symm
    intro i hi
    rw [unbindTermVec_nth hvb hi,bindTermVec_nth hv hi]
    exact ih i hi k (hsv.nth hi)
#print axioms unbindTerm_bind
end generic
end PA194PAeqBind
