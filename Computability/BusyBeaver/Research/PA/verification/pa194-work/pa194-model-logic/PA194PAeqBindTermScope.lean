import PA194PAeqBindTerm
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
def TermBindScope (t : V) : Prop := ∀ k n, k ≤ n → IsSemiterm PA194PAeq.language n t →
  IsSemiterm PA194PAeq.language (n+1) (bindTerm k t)
theorem TermBindScope_definable : 𝚷₁-Predicate (TermBindScope : V → Prop) := by
  haveI : 𝚺₁-Function₂ (bindTerm : V → V → V) := bindTerm_defined.to_definable
  unfold TermBindScope
  definability

theorem bindTerm_scope {t : V} (ht : IsUTerm PA194PAeq.language t) : TermBindScope t := by
  apply IsUTerm.induction 𝚷 TermBindScope_definable ?_ ?_ ?_ t ht
  · intro i k n hk hs
    have hi : i<n := by simpa using hs
    simp only [bindTerm_bvar,IsSemiterm.bvar]
    exact lt_trans hi (lt_add_one n)
  · intro i k n hk hs
    rw [bindTerm_fvar]
    by_cases h : i=0
    · simp only [bindFree,h,if_true,IsSemiterm.bvar]
      exact lt_of_le_of_lt hk (lt_add_one n)
    · simp [bindFree,h]
  · intro ar f v hf hv ih k n hk hs
    have hsv := ((IsSemiterm.func).mp hs).2
    have hlen : ar = len (bindTermVec k ar v) := by
      simpa [bindTermVec] using (termConstruction.resultVec_lh PA194PAeq.language ![k] hv).symm
    have hc : ∀ i < ar, IsSemiterm PA194PAeq.language (n+1) (nth (bindTermVec k ar v) i) := by
      intro i hi
      rw [bindTermVec_nth hv hi]
      exact ih i hi k n hk (hsv.nth hi)
    have hvout : IsSemitermVec PA194PAeq.language ar (n+1) (bindTermVec k ar v) := by
      constructor
      · exact ⟨hlen,fun i hi => (hc i hi).isUTerm⟩
      · intro i hi
        exact (hc i hi).bv
    rw [bindTerm_func hf hv]
    exact IsSemiterm.func.mpr ⟨hf,hvout⟩
#print axioms TermBindScope_definable
#print axioms bindTerm_scope
end generic
end PA194PAeqBind
