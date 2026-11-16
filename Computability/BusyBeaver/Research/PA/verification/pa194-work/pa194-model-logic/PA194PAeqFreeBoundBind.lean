import PA194PAeqFreeBoundTerm
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem listMax_pred {a b : V} (hlen : len a = len b)
    (h : ∀ i < len a, nth b i = nth a i - 1) : listMax b = listMax a - 1 := by
  apply le_antisymm
  · apply listMaxss_le
    intro i hi
    have hi' : i < len a := by simpa [hlen] using hi
    rw [h i hi']
    exact tsub_le_tsub_right (nth_le_listMax hi') 1
  · apply tsub_le_iff_right.mpr
    apply listMaxss_le
    intro i hi
    have hi' : i < len b := by simpa [hlen] using hi
    have hb := nth_le_listMax hi'
    rw [h i hi] at hb
    exact tsub_le_iff_right.mp hb

theorem bindTerm_uterm {k t : V} (ht : IsUTerm PA194PAeq.language t) :
    IsUTerm PA194PAeq.language (bindTerm k t) := by
  let n := max k (termBV PA194PAeq.language t)
  have hs : IsSemiterm PA194PAeq.language n t := ⟨ht,le_max_right _ _⟩
  exact (bindTerm_scope ht k n (le_max_left _ _) hs).isUTerm

def TermFreeBind (t : V) : Prop := ∀ k, termFreeBound (bindTerm k t) = termFreeBound t - 1
theorem TermFreeBind_definable : 𝚷₁-Predicate (TermFreeBind : V → Prop) := by
  haveI : 𝚺₁-Function₂ (bindTerm : V → V → V) := bindTerm_defined.to_definable
  haveI : 𝚺₁-Function₁ (termFreeBound : V → V) := termFreeBound_defined.to_definable
  unfold TermFreeBind
  definability

theorem termFreeBound_bind {t : V} (ht : IsUTerm PA194PAeq.language t) : TermFreeBind t := by
  apply IsUTerm.induction 𝚷 TermFreeBind_definable ?_ ?_ ?_ t ht
  · intro i k
    simp
  · intro i k
    rcases zero_or_succ i with rfl | ⟨j,rfl⟩
    · simp [bindFree]
    · simp [bindFree]
  · intro ar f v hf hv ih k
    have hlen : ar = len (bindTermVec k ar v) := by
      simpa [bindTermVec] using (termConstruction.resultVec_lh PA194PAeq.language ![k] hv).symm
    have hvb : IsUTermVec PA194PAeq.language ar (bindTermVec k ar v) := by
      refine ⟨hlen,?_⟩
      intro i hi
      rw [bindTermVec_nth hv hi]
      exact bindTerm_uterm (hv.2 i hi)
    rw [bindTerm_func hf hv,termFreeBound_func hf hvb,termFreeBound_func hf hv]
    apply listMax_pred
    · simp [termFreeBoundVec_len hv,termFreeBoundVec_len hvb]
    · intro i hi
      have hi' : i < ar := by simpa [termFreeBoundVec_len hv] using hi
      rw [termFreeBoundVec_nth hvb hi',bindTermVec_nth hv hi',termFreeBoundVec_nth hv hi']
      exact ih i hi' k
#print axioms listMax_pred
#print axioms bindTerm_uterm
#print axioms termFreeBound_bind
end generic
end PA194PAeqBind
