import PA194PAeqShiftFreeBound
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def TermBindSubst (t : V) : Prop := ∀ n k v w : V,
  IsSemiterm PA194PAeq.language n t →
  IsSemitermVec PA194PAeq.language n k v →
  (∀ i < n, bindTerm k v.[i] = w.[i]) → termFreeBound t = 0 →
  bindTerm k (termSubst PA194PAeq.language v t) = termSubst PA194PAeq.language w t

theorem termBindSubst_definable : 𝚷₁-Predicate (TermBindSubst : V → Prop) := by
  haveI : 𝚺₁-Function₁ (termFreeBound : V → V) := termFreeBound_defined.to_definable
  haveI : 𝚺₁-Function₂ (bindTerm : V → V → V) := bindTerm_defined.to_definable
  unfold TermBindSubst
  definability

theorem termBindSubst {t : V} (ht : IsUTerm PA194PAeq.language t) : TermBindSubst t := by
  apply IsUTerm.induction 𝚷 termBindSubst_definable ?_ ?_ ?_ t ht
  · intro i n k v w hs hv hw hz
    have hi : i < n := by simpa using hs
    simpa using hw i hi
  · intro i n k v w hs hv hw hz
    simp at hz
  · intro ar f ts hf hts ih n k v w hs hv hw hz
    have hst := ((IsSemiterm.func).mp hs).2
    have hts' : IsUTermVec PA194PAeq.language ar (termSubstVec PA194PAeq.language ar v ts) :=
      (hv.termSubstVec hst).isUTerm
    have hbound : listMax (termFreeBoundVec ar ts) = 0 := by simpa [termFreeBound_func hf hts] using hz
    rw [termSubst_func hf hts,bindTerm_func hf hts',termSubst_func hf hts]
    congr 1
    apply nth_ext' ar (by simpa [bindTermVec] using (termConstruction.resultVec_lh PA194PAeq.language ![k] hts')) (by simp [hts])
    intro i hi
    rw [bindTermVec_nth hts' hi,nth_termSubstVec hts hi,nth_termSubstVec hts hi]
    apply ih i hi n k v w (hst.nth hi) hv hw
    apply le_antisymm _ zero_le
    have hle : (termFreeBoundVec ar ts).[i] ≤ listMax (termFreeBoundVec ar ts) :=
      nth_le_listMax (by simpa [termFreeBoundVec_len hts] using hi)
    simpa [termFreeBoundVec_nth hts hi,hbound] using hle
#print axioms termBindSubst
end PA194PAeqBind
