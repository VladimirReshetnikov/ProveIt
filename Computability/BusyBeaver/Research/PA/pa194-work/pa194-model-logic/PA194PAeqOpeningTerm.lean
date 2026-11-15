import PA194PAeqOpeningQVec
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.OpeningQVec
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqBind
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def openingTerm (s k t : M) : M :=
  termSubst PA194PAeq.language (znth s k) (termShift PA194PAeq.language t)
def TermOpeningInverse (limit s t : M) : Prop := ∀ k ≤ limit,
  IsSemiterm PA194PAeq.language k t → openingTerm s k (bindTerm k t) = t

theorem termOpeningInverse_definable (limit s : M) : 𝚷₁-Predicate (TermOpeningInverse limit s) := by
  haveI : 𝚺₁-Function₂ (bindTerm : M → M → M) := bindTerm_defined.to_definable
  unfold TermOpeningInverse openingTerm
  definability

theorem opening_bindTerm (limit s : M)
    (h : (sourceQVecConstruction (M := M)).CSeq ![(?[ ^&(0 : M)] : M)] s)
    (hl : limit + 1 = lh s) {t : M} (ht : IsUTerm PA194PAeq.language t) :
    TermOpeningInverse limit s t := by
  apply IsUTerm.induction 𝚷 (termOpeningInverse_definable limit s) ?_ ?_ ?_ t ht
  · intro i k hk hs
    have hi : i < k := by simpa using hs
    have he := sourceQVec_trace_entries limit s h hl k hk
    simp [openingTerm, he.1 i hi]
  · intro i k hk hs
    have he := sourceQVec_trace_entries limit s h hl k hk
    rcases zero_or_succ i with rfl | ⟨j,rfl⟩
    · simp [openingTerm,bindFree,he.2]
    · simp [openingTerm,bindFree]
  · intro ar f v hf hv ih k hk hs
    have hsv := ((IsSemiterm.func).mp hs).2
    have hvb := bindTermVec_uterm (k := k) hv
    rw [bindTerm_func hf hv]
    unfold openingTerm
    rw [termShift_func hf hvb,termSubst_func hf hvb.termShiftVec]
    congr 1
    apply nth_ext' ar (by simp [hvb]) hv.lh.symm
    intro i hi
    rw [nth_termSubstVec hvb.termShiftVec hi,nth_termShiftVec hvb hi,bindTermVec_nth hv hi]
    exact ih i hi k hk (hsv.nth hi)
#print axioms opening_bindTerm
end PA194PAeq.OpeningQVec
