module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermSourceFreeOperation
@[expose] public section

namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem sourceFree_eq_subst_shift {s t w : V} (ht : IsSemiterm Presentation.language (s+1) t)
    (hw : ∀ i<s+1, nth w i=if i<s then qqBvar i else qqFvar 0) :
    sourceFree s t=termSubst Presentation.language w (termShift Presentation.language t) := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro i hi; simpa using (hw i hi).symm
  · intro i; simp
  · intro k f ts hf hv ih
    rw [sourceFree_func hf hv.isUTerm,termShift_func hf hv.isUTerm,termSubst_func hf hv.termShiftVec.isUTerm]
    congr 1
    apply nth_ext' k (sourceFreeVec_length hv.isUTerm) (len_termSubstVec hv.termShiftVec.isUTerm)
    intro i hi
    rw [sourceFreeVec_nth hv.isUTerm hi,nth_termSubstVec hv.termShiftVec.isUTerm hi,nth_termShiftVec hv.isUTerm hi,ih i hi]

theorem sourceFree_zero_eq_free {t : V} (ht : IsSemiterm Presentation.language 1 t) :
    sourceFree 0 t=termSubst Presentation.language (qqFvar 0 ∷ 0) (termShift Presentation.language t) := by
  apply sourceFree_eq_subst_shift (by simpa using ht)
  intro i hi
  have hz : i=0 := by simpa using hi
  subst i; simp

theorem sourceFree_zero_typed (t : Bootstrapping.Semiterm V Presentation.language 1) :
    sourceFree 0 t.val=t.free.val := sourceFree_zero_eq_free (by simpa using t.isSemiterm)

theorem sourceFree_bShift {s t : V} (ht : IsSemiterm Presentation.language (s+1) t) :
    sourceFree (s+1) (termBShift Presentation.language t)=termBShift Presentation.language (sourceFree s t) := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro i hi
    by_cases hh : i<s <;> simp [hh]
  · intro i; simp
  · intro k f ts hf hv ih
    have hs : IsSemitermVec Presentation.language k s (sourceFreeVec s k ts) :=
      IsSemitermVec.iff.mpr ⟨sourceFreeVec_length hv.isUTerm,fun i hi => by
        rw [sourceFreeVec_nth hv.isUTerm hi]; exact sourceFree_isSemiterm (hv.nth hi)⟩
    rw [termBShift_func hf hv.isUTerm,sourceFree_func hf hv.termBShiftVec.isUTerm,
      sourceFree_func hf hv.isUTerm,termBShift_func hf hs.isUTerm]
    congr 1
    apply nth_ext' k (sourceFreeVec_length hv.termBShiftVec.isUTerm) (len_termBShiftVec hs.isUTerm)
    intro i hi
    rw [sourceFreeVec_nth hv.termBShiftVec.isUTerm hi,nth_termBShiftVec hv.isUTerm hi,
      nth_termBShiftVec hs.isUTerm hi,sourceFreeVec_nth hv.isUTerm hi,ih i hi]

#print axioms sourceFree_eq_subst_shift
#print axioms sourceFree_zero_eq_free
#print axioms sourceFree_zero_typed
#print axioms sourceFree_bShift
end M6.PA.NumericPAeqTerm

