module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaSourceFreeArity
@[expose] public section
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm (sourceFree sourceFreeVec)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def OpeningVector (s w : V) : Prop := ∀ i<s+1, nth w i=if i<s then qqBvar i else qqFvar 0

theorem openingVector_qVec {s w : V} (hw : OpeningVector s w)
    (hv : IsSemitermVec Presentation.language (s+1) s w) :
    OpeningVector (s+1) (qVec Presentation.language w) := by
  intro i hi
  rcases zero_or_succ i with rfl|⟨i,rfl⟩
  · simp [qVec]
  · have hh : i<s+1 := by simpa using hi
    simp only [qVec,nth_adjoin_succ]
    rw [nth_termBShiftVec (by simpa [hv.lh] using hv.isUTerm) (by simpa [hv.lh] using hh),hw i hh]
    by_cases h : i<s <;> simp [h]

theorem sourceFreeVec_eq_subst_shift {s k ts w : V}
    (ht : IsSemitermVec Presentation.language k (s+1) ts) (hw : OpeningVector s w) :
    sourceFreeVec s k ts=termSubstVec Presentation.language k w (termShiftVec Presentation.language k ts) := by
  apply nth_ext' k (NumericPAeqTerm.sourceFreeVec_length ht.isUTerm) (len_termSubstVec ht.termShiftVec.isUTerm)
  intro i hi
  rw [NumericPAeqTerm.sourceFreeVec_nth ht.isUTerm hi,nth_termSubstVec ht.termShiftVec.isUTerm hi,
    nth_termShiftVec ht.isUTerm hi,NumericPAeqTerm.sourceFree_eq_subst_shift (ht.nth hi) hw]

theorem formulaSourceFree_eq_subst_shift {s p w : V}
    (hp : IsSemiformula Presentation.language (s+1) p)
    (hv : IsSemitermVec Presentation.language (s+1) s w) (hw : OpeningVector s w) :
    formulaSourceFree s p=subst Presentation.language w (shift Presentation.language p) := by
  suffices ∀ {n p : V}, IsSemiformula Presentation.language n p → ∀ s w, n=s+1 →
      IsSemitermVec Presentation.language (s+1) s w → OpeningVector s w →
      formulaSourceFree s p=subst Presentation.language w (shift Presentation.language p) from this hp s w rfl hv hw
  intro n p h
  apply IsSemiformula.pi1_structural_induction (P:=fun n p => ∀s w,n=s+1 →
    IsSemitermVec Presentation.language (s+1) s w → OpeningVector s w →
      formulaSourceFree s p=subst Presentation.language w (shift Presentation.language p)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · simp only [OpeningVector, eq_ite_iff]; definability
  · intro n k r ts hr ht s w he hv hw
    subst n
    rw [formulaSourceFree_rel _ _ _ _ hr ht.isUTerm,shift_rel hr ht.isUTerm,
      substs_rel hr ht.termShiftVec.isUTerm,sourceFreeVec_eq_subst_shift ht hw]
  · intro n k r ts hr ht s w he hv hw
    subst n
    rw [formulaSourceFree_nrel _ _ _ _ hr ht.isUTerm,shift_nrel hr ht.isUTerm,
      substs_nrel hr ht.termShiftVec.isUTerm,sourceFreeVec_eq_subst_shift ht hw]
  · intro n s w he hv hw; simp
  · intro n s w he hv hw; simp
  · intro n p q hp hq ihp ihq s w he hv hw
    rw [formulaSourceFree_and _ _ _ hp.isUFormula hq.isUFormula,shift_and hp.isUFormula hq.isUFormula,
      substs_and hp.shift.isUFormula hq.shift.isUFormula,ihp s w he hv hw,ihq s w he hv hw]
  · intro n p q hp hq ihp ihq s w he hv hw
    rw [formulaSourceFree_or _ _ _ hp.isUFormula hq.isUFormula,shift_or hp.isUFormula hq.isUFormula,
      substs_or hp.shift.isUFormula hq.shift.isUFormula,ihp s w he hv hw,ihq s w he hv hw]
  · intro n p hp ih s w he hv hw
    rw [formulaSourceFree_all _ _ hp.isUFormula,shift_all hp.isUFormula,substs_all hp.shift.isUFormula,
      ih (s+1) (qVec Presentation.language w) (by rw [he]) hv.qVec (openingVector_qVec hw hv)]
  · intro n p hp ih s w he hv hw
    rw [formulaSourceFree_exs _ _ hp.isUFormula,shift_exs hp.isUFormula,substs_ex hp.shift.isUFormula,
      ih (s+1) (qVec Presentation.language w) (by rw [he]) hv.qVec (openingVector_qVec hw hv)]

theorem formulaSourceFree_zero_eq_free {p : V} (hp : IsSemiformula Presentation.language 1 p) :
    formulaSourceFree 0 p=free Presentation.language p := by
  unfold free substs1
  apply formulaSourceFree_eq_subst_shift (by simpa using hp) (by simp)
  intro i hi
  have he : i=0 := by simpa using hi
  subst i; simp

#print axioms openingVector_qVec
#print axioms sourceFreeVec_eq_subst_shift
#print axioms formulaSourceFree_eq_subst_shift
#print axioms formulaSourceFree_zero_eq_free
end M6.PA.NumericPAeqFormula

