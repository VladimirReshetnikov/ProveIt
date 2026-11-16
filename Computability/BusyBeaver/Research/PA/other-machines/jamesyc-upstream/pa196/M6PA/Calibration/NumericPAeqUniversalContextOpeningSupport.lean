module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaFreeSupportSubstitution
@[expose] public section
namespace M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => Presentation.language
namespace NumericPAeqTerm
 theorem freeBound_shift_le {t:V} (ht:IsUTerm L t):freeBound (termShift L t)≤freeBound t+1 := by
  apply IsUTerm.induction 𝚺 (P:=fun t:V=>freeBound (termShift L t)≤freeBound t+1) ?_ ?_ ?_ ?_ t ht
  · definability
  · intro i; simp
  · intro i; simp
  · intro k r ts hr ht ih
    rw [termShift_func hr ht,freeBound_func hr ht.termShiftVec,freeBound_func hr ht]
    apply listMaxss_le_iff.mpr
    intro i hi
    have hi':i<k := by simpa [ht] using hi
    rw [freeBoundVec_nth ht.termShiftVec hi',nth_termShiftVec ht hi']
    exact le_trans (ih i hi') (add_le_add_left (by
      simpa only [freeBoundVec_nth ht hi'] using
        nth_le_listMax (show i<len (freeBoundVec k ts) by simpa [ht] using hi')) 1)
 theorem freeSupported_shift {l t:V} (h:FreeSupported l t):FreeSupported (l+1) (termShift L t) :=
  ⟨h.1.termShift,le_trans (freeBound_shift_le h.1) (add_le_add_left h.2 1)⟩
end NumericPAeqTerm
namespace NumericPAeqFormula
 theorem shifted_vector_bound {k ts:V} (ht:IsUTermVec L k ts):
    listMax (NumericPAeqTerm.freeBoundVec k (termShiftVec L k ts))≤listMax (NumericPAeqTerm.freeBoundVec k ts)+1 := by
  apply listMaxss_le_iff.mpr
  intro i hi
  have hi':i<k := by simpa [ht] using hi
  rw [NumericPAeqTerm.freeBoundVec_nth ht.termShiftVec hi',nth_termShiftVec ht hi']
  exact le_trans (NumericPAeqTerm.freeBound_shift_le (ht.nth hi')) (add_le_add_left (by
    simpa only [NumericPAeqTerm.freeBoundVec_nth ht hi'] using
      nth_le_listMax (show i<len (NumericPAeqTerm.freeBoundVec k ts) by simpa [ht] using hi')) 1)
 theorem freeBound_shift_le {p:V} (hp:IsUFormula L p):freeBound (shift L p)≤freeBound p+1 := by
  apply IsSemiformula.induction1 𝚺 (P:=fun (_ p:V)=>freeBound (shift L p)≤freeBound p+1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp.isSemiformula
  · definability
  · intro n k r ts hr ht
    simpa [shift_rel hr ht.isUTerm,freeBound_rel hr ht.isUTerm,freeBound_rel hr ht.isUTerm.termShiftVec] using shifted_vector_bound ht.isUTerm
  · intro n k r ts hr ht
    simpa [shift_nrel hr ht.isUTerm,freeBound_nrel hr ht.isUTerm,freeBound_nrel hr ht.isUTerm.termShiftVec] using shifted_vector_bound ht.isUTerm
  · intro n; simp
  · intro n; simp
  · intro n p q hp hq ihp ihq
    simp only [shift_and hp.isUFormula hq.isUFormula,freeBound_and hp.isUFormula hq.isUFormula,freeBound_and hp.isUFormula.shift hq.isUFormula.shift]
    exact max_le (le_trans ihp (add_le_add_left (le_max_left (freeBound p) (freeBound q)) 1)) (le_trans ihq (add_le_add_left (le_max_right (freeBound p) (freeBound q)) 1))
  · intro n p q hp hq ihp ihq
    simp only [shift_or hp.isUFormula hq.isUFormula,freeBound_or hp.isUFormula hq.isUFormula,freeBound_or hp.isUFormula.shift hq.isUFormula.shift]
    exact max_le (le_trans ihp (add_le_add_left (le_max_left (freeBound p) (freeBound q)) 1)) (le_trans ihq (add_le_add_left (le_max_right (freeBound p) (freeBound q)) 1))
  · intro n p hp ih; simpa [shift_all hp.isUFormula,freeBound_all hp.isUFormula,freeBound_all hp.isUFormula.shift] using ih
  · intro n p hp ih; simpa [shift_exs hp.isUFormula,freeBound_ex hp.isUFormula,freeBound_ex hp.isUFormula.shift] using ih
 theorem freeSupported_shift {l p:V} (h:FreeSupported l p):FreeSupported (l+1) (shift L p) :=
  ⟨h.1.shift,le_trans (freeBound_shift_le h.1) (add_le_add_left h.2 1)⟩
 theorem freeSupported_free {l p:V} (hp:IsSemiformula L 1 p) (h:FreeSupported l p):FreeSupported (l+1) (free L p) := by
  apply freeSupported_subst hp.shift (show IsSemitermVec L 1 0 (qqFvar 0∷(0:V)) by simp) (freeSupported_shift h)
  intro i hi
  have :i=0 := by simpa using hi
  subst i
  simp [NumericPAeqTerm.freeSupported_fvar]
#print axioms freeBound_shift_le
#print axioms freeSupported_shift
#print axioms freeSupported_free
end NumericPAeqFormula
end M6.PA

