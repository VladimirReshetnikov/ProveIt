module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermClosedSupport
public import M6PA.Calibration.NumericPAeqFormulaFreeSupportLaws
public import M6PA.Calibration.FoundationPAeqCodeInductionBody
@[expose] public section
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => Presentation.language

theorem shifted_vector_freeBound_zero {k v:V} (hv:IsUTermVec L k v) (he:termShiftVec L k v=v):
    listMax (NumericPAeqTerm.freeBoundVec k v)=0 := by
  apply le_antisymm
  · apply listMaxss_le_iff.mpr
    intro i hi
    have hik:i<k := by simpa [hv] using hi
    rw [NumericPAeqTerm.freeBoundVec_nth hv hik]
    have htfix:termShift L (nth v i)=nth v i := by
      simpa only [nth_termShiftVec hv hik] using congrArg (fun x:V=>nth x i) he
    rw [NumericPAeqTerm.freeBound_eq_zero_of_shift_fixed (hv.nth hik) htfix]
  · simp

theorem freeBound_eq_zero_of_shift_fixed {p:V} (hp:IsUFormula L p) (he:shift L p=p):freeBound p=0 := by
  have hall : ∀n p:V,IsSemiformula L n p→shift L p=p→freeBound p=0 := by
    apply IsSemiformula.induction1 𝚺 (P:=fun (_ p:V)=>shift L p=p→freeBound p=0)
    · definability
    · intro n k r ts hr ht h
      have hv : termShiftVec L k ts=ts := by simpa [shift_rel hr ht.isUTerm] using h
      rw [freeBound_rel hr ht.isUTerm]
      exact shifted_vector_freeBound_zero ht.isUTerm hv
    · intro n k r ts hr ht h
      have hv : termShiftVec L k ts=ts := by simpa [shift_nrel hr ht.isUTerm] using h
      rw [freeBound_nrel hr ht.isUTerm]
      exact shifted_vector_freeBound_zero ht.isUTerm hv
    · intro n h; simp
    · intro n h; simp
    · intro n p q hp hq ihp ihq h
      have hh:shift L p=p ∧ shift L q=q := by simpa [shift_and hp.isUFormula hq.isUFormula] using h
      simp [freeBound_and hp.isUFormula hq.isUFormula,ihp hh.1,ihq hh.2]
    · intro n p q hp hq ihp ihq h
      have hh:shift L p=p ∧ shift L q=q := by simpa [shift_or hp.isUFormula hq.isUFormula] using h
      simp [freeBound_or hp.isUFormula hq.isUFormula,ihp hh.1,ihq hh.2]
    · intro n p hp ih h
      have hh:shift L p=p := by simpa [shift_all hp.isUFormula] using h
      simpa [freeBound_all hp.isUFormula] using ih hh
    · intro n p hp ih h
      have hh:shift L p=p := by simpa [shift_exs hp.isUFormula] using h
      simpa [freeBound_ex hp.isUFormula] using ih hh
  exact hall _ p hp.isSemiformula he

theorem freeSupported_zero_of_shift_fixed {p:V} (hp:IsUFormula L p) (he:shift L p=p):FreeSupported 0 p :=
  ⟨hp,by rw [freeBound_eq_zero_of_shift_fixed hp he]⟩

theorem freeSupported_imp_right {m p q:V} (h:FreeSupported m (imp L p q)):FreeSupported m q := by
  have hu : IsUFormula L (qqOr (neg L p) q) := h.1
  have hparts := IsUFormula.or.mp hu
  exact ((freeSupported_or hparts.1 hparts.2).mp h).2

theorem freeSupported_targetIndBody {m k:V} (h:FreeSupported m (FoundationPAeqCode.targetIndBody k)):
    FreeSupported m k := by
  have hc := freeSupported_imp_right (freeSupported_imp_right h)
  exact (freeSupported_all (IsUFormula.all.mp hc.1)).mp hc
#print axioms shifted_vector_freeBound_zero
#print axioms freeBound_eq_zero_of_shift_fixed
#print axioms freeSupported_zero_of_shift_fixed
#print axioms freeSupported_targetIndBody
end M6.PA.NumericPAeqFormula

