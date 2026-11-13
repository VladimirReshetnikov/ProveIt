module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateBinders
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm (targetShiftTerms)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language

theorem termValue_targetShift {s : Nat} (t : Term s) {n b f : V}
    (h : EnvironmentsValid (s:V) n b f) (hf : ∀i,t.FVar? i→(i:V)<len f) :
    termValue t (targetShiftTerms b) (targetShiftTerms f)=termShift L (termValue t b f) := by
  cases t with
  | bvar i => exact NumericPAeqTerm.targetShiftTerms_nth h.1 (by exact_mod_cast i.isLt)
  | fvar i => exact NumericPAeqTerm.targetShiftTerms_nth h.2 (hf i (by simp))
  | func fn _ => nomatch fn

theorem atomValue_targetShift {s k : Nat} (r : Relation k) (ts : Fin k → Term s)
    {n P b f : V} (hP : IsSemiformula L 1 P)
    (h : EnvironmentsValid (s:V) n b f) (hf : ∀j i,(ts j).FVar? i→(i:V)<len f) :
    shift L (atomValue r ts P b f)=
      atomValue r ts (shift L P) (targetShiftTerms b) (targetShiftTerms f) := by
  have ht j := termValue_isSemiterm (ts j) h (hf j)
  cases r with
  | eq =>
    simp only [atomValue]
    rw [shift_rel (by simp) (by simp [(ht 0).isUTerm,(ht 1).isUTerm]),
      termShiftVec_cons₂ (ht 0).isUTerm (ht 1).isUTerm,
      termValue_targetShift (ts 0) h (hf 0),termValue_targetShift (ts 1) h (hf 1)]
  | mem =>
    simp only [atomValue]
    rw [shift_rel (by simp) (by simp [(ht 0).isUTerm,(ht 1).isUTerm]),
      termShiftVec_cons₂ (ht 0).isUTerm (ht 1).isUTerm,
      termValue_targetShift (ts 0) h (hf 0),termValue_targetShift (ts 1) h (hf 1)]
  | predicate =>
    simp only [atomValue,substs1]
    rw [shift_substs hP (m:=n) (by simp [ht 0]),termShiftVec_cons₁ (ht 0).isUTerm,
      termValue_targetShift (ts 0) h (hf 0)]
#print axioms termValue_targetShift
#print axioms atomValue_targetShift
end M6.PA.RelationalPredicateTemplate

