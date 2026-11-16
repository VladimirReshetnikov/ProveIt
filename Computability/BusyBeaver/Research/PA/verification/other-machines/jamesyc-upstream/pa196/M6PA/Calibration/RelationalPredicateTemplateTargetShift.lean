module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateTargetShiftBinders
public import M6PA.Calibration.RelationalPredicateTemplateFormulaValidity
@[expose] public section
/-! Eigenvariable/free-variable shift also shifts the unary predicate's free
parameters. A fixed-P naturality statement would in general be false. -/
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm (targetShiftTerms)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
theorem formulaValue_targetShift {s : Nat} (p : Formula s) {n P b f : V}
    (hP : IsSemiformula L 1 P) (h : EnvironmentsValid (s:V) n b f)
    (hf : ∀i,p.FVar? i→(i:V)<len f) :
    shift L (formulaValue p P b f)=
      formulaValue p (shift L P) (targetShiftTerms b) (targetShiftTerms f) := by
  induction p generalizing n b f with
  | verum => simp [formulaValue]
  | falsum => simp [formulaValue]
  | rel r ts =>
    exact atomValue_targetShift r ts hP h (fun j i hi => hf i (by simpa using Exists.intro j hi))
  | nrel r ts =>
    have hf' : ∀j i,(ts j).FVar? i→(i:V)<len f := fun j i hi => hf i (by simpa using Exists.intro j hi)
    simp only [formulaValue]
    rw [shift_neg (atomValue_isSemiformula r ts hP h hf'),
      atomValue_targetShift r ts hP h hf']
  | and p q ihp ihq =>
    have hp : ∀i,p.FVar? i→(i:V)<len f := fun i hi => hf i ((FFL.FirstOrder.Semiformula.fvar?_and i p q).mpr (Or.inl hi))
    have hq : ∀i,q.FVar? i→(i:V)<len f := fun i hi => hf i ((FFL.FirstOrder.Semiformula.fvar?_and i p q).mpr (Or.inr hi))
    simp only [formulaValue]
    rw [shift_and (formulaValue_isSemiformula p hP h hp).isUFormula
      (formulaValue_isSemiformula q hP h hq).isUFormula,ihp h hp,ihq h hq]
  | or p q ihp ihq =>
    have hp : ∀i,p.FVar? i→(i:V)<len f := fun i hi => hf i ((FFL.FirstOrder.Semiformula.fvar?_or i p q).mpr (Or.inl hi))
    have hq : ∀i,q.FVar? i→(i:V)<len f := fun i hi => hf i ((FFL.FirstOrder.Semiformula.fvar?_or i p q).mpr (Or.inr hi))
    simp only [formulaValue]
    rw [shift_or (formulaValue_isSemiformula p hP h hp).isUFormula
      (formulaValue_isSemiformula q hP h hq).isUFormula,ihp h hp,ihq h hq]
  | @all src p ih =>
    have hb := bindEnvironments_valid h
    have hf' : ∀i,p.FVar? i→(i:V)<len (bindFree f) := by
      intro i hi; simpa [bindFree,NumericPAeqTerm.shiftTerms_length h.2] using hf i hi
    have hb' : EnvironmentsValid ((src+1:Nat):V) (n+1) (bindBound b) (bindFree f) := by
      simpa only [Nat.cast_add,Nat.cast_one] using hb
    simp only [formulaValue]
    rw [shift_all (formulaValue_isSemiformula p hP hb' hf').isUFormula,
      ih hb' hf',bindBound_targetShift h.1,bindFree_targetShift h.2]
  | @exs src p ih =>
    have hb := bindEnvironments_valid h
    have hf' : ∀i,p.FVar? i→(i:V)<len (bindFree f) := by
      intro i hi; simpa [bindFree,NumericPAeqTerm.shiftTerms_length h.2] using hf i hi
    have hb' : EnvironmentsValid ((src+1:Nat):V) (n+1) (bindBound b) (bindFree f) := by
      simpa only [Nat.cast_add,Nat.cast_one] using hb
    simp only [formulaValue]
    rw [shift_exs (formulaValue_isSemiformula p hP hb' hf').isUFormula,
      ih hb' hf',bindBound_targetShift h.1,bindFree_targetShift h.2]
#print axioms formulaValue_targetShift
end M6.PA.RelationalPredicateTemplate

