module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateFormulaValidity
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
theorem formulaValue_neg {s : Nat} (p : Formula s) {n P b f : V}
    (hP : IsSemiformula L 1 P) (h : EnvironmentsValid (s:V) n b f)
    (hf : ∀i,p.FVar? i→(i:V)<len f) :
    formulaValue p.neg P b f=neg L (formulaValue p P b f) := by
  induction p generalizing n b f with
  | verum => simp [FFL.FirstOrder.Semiformula.neg,formulaValue]
  | falsum => simp [FFL.FirstOrder.Semiformula.neg,formulaValue]
  | rel r ts => rfl
  | nrel r ts =>
    have hf' : ∀j i,(ts j).FVar? i→(i:V)<len f := fun j i hi => hf i (by simpa using Exists.intro j hi)
    exact (atomValue_isSemiformula r ts hP h hf').isUFormula.neg_neg.symm
  | and p q ihp ihq =>
    have hp : ∀i,p.FVar? i→(i:V)<len f := fun i hi => hf i ((FFL.FirstOrder.Semiformula.fvar?_and i p q).mpr (Or.inl hi))
    have hq : ∀i,q.FVar? i→(i:V)<len f := fun i hi => hf i ((FFL.FirstOrder.Semiformula.fvar?_and i p q).mpr (Or.inr hi))
    simp only [FFL.FirstOrder.Semiformula.neg,formulaValue]
    rw [neg_and (formulaValue_isSemiformula p hP h hp).isUFormula
      (formulaValue_isSemiformula q hP h hq).isUFormula,ihp h hp,ihq h hq]
  | or p q ihp ihq =>
    have hp : ∀i,p.FVar? i→(i:V)<len f := fun i hi => hf i ((FFL.FirstOrder.Semiformula.fvar?_or i p q).mpr (Or.inl hi))
    have hq : ∀i,q.FVar? i→(i:V)<len f := fun i hi => hf i ((FFL.FirstOrder.Semiformula.fvar?_or i p q).mpr (Or.inr hi))
    simp only [FFL.FirstOrder.Semiformula.neg,formulaValue]
    rw [neg_or (formulaValue_isSemiformula p hP h hp).isUFormula
      (formulaValue_isSemiformula q hP h hq).isUFormula,ihp h hp,ihq h hq]
  | @all src p ih =>
    have hb := bindEnvironments_valid h
    have hf' : ∀i,p.FVar? i→(i:V)<len (bindFree f) := by
      intro i hi; simpa [bindFree,NumericPAeqTerm.shiftTerms_length h.2] using hf i hi
    have hb' : EnvironmentsValid ((src+1:Nat):V) (n+1) (bindBound b) (bindFree f) := by
      simpa only [Nat.cast_add,Nat.cast_one] using hb
    simp only [FFL.FirstOrder.Semiformula.neg,formulaValue]
    rw [neg_all (formulaValue_isSemiformula p hP hb' hf').isUFormula,
      ih hb' hf']
  | @exs src p ih =>
    have hb := bindEnvironments_valid h
    have hf' : ∀i,p.FVar? i→(i:V)<len (bindFree f) := by
      intro i hi; simpa [bindFree,NumericPAeqTerm.shiftTerms_length h.2] using hf i hi
    have hb' : EnvironmentsValid ((src+1:Nat):V) (n+1) (bindBound b) (bindFree f) := by
      simpa only [Nat.cast_add,Nat.cast_one] using hb
    simp only [FFL.FirstOrder.Semiformula.neg,formulaValue]
    rw [neg_ex (formulaValue_isSemiformula p hP hb' hf').isUFormula,
      ih hb' hf']
#print axioms formulaValue_neg
end M6.PA.RelationalPredicateTemplate
