module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateSubstitutionBinders
public import M6PA.Calibration.RelationalPredicateTemplateFormulaValidity
@[expose] public section
/-! Capture-aware target bound substitution through a finite host template. -/
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
theorem formulaValue_subst {s : Nat} (p : Formula s) {n m P b f w : V}
    (hP : IsSemiformula L 1 P) (h : EnvironmentsValid (s:V) n b f) (hw : IsSemitermVec L n m w)
    (hf : ∀i,p.FVar? i→(i:V)<len f) :
    subst L w (formulaValue p P b f)=
      formulaValue p P (substTerms w b) (substTerms w f) := by
  induction p generalizing n m b f w with
  | verum => simp [formulaValue]
  | falsum => simp [formulaValue]
  | rel r ts =>
    exact atomValue_subst r ts hP h hw (fun j i hi => hf i (by simpa using Exists.intro j hi))
  | nrel r ts =>
    have hf' : ∀j i,(ts j).FVar? i→(i:V)<len f := fun j i hi => hf i (by simpa using Exists.intro j hi)
    simp only [formulaValue]
    rw [substs_neg (atomValue_isSemiformula r ts hP h hf') hw,
      atomValue_subst r ts hP h hw hf']
  | and p q ihp ihq =>
    have hp : ∀i,p.FVar? i→(i:V)<len f := fun i hi => hf i ((FFL.FirstOrder.Semiformula.fvar?_and i p q).mpr (Or.inl hi))
    have hq : ∀i,q.FVar? i→(i:V)<len f := fun i hi => hf i ((FFL.FirstOrder.Semiformula.fvar?_and i p q).mpr (Or.inr hi))
    simp only [formulaValue]
    rw [substs_and (formulaValue_isSemiformula p hP h hp).isUFormula
      (formulaValue_isSemiformula q hP h hq).isUFormula,ihp h hw hp,ihq h hw hq]
  | or p q ihp ihq =>
    have hp : ∀i,p.FVar? i→(i:V)<len f := fun i hi => hf i ((FFL.FirstOrder.Semiformula.fvar?_or i p q).mpr (Or.inl hi))
    have hq : ∀i,q.FVar? i→(i:V)<len f := fun i hi => hf i ((FFL.FirstOrder.Semiformula.fvar?_or i p q).mpr (Or.inr hi))
    simp only [formulaValue]
    rw [substs_or (formulaValue_isSemiformula p hP h hp).isUFormula
      (formulaValue_isSemiformula q hP h hq).isUFormula,ihp h hw hp,ihq h hw hq]
  | @all src p ih =>
    have hb := bindEnvironments_valid h
    have hf' : ∀i,p.FVar? i→(i:V)<len (bindFree f) := by
      intro i hi; simpa [bindFree,NumericPAeqTerm.shiftTerms_length h.2] using hf i hi
    have hb' : EnvironmentsValid ((src+1:Nat):V) (n+1) (bindBound b) (bindFree f) := by
      simpa only [Nat.cast_add,Nat.cast_one] using hb
    simp only [formulaValue]
    rw [substs_all (formulaValue_isSemiformula p hP hb' hf').isUFormula,
      ih hb' hw.qVec hf',bindBound_subst h.1 hw,bindFree_subst h.2 hw]
  | @exs src p ih =>
    have hb := bindEnvironments_valid h
    have hf' : ∀i,p.FVar? i→(i:V)<len (bindFree f) := by
      intro i hi; simpa [bindFree,NumericPAeqTerm.shiftTerms_length h.2] using hf i hi
    have hb' : EnvironmentsValid ((src+1:Nat):V) (n+1) (bindBound b) (bindFree f) := by
      simpa only [Nat.cast_add,Nat.cast_one] using hb
    simp only [formulaValue]
    rw [substs_ex (formulaValue_isSemiformula p hP hb' hf').isUFormula,
      ih hb' hw.qVec hf',bindBound_subst h.1 hw,bindFree_subst h.2 hw]
#print axioms formulaValue_subst
end M6.PA.RelationalPredicateTemplate

