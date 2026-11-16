module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateFormula
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem formulaValue_isSemiformula {s : Nat} (p : Formula s) {n P b f : V}
    (hP : IsSemiformula RelationalSource.language 1 P)
    (h : EnvironmentsValid (s:V) n b f)
    (hf : ∀i,p.FVar? i→(i:V)<len f) :
    IsSemiformula RelationalSource.language n (formulaValue p P b f) := by
  induction p generalizing n b f with
  | verum => simp [formulaValue]
  | falsum => simp [formulaValue]
  | rel r ts =>
    exact atomValue_isSemiformula r ts hP h (fun j i hi => hf i (by simpa using Exists.intro j hi))
  | nrel r ts =>
    exact (atomValue_isSemiformula r ts hP h (fun j i hi => hf i (by simpa using Exists.intro j hi))).neg
  | and p q ihp ihq =>
    exact IsSemiformula.and.mpr ⟨ihp h (fun i hi => hf i ((FFL.FirstOrder.Semiformula.fvar?_and i p q).mpr (Or.inl hi))),ihq h (fun i hi => hf i ((FFL.FirstOrder.Semiformula.fvar?_and i p q).mpr (Or.inr hi)))⟩
  | or p q ihp ihq =>
    exact IsSemiformula.or.mpr ⟨ihp h (fun i hi => hf i ((FFL.FirstOrder.Semiformula.fvar?_or i p q).mpr (Or.inl hi))),ihq h (fun i hi => hf i ((FFL.FirstOrder.Semiformula.fvar?_or i p q).mpr (Or.inr hi)))⟩
  | all p ih =>
    apply IsSemiformula.all.mpr
    apply ih (by simpa only [Nat.cast_add,Nat.cast_one] using bindEnvironments_valid h)
    intro i hi
    simpa [bindFree,NumericPAeqTerm.shiftTerms_length h.2] using hf i hi
  | exs p ih =>
    apply IsSemiformula.exs.mpr
    apply ih (by simpa only [Nat.cast_add,Nat.cast_one] using bindEnvironments_valid h)
    intro i hi
    simpa [bindFree,NumericPAeqTerm.shiftTerms_length h.2] using hf i hi
#print axioms formulaValue_isSemiformula
end M6.PA.RelationalPredicateTemplate

