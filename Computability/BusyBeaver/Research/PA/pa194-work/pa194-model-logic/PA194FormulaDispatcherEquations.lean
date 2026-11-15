import PA194FormulaDispatcher
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194FormulaDispatcher
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem translate_rel (param k r v : V) (hr : PA194PAeq.language.IsRel k r)
    (hv : IsUTermVec PA194PAeq.language k v) :
    translateFormula param (^rel k r v) = atomicEquality param (nth v 0) (nth v 1) := by
  simpa [translateFormula,formulaConstruction,atom] using (formulaConstruction (V := V)).result_rel (param := param) hr hv

theorem translate_nrel (param k r v : V) (hr : PA194PAeq.language.IsRel k r)
    (hv : IsUTermVec PA194PAeq.language k v) :
    translateFormula param (^nrel k r v) = neg SourceL (atomicEquality param (nth v 0) (nth v 1)) := by
  simpa [translateFormula,formulaConstruction,atom] using (formulaConstruction (V := V)).result_nrel (param := param) hr hv

theorem translate_verum (param : V) : translateFormula param ^⊤ = ^⊤ := by
  simpa [translateFormula,formulaConstruction] using (formulaConstruction (V := V)).result_verum (param := param) (L := PA194PAeq.language)
theorem translate_falsum (param : V) : translateFormula param ^⊥ = ^⊥ := by
  simpa [translateFormula,formulaConstruction] using (formulaConstruction (V := V)).result_falsum (param := param) (L := PA194PAeq.language)
theorem translate_and (param p q : V) (hp : IsUFormula PA194PAeq.language p)
    (hq : IsUFormula PA194PAeq.language q) :
    translateFormula param (p ^⋏ q) = translateFormula param p ^⋏ translateFormula param q := by
  simpa [translateFormula,formulaConstruction] using (formulaConstruction (V := V)).result_and (param := param) hp hq
theorem translate_or (param p q : V) (hp : IsUFormula PA194PAeq.language p)
    (hq : IsUFormula PA194PAeq.language q) :
    translateFormula param (p ^⋎ q) = translateFormula param p ^⋎ translateFormula param q := by
  simpa [translateFormula,formulaConstruction] using (formulaConstruction (V := V)).result_or (param := param) hp hq
theorem translate_all (param p : V) (hp : IsUFormula PA194PAeq.language p) :
    translateFormula param (^∀ p) = allOutput (translateFormula (formulaChildParameters param) p) := by
  simpa [translateFormula,formulaConstruction] using (formulaConstruction (V := V)).result_all (param := param) hp
theorem translate_exs (param p : V) (hp : IsUFormula PA194PAeq.language p) :
    translateFormula param (^∃ p) = exsOutput (translateFormula (formulaChildParameters param) p) := by
  simpa [translateFormula,formulaConstruction] using (formulaConstruction (V := V)).result_exs (param := param) hp
#print axioms translate_rel
#print axioms translate_nrel
#print axioms translate_verum
#print axioms translate_falsum
#print axioms translate_and
#print axioms translate_or
#print axioms translate_all
#print axioms translate_exs
end generic
end PA194FormulaDispatcher
