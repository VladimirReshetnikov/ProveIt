import PA194PAeqAtomValidity
import PA194PAeqFormulaCode
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeqTermBlueprint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
instance formulaCode_definable : 𝚺₁-Function₂ (formulaCode : V→V→V) := formulaCode_defined.to_definable

theorem formulaCode_valid (param : V) {n p : V} (hp : IsSemiformula ℒₒᵣ n p) :
    IsSemiformula PA194PAeq.language n (formulaCode param p) := by
  apply IsSemiformula.induction1 𝚺 (P:=fun n p => IsSemiformula PA194PAeq.language n (formulaCode param p)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k r ts hr ht
    rw [formulaCode_rel _ _ _ _ hr ht.isUTerm]
    exact atom_valid param hr ht
  · intro n k r ts hr ht
    rw [formulaCode_nrel _ _ _ _ hr ht.isUTerm]
    simpa using atom_valid param hr ht
  · intro n; rw [formulaCode_verum]; simp
  · intro n; rw [formulaCode_falsum]; simp
  · intro n p q hp hq ihp ihq
    rw [formulaCode_and _ _ _ hp.isUFormula hq.isUFormula]
    simpa using And.intro ihp ihq
  · intro n p q hp hq ihp ihq
    rw [formulaCode_or _ _ _ hp.isUFormula hq.isUFormula]
    simpa using And.intro ihp ihq
  · intro n p hp ih
    rw [formulaCode_all _ _ hp.isUFormula]
    simpa using ih
  · intro n p hp ih
    rw [formulaCode_exs _ _ hp.isUFormula]
    simpa using ih

#print axioms formulaCode_valid
end PA194PAeqTermBlueprint

