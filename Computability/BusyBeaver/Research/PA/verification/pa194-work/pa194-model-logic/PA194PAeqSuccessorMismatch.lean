import PA194PAeqClosedInduction
import PA194PAeqTermCode
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqTermBlueprint
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def arithmeticSuccVariable : V := ^func 2 0 (?[ ^#(0 : V), ^func (0 : V) 1 0] : V)
theorem arithmeticSuccVariable_code : termCode (arithmeticSuccVariable : V) =
    ^func (2 : V) 2 (?[ ^#(0 : V), ^func (1 : V) 1 (?[ ^func (0 : V) 0 0] : V)] : V) := by
  rw [arithmeticSuccVariable, termCode_add (by simp) (by simp [original_functions])]
  simp [PA194PAeqTermBlueprint.zeroCode, PA194PAeqTermBlueprint.oneCode]
theorem arithmeticSuccVariable_ne_primitive : termCode (arithmeticSuccVariable : V) ≠ succVarCode := by
  rw [arithmeticSuccVariable_code]
  simp [succVarCode,qqFunc]
#print axioms arithmeticSuccVariable_code
#print axioms arithmeticSuccVariable_ne_primitive
end generic
end PA194PAeqBind
