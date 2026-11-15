import PA194PAeqOpeningFormulaInverse
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.InductionReopen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqBind
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local instance] PA194PAeqBind.ordinaryPAeq_delta

theorem openingInverse : OpeningInverse (V := V) := by
  intro p hp
  exact (OpeningQVec.bindFormula_scope_open p hp).2

theorem primitiveBody_unconditional {p : V} (hp : IsSemiformula language 1 p) :
    Provable ordinaryPAeq (inductionBody p) := primitiveBody openingInverse hp

theorem addOneBody_unconditional {p : V} (hp : IsSemiformula language 1 p) :
    Provable ordinaryPAeq (inductionBodyAddOne p) := addOneBody openingInverse hp

theorem arithmeticInductionBody_unconditional (param : V) {p : V}
    (hp : IsSemiformula ℒₒᵣ 1 p) :
    Provable ordinaryPAeq (PA194PAeqTermBlueprint.formulaCode param (indBodyVal p)) :=
  arithmeticInductionBody openingInverse param hp
#print axioms openingInverse
#print axioms primitiveBody_unconditional
#print axioms addOneBody_unconditional
#print axioms arithmeticInductionBody_unconditional
end PA194PAeq.InductionReopen
