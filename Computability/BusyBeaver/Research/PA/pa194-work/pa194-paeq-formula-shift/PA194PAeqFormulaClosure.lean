import PA194PAeqFormulaShift
import Foundation.FirstOrder.Bootstrapping.Syntax.Formula.Iteration
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeqTermBlueprint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem termVector_one {t : V} (ht : IsUTerm ℒₒᵣ t) :
    termVector (1:V) (t∷0)=termCode t∷0 := by
  simpa using termVector_cons (k:=0) (ts:=0) ht (by simp)

theorem formulaCode_substs1 (param : V) {n p t : V}
    (hp : IsSemiformula ℒₒᵣ 1 p) (ht : IsSemiterm ℒₒᵣ n t) :
    formulaCode param (substs1 ℒₒᵣ t p)=
      substs1 PA194PAeq.language (termCode t) (formulaCode param p) := by
  simp only [substs1]
  rw [formulaCode_subst param hp (show IsSemitermVec ℒₒᵣ 1 n (t∷0) from by simp [ht]),
    termVector_one ht.isUTerm]

theorem formulaCode_free (param : V) {p : V} (hp : IsSemiformula ℒₒᵣ 1 p) :
    formulaCode param (Bootstrapping.free ℒₒᵣ p)=
      Bootstrapping.free PA194PAeq.language (formulaCode param p) := by
  simp only [Bootstrapping.free]
  rw [formulaCode_substs1 param hp.shift (show IsSemiterm ℒₒᵣ 0 (qqFvar 0) from by simp),
    termCode_fvar,formulaCode_shift param hp.isUFormula]

#print axioms termVector_one
#print axioms formulaCode_substs1
#print axioms formulaCode_free
end PA194PAeqTermBlueprint

