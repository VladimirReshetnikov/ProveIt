import PA194PAeqLanguage
import Foundation.FirstOrder.Bootstrapping.Syntax.Formula.Coding
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeqTermBlueprint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def equalityCode (s t : V) : V := qqRel 2 0 (s∷(t∷0))
noncomputable def lessCode (s t : V) : V := qqExs (equalityCode
  (qqFunc 2 2 (termBShift PA194PAeq.language s∷(qqFunc 1 1 (qqBvar 0∷0)∷0)))
  (termBShift PA194PAeq.language t))
noncomputable def equalityGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “out s t. ∃ ts sts, !adjoinDef ts t 0 ∧ !adjoinDef sts s ts ∧ !qqRelDef out 2 0 sts”
noncomputable def lessGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “out s t. ∃ ss tt b bs succ succs args add eq,
    !(termBShiftGraph PA194PAeq.language) ss s ∧ !(termBShiftGraph PA194PAeq.language) tt t ∧
    !qqBvarDef b 0 ∧ !adjoinDef bs b 0 ∧ !qqFuncDef succ 1 1 bs ∧
    !adjoinDef succs succ 0 ∧ !adjoinDef args ss succs ∧ !qqFuncDef add 2 2 args ∧
    !equalityGraph eq add tt ∧ !qqExsDef out eq”

theorem equality_graph (out s t : V) : equalityGraph.val.Evalb ![out,s,t] ↔ out=equalityCode s t := by
  simp [equalityGraph,equalityCode]
theorem less_graph (out s t : V) : lessGraph.val.Evalb ![out,s,t] ↔ out=lessCode s t := by
  simp [lessGraph,lessCode,equality_graph,Matrix.comp_vecCons'']

instance equality_defined : 𝚺₁-Function₂ (equalityCode : V→V→V) via equalityGraph :=
  .mk fun v => by
    have hv : ![v 0,v 1,v 2]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! equality_graph (v 0) (v 1) (v 2)
instance less_defined : 𝚺₁-Function₂ (lessCode : V→V→V) via lessGraph :=
  .mk fun v => by
    have hv : ![v 0,v 1,v 2]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! less_graph (v 0) (v 1) (v 2)


#print axioms equality_graph
#print axioms less_graph
#print axioms equality_defined
#print axioms less_defined
end PA194PAeqTermBlueprint
