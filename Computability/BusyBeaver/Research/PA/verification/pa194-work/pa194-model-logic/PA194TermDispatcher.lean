import PA194BinaryTermValue
import PA194PAeqTermFormulaTree
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace PA194TermDispatcher
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194PAeqTermFormulaTree
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def atomValue (param v env : V) : V :=
  variableValue (nth param 2) (nth (nth param env) (pi₂ (nth v 0 - 1)))
noncomputable def andValue (param p l r : V) : V :=
  if p = ^⊤ then successorValue (nth param 2) r
  else binaryValue additionTemplate (nth param 2) l r
noncomputable def orValue (param l r : V) : V := binaryValue multiplicationTemplate (nth param 2) l r
noncomputable def verumValue (param : V) : V := zeroValue (nth param 2)

noncomputable def termBlueprint : UformulaRec1.Blueprint where
  rel := .mkSigma “out param k R v. ∃ a a' i env x z, !nthDef a v 0 ∧ !subDef a' a 1 ∧ !pi₂Def i a' ∧
    !nthDef env param 0 ∧ !nthDef x env i ∧ !nthDef z param 2 ∧ !variableValueGraph out z x”
  nrel := .mkSigma “out param k R v. ∃ a a' i env x z, !nthDef a v 0 ∧ !subDef a' a 1 ∧ !pi₂Def i a' ∧
    !nthDef env param 1 ∧ !nthDef x env i ∧ !nthDef z param 2 ∧ !variableValueGraph out z x”
  verum := .mkSigma “out param. ∃ z, !nthDef z param 2 ∧ !zeroValueGraph out z”
  falsum := .mkSigma “out param. ∃ z, !nthDef z param 2 ∧ !zeroValueGraph out z”
  and := .mkSigma “out param p q l r. ∃ z top, !nthDef z param 2 ∧ !qqVerumDef top ∧
    ((p = top ∧ !successorValueGraph out z r) ∨ (p ≠ top ∧ !(binaryValueGraph additionTemplate) out z l r))”
  or := .mkSigma “out param p q l r. ∃ z, !nthDef z param 2 ∧ !(binaryValueGraph multiplicationTemplate) out z l r”
  all := .mkSigma “out param p r. out = r”
  exs := .mkSigma “out param p r. out = r”
  allChanges := .mkSigma “out param. !childParametersGraph out param”
  exsChanges := .mkSigma “out param. !(shiftParametersGraph) out param 1”

noncomputable def termConstruction : UformulaRec1.Construction V termBlueprint where
  rel param _ _ v := atomValue param v 0
  nrel param _ _ v := atomValue param v 1
  verum param := verumValue param
  falsum param := verumValue param
  and param p _ l r := andValue param p l r
  or param _ _ l r := orValue param l r
  all _ _ r := r
  exs _ _ r := r
  allChanges param := childParameters param
  exsChanges param := shiftParameters param 1
  rel_defined := .mk fun v => by simp [termBlueprint,atomValue,variableValue_graph,Matrix.comp_vecCons'']
  nrel_defined := .mk fun v => by simp [termBlueprint,atomValue,variableValue_graph,Matrix.comp_vecCons'']
  verum_defined := .mk fun v => by simp [termBlueprint,verumValue,zeroValue_graph,Matrix.comp_vecCons'']
  falsum_defined := .mk fun v => by simp [termBlueprint,verumValue,zeroValue_graph,Matrix.comp_vecCons'']
  and_defined := .mk fun v => by
    by_cases h : v 2 = (^⊤ : V) <;>
      simp [termBlueprint,andValue,h,successorValue_graph,binaryValue_graph,Matrix.comp_vecCons'']
  or_defined := .mk fun v => by simp [termBlueprint,orValue,binaryValue_graph,Matrix.comp_vecCons'']
  all_defined := .mk fun v => by simp [termBlueprint]
  exs_defined := .mk fun v => by simp [termBlueprint]
  allChanges_defined := .mk fun v => by simp [termBlueprint,childParameters_graph,Matrix.comp_vecCons'']
  exChanges_defined := .mk fun v => by simp [termBlueprint,shiftParameters_graph,Matrix.comp_vecCons'']

noncomputable def translate (param t : V) : V :=
  (termConstruction (V := V)).result SourceL param (termTree t)
noncomputable def translateGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “out param t. ∃ tree, !termTreeGraph tree t ∧ !(termBlueprint.result SourceL) out param tree”
theorem translate_graph (out param t : V) :
    translateGraph.val.Evalb ![out,param,t] ↔ out = translate param t := by
  simp [translateGraph,translate,termTree_defined.df,termConstruction.result_defined.df,Matrix.comp_vecCons'']
#print axioms translate_graph
end generic
end PA194TermDispatcher
