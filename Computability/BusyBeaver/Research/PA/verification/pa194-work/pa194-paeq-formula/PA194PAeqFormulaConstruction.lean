import PA194PAeqAtomCode
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeqTermBlueprint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
attribute [local irreducible] atomGraph
noncomputable def negativeAtomGraph : 𝚺₁.Semisentence 5 := .mkSigma
  “out param k r ts. ∃ a, !atomGraph a param k r ts ∧ !(negGraph PA194PAeq.language) out a”
noncomputable def formulaBlueprint : UformulaRec1.Blueprint where
  rel := atomGraph
  nrel := negativeAtomGraph
  verum := .mkSigma “out param. !qqVerumDef out”
  falsum := .mkSigma “out param. !qqFalsumDef out”
  and := .mkSigma “out param p q a b. !qqAndDef out a b”
  or := .mkSigma “out param p q a b. !qqOrDef out a b”
  allChanges := .mkSigma “out param. out = param”
  exsChanges := .mkSigma “out param. out = param”
  all := .mkSigma “out param p y. !qqAllDef out y”
  exs := .mkSigma “out param p y. !qqExsDef out y”
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def formulaConstruction : UformulaRec1.Construction V formulaBlueprint where
  rel := atomCode
  nrel := fun param k r ts => neg PA194PAeq.language (atomCode param k r ts)
  verum := fun _ => qqVerum
  falsum := fun _ => qqFalsum
  and := fun _ _ _ a b => qqAnd a b
  or := fun _ _ _ a b => qqOr a b
  allChanges := fun param => param
  exsChanges := fun param => param
  all := fun _ _ y => qqAll y
  exs := fun _ _ y => qqExs y
  rel_defined := atom_defined
  nrel_defined := .mk fun v => by
    simp only [formulaBlueprint,negativeAtomGraph,HierarchySymbol.Semiformula.val_mkSigma]
    simp [Matrix.comp_vecCons'']
  verum_defined := .mk fun v => by simp [formulaBlueprint]
  falsum_defined := .mk fun v => by simp [formulaBlueprint]
  and_defined := .mk fun v => by simp [formulaBlueprint]
  or_defined := .mk fun v => by simp [formulaBlueprint]
  allChanges_defined := .mk fun v => by simp [formulaBlueprint]
  exChanges_defined := .mk fun v => by simp [formulaBlueprint]
  all_defined := .mk fun v => by simp [formulaBlueprint]
  exs_defined := .mk fun v => by simp [formulaBlueprint]

#print axioms formulaConstruction
end PA194PAeqTermBlueprint

