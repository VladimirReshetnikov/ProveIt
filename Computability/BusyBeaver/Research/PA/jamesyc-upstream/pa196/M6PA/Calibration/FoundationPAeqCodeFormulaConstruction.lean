module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeAtomTranslation
@[expose] public section

/-! Original arithmetic to PAeq formula recursion. The dummy parameter is
unchanged under binders. Its graph is supplied by the actual pinned recursor;
no axiom-image or proof-number transform is assumed here. -/
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
attribute [local irreducible] atomGraph
noncomputable def negativeAtomGraph : 𝚺ᴬ₁.Semisentence 5 := .mkSigma
  “out param k r ts. ∃ a, !atomGraph a param k r ts ∧ !(negGraph Presentation.language) out a”
noncomputable def formulaBlueprint : UformulaRec1.Blueprint where
  rel := atomGraph
  nrel := negativeAtomGraph
  verum := .mkSigma “out param. !qqVerumDef out”
  falsum := .mkSigma “out param. !qqFalsumDef out”
  and := .mkSigma “out param p q a b. !qqAndDef out a b”
  or := .mkSigma “out param p q a b. !qqOrDef out a b”
  all := .mkSigma “out param p ys. ∃ a, !nthDef a ys 0 ∧ !qqAllDef out a”
  exs := .mkSigma “out param p ys. ∃ a, !nthDef a ys 0 ∧ !qqExsDef out a”
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def formulaConstruction : UformulaRec1.Construction V formulaBlueprint where
  rel := atomCode
  nrel := fun param k r ts => neg Presentation.language (atomCode param k r ts)
  verum := fun _ => qqVerum
  falsum := fun _ => qqFalsum
  and := fun _ _ _ a b => qqAnd a b
  or := fun _ _ _ a b => qqOr a b
  all := fun _ _ ys => qqAll (nth ys 0)
  exs := fun _ _ ys => qqExs (nth ys 0)
  rel_defined := atom_defined
  nrel_defined := .mk fun v => by
    simp only [formulaBlueprint,negativeAtomGraph,Bounding.HierarchySymbol.Semiformula.val_mkSigma]
    simp [atom_graph,Matrix.comp_vecCons'']
  verum_defined := .mk fun v => by simp [formulaBlueprint]
  falsum_defined := .mk fun v => by simp [formulaBlueprint]
  and_defined := .mk fun v => by simp [formulaBlueprint]
  or_defined := .mk fun v => by simp [formulaBlueprint]
  all_defined := .mk fun v => by simp [formulaBlueprint]
  exs_defined := .mk fun v => by simp [formulaBlueprint]

#print axioms formulaConstruction
end M6.PA.FoundationPAeqCode

