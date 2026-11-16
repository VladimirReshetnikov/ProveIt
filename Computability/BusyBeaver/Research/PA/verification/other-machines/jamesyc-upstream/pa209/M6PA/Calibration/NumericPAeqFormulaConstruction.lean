module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaFields
@[expose] public section

/-! Actual changing-parameter formula recursion consuming the proved total
term witness function. Full PA models are required by that term supplier. -/
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

noncomputable def formulaConstruction : UformulaRec1.Construction V formulaBlueprint where
  rel := atomCode
  nrel := fun param k r ts => neg RelationalSource.language (atomCode param k r ts)
  verum := fun _ => qqVerum
  falsum := fun _ => qqFalsum
  and := fun _ _ _ a b => qqAnd a b
  or := fun _ _ _ a b => qqOr a b
  all := fun _ _ ys => guardedAllCode (nth ys 0)
  exs := fun _ _ ys => guardedExsCode (nth ys 0)
  allChanges := fun param _ => binderParameters param
  exsChanges := fun param _ => binderParameters param
  rel_defined := atom_defined
  nrel_defined := negativeAtom_defined
  verum_defined := truthTranslation_defined
  falsum_defined := falseTranslation_defined
  and_defined := andTranslation_defined
  or_defined := orTranslation_defined
  all_defined := allTranslation_defined
  exs_defined := exsTranslation_defined
  allChanges_defined := binderChange_defined
  exChanges_defined := binderChange_defined
  allChanges_monotone := fun _ => le_rfl
  exsChanges_monotone := fun _ => le_rfl

#print axioms formulaConstruction
end M6.PA.NumericPAeqFormula

