module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.FoundationRelationalCodeFields
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalSource
open M6.PA.RelationalSource.Numeric

namespace PA196.Arithmetic.Transport.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualArithmeticGraph PA196.Arithmetic.HeadGraphs
attribute [local irreducible] ActualArithmeticGraph.graph totalAtomGraph advanceGraph
  translationNeg translationAnd translationOr translationExs universalExpr

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


noncomputable def formulaConstruction : UformulaRec1.Construction V formulaBlueprint where
  rel := totalAtom
  nrel := fun param k r ts => eval translationNeg (totalAtom param k r ts) 0 0 0
  verum := fun _ => 0
  falsum := fun _ => 1
  and := fun _ _ _ a b => eval translationAnd a b 0 0
  or := fun _ _ _ a b => eval translationOr a b 0 0
  all := fun param _ ys => eval universalExpr (nth param 2) (nth ys 0) 0 0
  exs := fun param _ ys => eval translationExs (nth param 2) (nth ys 0) 0 0
  allChanges := fun param _ => advance param
  exsChanges := fun param _ => advance param
  rel_defined := totalAtom_defined
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
end PA196.Arithmetic.Transport.RelationalSource.Numeric

