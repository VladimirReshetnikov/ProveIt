module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalCodeTotalAtoms
@[expose] public section

/-! A concrete all-model formula recursion, with explicit changing binder
parameters. Correctness under global coverage and external calibration are
separate from totality and the constructor equations proved here. -/
namespace M6.PA.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualArithmeticGraph ActualHeadGraphs

def translationNeg : Expr := neg .a
def translationAnd : Expr := conj .a .b
def translationOr : Expr := im (neg .a) .b
def translationExs : Expr := ex .a .b

attribute [local irreducible] ActualArithmeticGraph.graph totalAtomGraph advanceGraph
  translationNeg translationAnd translationOr translationExs universalExpr


noncomputable def negativeAtomGraph : 𝚺ᴬ₁.Semisentence 5 := .mkSigma
  “y param k r ts. ∃ a, !totalAtomGraph a param k r ts ∧
    !(graph translationNeg) y a 0 0 0”
noncomputable def truthTranslationGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma “y param. y=0”
noncomputable def falseTranslationGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma “y param. y=1”
noncomputable def andTranslationGraph : 𝚺ᴬ₁.Semisentence 6 := .mkSigma
  “y param p q a b. !(graph translationAnd) y a b 0 0”
noncomputable def orTranslationGraph : 𝚺ᴬ₁.Semisentence 6 := .mkSigma
  “y param p q a b. !(graph translationOr) y a b 0 0”
noncomputable def allTranslationGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “y param p ys. ∃ lo a, !nthDef lo param 2 ∧ !nthDef a ys 0 ∧
    !(graph universalExpr) y lo a 0 0”
noncomputable def exsTranslationGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “y param p ys. ∃ lo a, !nthDef lo param 2 ∧ !nthDef a ys 0 ∧
    !(graph translationExs) y lo a 0 0”
noncomputable def binderChangeGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “out param i. !advanceGraph out param”

noncomputable def formulaBlueprint : UformulaRec1.Blueprint where
  rel := totalAtomGraph
  nrel := negativeAtomGraph
  verum := truthTranslationGraph
  falsum := falseTranslationGraph
  and := andTranslationGraph
  or := orTranslationGraph
  all := allTranslationGraph
  exs := exsTranslationGraph
  allChanges := binderChangeGraph
  exsChanges := binderChangeGraph

#print axioms formulaBlueprint
end M6.PA.RelationalSource.Numeric

