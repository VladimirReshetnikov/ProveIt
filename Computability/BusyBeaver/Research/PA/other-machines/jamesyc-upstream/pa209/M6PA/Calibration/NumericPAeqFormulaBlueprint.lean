module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaAtoms
@[expose] public section
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

noncomputable def negativeAtomGraph : 𝚺ᴬ₁.Semisentence 5 := .mkSigma
  “out param k r ts. ∃ a, !atomGraph a param k r ts ∧
    !(negGraph RelationalSource.language) out a”
noncomputable def truthTranslationGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “out param. !qqVerumDef out”
noncomputable def falseTranslationGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “out param. !qqFalsumDef out”
noncomputable def andTranslationGraph : 𝚺ᴬ₁.Semisentence 6 := .mkSigma
  “out param p q a b. !qqAndDef out a b”
noncomputable def orTranslationGraph : 𝚺ᴬ₁.Semisentence 6 := .mkSigma
  “out param p q a b. !qqOrDef out a b”
noncomputable def allTranslationGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “out param p ys. ∃ a, !nthDef a ys 0 ∧ !guardedAllGraph out a”
noncomputable def exsTranslationGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “out param p ys. ∃ a, !nthDef a ys 0 ∧ !guardedExsGraph out a”
noncomputable def binderChangeGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “out param i. !binderParametersGraph out param”
noncomputable def formulaBlueprint : UformulaRec1.Blueprint where
  rel := atomGraph
  nrel := negativeAtomGraph
  verum := truthTranslationGraph
  falsum := falseTranslationGraph
  and := andTranslationGraph
  or := orTranslationGraph
  all := allTranslationGraph
  exs := exsTranslationGraph
  allChanges := binderChangeGraph
  exsChanges := binderChangeGraph
end M6.PA.NumericPAeqFormula

