module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermFreeSupportSubstitution
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Functions
@[expose] public section
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => Presentation.language
attribute [local irreducible] NumericPAeqTerm.freeBoundVecGraph
namespace FreeBound


noncomputable def blueprint : UformulaRec1.Blueprint where
  rel := .mkSigma “y param k R v. ∃ M, !(NumericPAeqTerm.freeBoundVecGraph) M k v ∧ !listMaxDef y M”
  nrel := .mkSigma “y param k R v. ∃ M, !(NumericPAeqTerm.freeBoundVecGraph) M k v ∧ !listMaxDef y M”
  verum := .mkSigma “y param. y = 0”
  falsum := .mkSigma “y param. y = 0”
  and := .mkSigma “y param p₁ p₂ y₁ y₂. !max.dfn y y₁ y₂”
  or := .mkSigma “y param p₁ p₂ y₁ y₂. !max.dfn y y₁ y₂”
  all := .mkSigma “y param p₁ ys. !nthDef y ys 0”
  exs := .mkSigma “y param p₁ ys. !nthDef y ys 0”

end FreeBound
#print axioms FreeBound.blueprint
end M6.PA.NumericPAeqFormula

