import PA196PASubstitutionStageUniform
import PA196PRAQVecTower

/-! Explicit arithmetic graph and candidate-PRA term for the substitution
stage bound. No candidate-PRA graph domination is asserted here. -/
set_option autoImplicit false
namespace PA196PASubstitutionTowerGraph
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PA196PAQVecSeqTrace PA196PAQVecTowerAlgebra

noncomputable def towerGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “out x. !boundBlueprint.resultDef out (x+2) (4*x+1)”
noncomputable def towerTerm : TermN 1 :=
  .func PA196PRAQVecTower.towerCode
    ![Semiterm.lMap embedding ‘#0+2’, Semiterm.lMap embedding ‘4*#0+1’]

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem towerGraph_eval (out x : V) :
    towerGraph.val.Evalb ![out,x] ↔ out = iter (x+2) (4*x+1) := by
  have h := (boundConstruction (V := V)).result_defined_iff ![out,x+2,4*x+1]
  simpa [towerGraph, iter, Matrix.fun_eq_vec_one, numeral_eq_natCast] using h

#print axioms towerGraph_eval
end PA196PASubstitutionTowerGraph
