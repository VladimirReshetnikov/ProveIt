module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermLanguage
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Term.Functions
public import Mathlib.Tactic.FinCases
@[expose] public section

/-! The literal Foundation ordered-semiring to PAeq term-code adapter.
It keeps source variable indices, sends one to S(0), and changes function tags.
This is syntax, not a proof-code translation. -/
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def zeroCode : V := qqFunc 0 0 0
noncomputable def oneCode : V := qqFunc 1 1 (zeroCode ∷ 0)
noncomputable def functionCode (k f w : V) : V :=
  if k=0 then if f=0 then zeroCode else oneCode
  else qqFunc 2 (if f=0 then 2 else 3) w

noncomputable def functionCodeGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “out k f w.
    (k=0 ∧ f=0 ∧ !qqFuncDef out 0 0 0) ∨
    (k=0 ∧ f≠0 ∧ ∃ z zs, !qqFuncDef z 0 0 0 ∧ !adjoinDef zs z 0 ∧ !qqFuncDef out 1 1 zs) ∨
    (k≠0 ∧ f=0 ∧ !qqFuncDef out 2 2 w) ∨
    (k≠0 ∧ f≠0 ∧ !qqFuncDef out 2 3 w)”

theorem functionCode_graph (out k f w : V) :
    functionCodeGraph.val.Evalb ![out,k,f,w] ↔ out=functionCode k f w := by
  by_cases hk : k=0 <;> by_cases hf : f=0 <;>
    simp [functionCodeGraph,functionCode,zeroCode,oneCode,hk,hf]

instance functionCode_defined :
    𝚺ᴬ₁-Function₃ (functionCode : V→V→V→V) via functionCodeGraph :=
  .mk fun v => by
    have hv : ![v 0,v 1,v 2,v 3]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! functionCode_graph (v 0) (v 1) (v 2) (v 3)

attribute [local irreducible] functionCodeGraph
noncomputable def termBlueprint : Language.TermRec.Blueprint 0 where
  bvar := .mkSigma “out i. !qqBvarDef out i”
  fvar := .mkSigma “out i. !qqFvarDef out i”
  func := .mkSigma “out k f v w. !functionCodeGraph out k f w”

noncomputable def termConstruction : Language.TermRec.Construction V termBlueprint where
  bvar _ i := qqBvar i
  fvar _ i := qqFvar i
  func _ k f _ w := functionCode k f w
  bvar_defined := .mk fun v => by simp [termBlueprint]
  fvar_defined := .mk fun v => by simp [termBlueprint]
  func_defined := .mk fun v => by
    simp only [termBlueprint,Bounding.HierarchySymbol.Semiformula.val_mkSigma]
    rw [Semiformula.eval_substs]
    simp [functionCode_defined.df]

#print axioms functionCode_graph
#print axioms functionCode_defined
#print axioms termConstruction
end M6.PA.FoundationPAeqCode

