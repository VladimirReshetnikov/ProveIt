module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermTemplates
public import Foundation.FirstOrder.Arithmetic.HFS.PRF
@[expose] public section

/-! Model-length domain guards over a vector of relational term codes.
This is syntax construction only; no native certificate is assumed. -/
namespace M6.PA.NumericPAeqValueDomainGuard
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] templateOneGraph
noncomputable def guardStepGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “out previous i env. ∃ t d, !nthDef t env i ∧ !domainCodeGraph d t ∧ !qqAndDef out previous d”

theorem guardStep_graph (out previous i env : V) :
    guardStepGraph.val.Evalb ![out,previous,i,env] ↔
      out=qqAnd previous (domainCode (nth env i)) := by
  simp [guardStepGraph,templateOne_graph,domainCode,Matrix.comp_vecCons'']

noncomputable def guardBlueprint : PR.Blueprint 1 where
  zero := .mkSigma “out env. !qqVerumDef out”
  succ := guardStepGraph

noncomputable def guardConstruction : PR.Construction V guardBlueprint where
  zero := fun _ => qqVerum
  succ := fun v i previous => qqAnd previous (domainCode (nth (v 0) i))
  zero_defined := .mk fun v => by simp [guardBlueprint]
  succ_defined := .mk fun v => by
    have hv : ![v 0,v 1,v 2,v 3]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! guardStep_graph (v 0) (v 1) (v 2) (v 3)

noncomputable def guard (env count : V) : V := guardConstruction.result ![env] count
noncomputable def guardGraph : 𝚺ᴬ₁.Semisentence 3 :=
  guardBlueprint.resultDef.rew (Rew.subst ![#0,#2,#1])

theorem guard_graph (out env count : V) :
    guardGraph.val.Evalb ![out,env,count] ↔ out=guard env count := by
  simpa [guardGraph,guard,Matrix.comp_vecCons''] using!
    guardConstruction.result_defined_iff ![out,count,env]

@[simp] theorem guard_zero (env : V) : guard env 0=qqVerum := by
  simp [guard,guardConstruction]
theorem guard_succ (env count : V) :
    guard env (count+1)=qqAnd (guard env count) (domainCode (nth env count)) := by
  simp [guard,guardConstruction]

theorem guard_total_unique (env count : V) : ∃! out, guardGraph.val.Evalb ![out,env,count] := by
  refine ⟨guard env count,(guard_graph _ _ _).mpr rfl,?_⟩
  intro out h; exact (guard_graph _ _ _).mp h

#print axioms guard_graph
#print axioms guard_zero
#print axioms guard_succ
#print axioms guard_total_unique
end M6.PA.NumericPAeqValueDomainGuard

