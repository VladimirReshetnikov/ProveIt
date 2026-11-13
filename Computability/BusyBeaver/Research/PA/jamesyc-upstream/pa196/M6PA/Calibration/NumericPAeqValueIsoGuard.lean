module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqValueIsoCode
public import Foundation.FirstOrder.Arithmetic.HFS.PRF
@[expose] public section

/-! Model-length pointwise order-isomorphism guards over two term vectors.
This is syntax construction only; no native certificate is assumed. -/
namespace M6.PA.NumericPAeqValueIsoGuard
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] templateTwoGraph
noncomputable def guardStepGraph : 𝚺ᴬ₁.Semisentence 5 := .mkSigma
  “out previous i env other. ∃ t u d, !nthDef t env i ∧ !nthDef u other i ∧ !isoCodeGraph d t u ∧ !qqAndDef out previous d”

theorem guardStep_graph (out previous i env other : V) :
    guardStepGraph.val.Evalb ![out,previous,i,env,other] ↔
      out=qqAnd previous (isoCode (nth env i) (nth other i)) := by
  simp [guardStepGraph,isoCode_graph,isoCode,Matrix.comp_vecCons'']

noncomputable def guardBlueprint : PR.Blueprint 2 where
  zero := .mkSigma “out env other. !qqVerumDef out”
  succ := guardStepGraph

noncomputable def guardConstruction : PR.Construction V guardBlueprint where
  zero := fun _ => qqVerum
  succ := fun v i previous => qqAnd previous (isoCode (nth (v 0) i) (nth (v 1) i))
  zero_defined := .mk fun v => by simp [guardBlueprint]
  succ_defined := .mk fun v => by
    have hv : ![v 0,v 1,v 2,v 3,v 4]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! guardStep_graph (v 0) (v 1) (v 2) (v 3) (v 4)

noncomputable def guard (env other count : V) : V := guardConstruction.result ![env,other] count
noncomputable def guardGraph : 𝚺ᴬ₁.Semisentence 4 :=
  guardBlueprint.resultDef.rew (Rew.subst ![#0,#3,#1,#2])

theorem guard_graph (out env other count : V) :
    guardGraph.val.Evalb ![out,env,other,count] ↔ out=guard env other count := by
  simpa [guardGraph,guard,Matrix.comp_vecCons''] using!
    guardConstruction.result_defined_iff ![out,count,env,other]

@[simp] theorem guard_zero (env other : V) : guard env other 0=qqVerum := by
  simp [guard,guardConstruction]
theorem guard_succ (env other count : V) :
    guard env other (count+1)=qqAnd (guard env other count) (isoCode (nth env count) (nth other count)) := by
  simp [guard,guardConstruction]

theorem guard_total_unique (env other count : V) : ∃! out, guardGraph.val.Evalb ![out,env,other,count] := by
  refine ⟨guard env other count,(guard_graph _ _ _ _).mpr rfl,?_⟩
  intro out h; exact (guard_graph _ _ _ _).mp h

#print axioms guard_graph
#print axioms guard_zero
#print axioms guard_succ
#print axioms guard_total_unique
end M6.PA.NumericPAeqValueIsoGuard

