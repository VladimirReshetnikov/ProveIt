module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermFunction
public import Foundation.FirstOrder.Arithmetic.HFS.PRF
@[expose] public section

/-! A genuine model-length conjunction of actual substitution-entry value
formulas. This defines syntax, not truth or accepted certificates. -/
namespace M6.PA.NumericPAeqValueRealizationGuard
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

noncomputable def entry (b f w a i:V):V := valueSyntax (parameters b f (nth a i)) (nth w i)
attribute [local irreducible] valueSyntaxGraph parametersGraph
noncomputable def entryGraph : 𝚺ᴬ₁.Semisentence 6 := .mkSigma
  “out b f w a i. ∃ t x param, !nthDef t w i ∧ !nthDef x a i ∧
    !parametersGraph param b f x ∧ !valueSyntaxGraph out param t”
theorem entry_graph (out b f w a i:V):entryGraph.val.Evalb ![out,b,f,w,a,i] ↔ out=entry b f w a i := by
  simp [entryGraph,entry,parameters_graph,valueSyntax_graph,Matrix.comp_vecCons'']
attribute [local irreducible] entryGraph
noncomputable def guardStepGraph : 𝚺ᴬ₁.Semisentence 7 := .mkSigma
  “out previous i b f w a. ∃ e, !entryGraph e b f w a i ∧ !qqAndDef out previous e”
theorem guardStep_graph (out previous i b f w a:V):
    guardStepGraph.val.Evalb ![out,previous,i,b,f,w,a] ↔ out=qqAnd previous (entry b f w a i) := by
  simp [guardStepGraph,entry_graph,Matrix.comp_vecCons'']
noncomputable def guardBlueprint : PR.Blueprint 4 where
  zero := .mkSigma “out b f w a. !qqVerumDef out”
  succ := guardStepGraph
noncomputable def guardConstruction : PR.Construction V guardBlueprint where
  zero := fun _ => qqVerum
  succ := fun v i previous => qqAnd previous (entry (v 0) (v 1) (v 2) (v 3) i)
  zero_defined := .mk fun v => by simp [guardBlueprint]
  succ_defined := .mk fun v => by
    have hv : ![v 0,v 1,v 2,v 3,v 4,v 5,v 6]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! guardStep_graph (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)
noncomputable def guard (b f w a count:V):V := guardConstruction.result ![b,f,w,a] count
noncomputable def guardGraph : 𝚺ᴬ₁.Semisentence 6 :=
  guardBlueprint.resultDef.rew (Rew.subst ![#0,#5,#1,#2,#3,#4])
theorem guard_graph (out b f w a count:V):guardGraph.val.Evalb ![out,b,f,w,a,count] ↔ out=guard b f w a count := by
  simpa [guardGraph,guard,Matrix.comp_vecCons''] using!
    guardConstruction.result_defined_iff ![out,count,b,f,w,a]
@[simp] theorem guard_zero (b f w a:V):guard b f w a 0=qqVerum := by simp [guard,guardConstruction]
theorem guard_succ (b f w a count:V):guard b f w a (count+1)=qqAnd (guard b f w a count) (entry b f w a count) := by
  simp [guard,guardConstruction]
theorem guard_total_unique (b f w a count:V):∃!out,guardGraph.val.Evalb ![out,b,f,w,a,count] := by
  refine ⟨guard b f w a count,(guard_graph _ _ _ _ _ _).mpr rfl,?_⟩
  intro out h; exact (guard_graph _ _ _ _ _ _).mp h
#print axioms entry_graph
#print axioms guard_graph
#print axioms guard_succ
#print axioms guard_total_unique
end M6.PA.NumericPAeqValueRealizationGuard

