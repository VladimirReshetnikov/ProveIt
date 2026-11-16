module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.FoundationRelationalCodeRecursion
public import Foundation.FirstOrder.Arithmetic.HFS.PRF
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalSource
open M6.PA.RelationalSource.Numeric


/-! A total auxiliary translation of HFS formula sets, not a reinterpretation
of sets as vectors. Numeric indices are scanned with actual HFS membership. -/
namespace PA196.Arithmetic.Transport.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

attribute [local irreducible] ActualArithmeticGraph.graph translateGraph translationOr

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Unknown/invalid formula members use the already fixed total translator.
The set itself is never decoded using nth or a vector length. -/
noncomputable def sequentStep (param s i previous : V) : V := by
  classical
  exact if i ∈ s then ActualArithmeticGraph.eval translationOr (translate param i) previous 0 0
    else previous

noncomputable def sequentStepGraph : 𝚺ᴬ₁.Semisentence 5 := .mkSigma
  “out previous i param s.
    (i ∈ s ∧ ∃ a, !translateGraph a param i ∧
      !(ActualArithmeticGraph.graph translationOr) out a previous 0 0) ∨
    (i ∉ s ∧ out=previous)”

theorem sequentStep_graph (out previous i param s : V) :
    sequentStepGraph.val.Evalb ![out,previous,i,param,s] ↔
      out=sequentStep param s i previous := by
  classical
  by_cases hi : i∈s <;>
    simp [sequentStepGraph,sequentStep,hi,ActualArithmeticGraph.graph_correct,Matrix.comp_vecCons'']

attribute [local irreducible] sequentStepGraph

noncomputable def sequentBlueprint : PR.Blueprint 2 where
  zero := .mkSigma “out param s. out=1”
  succ := sequentStepGraph

noncomputable def sequentConstruction : PR.Construction V sequentBlueprint where
  zero := fun _ => 1
  succ := fun v i previous => sequentStep (v 0) (v 1) i previous
  zero_defined := .mk fun v => by simp [sequentBlueprint]
  succ_defined := .mk fun v => by
    have hv : ![v 0,v 1,v 2,v 3,v 4]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! sequentStep_graph (v 0) (v 1) (v 2) (v 3) (v 4)

noncomputable def sequentScan (param s n : V) : V := sequentConstruction.result ![param,s] n

noncomputable def sequentScanGraph : 𝚺ᴬ₁.Semisentence 4 :=
  sequentBlueprint.resultDef.rew (Rew.subst ![#0,#3,#1,#2])

theorem sequentScan_graph (out param s n : V) :
    sequentScanGraph.val.Evalb ![out,param,s,n] ↔ out=sequentScan param s n := by
  simpa [sequentScanGraph,sequentScan,Matrix.comp_vecCons''] using!
    sequentConstruction.result_defined_iff ![out,n,param,s]

@[simp] theorem sequentScan_zero (param s : V) : sequentScan param s 0=1 := by
  simp [sequentScan,sequentConstruction]

theorem sequentScan_succ (param s n : V) :
    sequentScan param s (n+1)=sequentStep param s n (sequentScan param s n) := by
  simp [sequentScan,sequentConstruction]

theorem sequentScan_mem (param s n : V) (hn : n∈s) :
    sequentScan param s (n+1)=
      ActualArithmeticGraph.eval translationOr (translate param n) (sequentScan param s n) 0 0 := by
  rw [sequentScan_succ]
  simp [sequentStep,hn]

theorem sequentScan_not_mem (param s n : V) (hn : n∉s) :
    sequentScan param s (n+1)=sequentScan param s n := by
  rw [sequentScan_succ]
  simp [sequentStep,hn]

/-- Every HFS member lies below the numeric scan bound s. -/
noncomputable def sequentCode (param s : V) : V := sequentScan param s s

attribute [local irreducible] sequentScanGraph

noncomputable def sequentGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “out param s. !sequentScanGraph out param s s”

theorem sequent_graph (out param s : V) :
    sequentGraph.val.Evalb ![out,param,s] ↔ out=sequentCode param s := by
  simp only [sequentGraph,Bounding.HierarchySymbol.Semiformula.val_mkSigma]
  rw [Semiformula.eval_substs]
  simp [sequentScan_graph,sequentCode,Matrix.comp_vecCons'']

theorem sequent_total_unique (param s : V) :
    ∃! out, sequentGraph.val.Evalb ![out,param,s] := by
  refine ⟨sequentCode param s,(sequent_graph _ _ _).mpr rfl,?_⟩
  intro out h
  exact (sequent_graph _ _ _).mp h

@[simp] theorem sequent_empty (param : V) : sequentCode param (∅:V)=1 := by
  change sequentScan param 0 0=1
  exact sequentScan_zero _ _

theorem member_within_scan {p s : V} (h : p∈s) : p<s := lt_of_mem h

#print axioms sequentStep_graph
#print axioms sequentConstruction
#print axioms sequentScan_graph
#print axioms sequentScan_zero
#print axioms sequentScan_succ
#print axioms sequentScan_mem
#print axioms sequentScan_not_mem
#print axioms sequent_graph
#print axioms sequent_total_unique
#print axioms sequent_empty
#print axioms member_within_scan
end PA196.Arithmetic.Transport.RelationalSource.Numeric

