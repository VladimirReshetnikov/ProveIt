module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalAXMacro
public import M6PA.Scheduler.ActualCommandAXInternal
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.ModelAX
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def valuation (t c d h y x : V) : Fin 6 → V := ![t,c,d,h,y,x]
lemma initial_profile (t c d h y x tail : V) :
    materialize (valuation t c d h y x) tail Source.AXSymbolic.initial=
      ⟨t,c,d,h,SourceCantorInternal.pairValue y (SourceCantorInternal.pairValue x tail),[]⟩ := rfl

/-- The actual symbolic output, calibrated uniformly to the arithmetic
command graph's repaired head/bundle expressions, not a Nat-only equation. -/
lemma actual_profile (t c d h y x tail : V) :
    materialize (valuation t c d h y x) tail Source.AXSymbolic.actualResult=
      ⟨ActualArithmeticGraph.eval ActualHeadGraphs.bundleExpr (d+x) (h+y) c d,
        c,d+x,h+y,tail,ActualCommandStepGraph.schemaHeads (d+x) (h+y) c d h ++ [t]⟩ := by
  simp [materialize,valuation,Source.AXSymbolic.actualResult,eval,im,stackCode,
    ActualCommandStepGraph.schemaHeads,ActualArithmeticGraph.eval,
    ActualHeadGraphs.rho1Expr,ActualHeadGraphs.rho2Expr,ActualHeadGraphs.rho3Expr,
    ActualHeadGraphs.rho4Expr,ActualHeadGraphs.rho5Expr,ActualHeadGraphs.rho6Expr,
    ActualHeadGraphs.rho7Expr,ActualHeadGraphs.rho8Expr,ActualHeadGraphs.universalExpr,
    ActualHeadGraphs.bundleExpr,ActualHeadGraphs.pointExpr,ActualHeadGraphs.separationExpr,
    ActualHeadGraphs.memVacExpr,ActualHeadGraphs.im,ActualHeadGraphs.al,
    ActualHeadGraphs.mem,ActualHeadGraphs.eqn,ActualHeadGraphs.neg,ActualHeadGraphs.conj,
    ActualHeadGraphs.ex,Nat.cast_ofNat,add_assoc,← one_add_one_eq_two,← two_add_one_eq_three]
lemma stackCode_foldr (xs : List V) (bottom : V) :
    stackCode xs bottom=xs.foldr SourceCantorInternal.pairValue bottom := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [stackCode,List.foldr_cons,ih]
#print axioms actual_profile
end M6.Arithmetic.PA.InternalTrace.ModelAX

