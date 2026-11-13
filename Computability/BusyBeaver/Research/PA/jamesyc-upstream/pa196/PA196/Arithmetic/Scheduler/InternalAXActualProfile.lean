module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalAXMacro
public import PA196.Arithmetic.CommandInternal
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.ModelAX
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]
noncomputable def valuation (t c d h y x : V) : Fin 6 → V := ![t,c,d,h,y,x]
lemma initial_profile (t c d h y x tail : V) :
    materialize (valuation t c d h y x) tail Source.AXSymbolic.initial=
      ⟨t,c,d,h,SourceCantorInternal.pairValue y (SourceCantorInternal.pairValue x tail),[]⟩ := rfl

/-- The actual symbolic output, calibrated uniformly to the arithmetic
command graph's repaired head/bundle expressions, not a Nat-only equation. -/
lemma actual_profile (t c d h y x tail : V) :
    materialize (valuation t c d h y x) tail PA196.Source.AXSymbolic.result=
      ⟨ActualArithmeticGraph.eval HeadGraphs.bundleExpr (h+y) (d+x) c d,
        c,d+x,h+y,tail,CommandStep.schemaHeads (d+x) (h+y) c d h ++ [t]⟩ := by
  simp [materialize,valuation,PA196.Source.AXSymbolic.result,eval,im,stackCode,
    CommandStep.schemaHeads,ActualArithmeticGraph.eval,
    HeadGraphs.head1Expr,HeadGraphs.head2Expr,HeadGraphs.head3Expr,
    HeadGraphs.head4Expr,HeadGraphs.head5Expr,HeadGraphs.head6Expr,
    HeadGraphs.rho8Expr,HeadGraphs.universalExpr,
    HeadGraphs.bundleExpr,HeadGraphs.pointExpr,HeadGraphs.separationExpr,
    HeadGraphs.eqVacExpr,HeadGraphs.memVacExpr,HeadGraphs.im,HeadGraphs.al,
    HeadGraphs.mem,HeadGraphs.eqn,HeadGraphs.neg,HeadGraphs.conj,
    HeadGraphs.ex,Nat.cast_ofNat,add_assoc,← one_add_one_eq_two,← two_add_one_eq_three]
lemma stackCode_foldr (xs : List V) (bottom : V) :
    stackCode xs bottom=xs.foldr SourceCantorInternal.pairValue bottom := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [stackCode,List.foldr_cons,ih]
#print axioms actual_profile
end PA196.Arithmetic.Machine.PA.InternalTrace.ModelAX

