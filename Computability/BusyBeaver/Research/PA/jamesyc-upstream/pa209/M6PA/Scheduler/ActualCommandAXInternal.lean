module
import all M6PA.Scheduler.ActualCommandStepGraph
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualCommandMPInternal
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.ActualCommandStepGraph
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal ActualHeadGraphs
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Exact source command atom: the first decoded field is y, then x. -/
noncomputable def axCode (c x y : V) : V := pairValue (c+2) (pairValue y (pairValue x 0))

noncomputable def schemaHeads (a b c d h : V) : List V :=
  [ActualArithmeticGraph.eval rho1Expr a b c d,
   ActualArithmeticGraph.eval rho2Expr a b c d,
   ActualArithmeticGraph.eval rho3Expr a b c d,
   ActualArithmeticGraph.eval rho4Expr a b c d,
   ActualArithmeticGraph.eval rho5Expr a b c d,
   ActualArithmeticGraph.eval rho6Expr a b c d,
   ActualArithmeticGraph.eval rho7Expr a b c d,
   ActualArithmeticGraph.eval rho8Expr a b c d,
   ActualArithmeticGraph.eval universalExpr d h 0 0]
noncomputable def gateValue (a b c d : V) : V :=
  if c=a then 0 else if c=b then 0 else ActualArithmeticGraph.eval bundleExpr a b c d

private theorem select_ax (c x y t w d h : V) :
    stepValue (axCode c x y) (stateCode t w d h) =
      ActualWordExpression.eval ax (stateCode t w d h) (axCode c x y) 0 := by
  have hp : (1 : V)<c+2 := lt_of_lt_of_le (show (1 : V)<2 by simp) (show (2 : V)≤c+2 by simp)
  have h0 : c+2≠(0 : V) := ne_of_gt (lt_trans (by simp) hp)
  have h1 : c+2≠(1 : V) := ne_of_gt hp
  unfold stepValue stepExpr
  expose_pa215_step_helpers
  simp only [ActualWordExpression.eval,ActualCheckExpression.eval]
  simp [axCode,(decode_pairValue (c+2) (pairValue y (pairValue x 0))).1,
    stateCode_ne_zero,h0,h1]

/-- Actual nine-head order, guarded bundle, saved top, and original cache D
are preserved uniformly, without assuming standardness of any register. -/
theorem ax_value (c x y t w d h : V) :
    stepValue (axCode c x y) (stateCode t w d h) =
      stateCode (gateValue (d+x) (h+y) c d)
        ((schemaHeads (d+x) (h+y) c d h ++ [t]).foldr pairValue w) 0 0 := by
  rw [select_ax]
  unfold ax
  expose_pa215_step_helpers
  have hn (z zs : V) : (z ∷ zs).[3]=zs.[2] := by
    simpa [-nth_adjoin_succ,two_add_one_eq_three] using nth_adjoin_succ z zs 2
  simp [ActualWordExpression.eval,ActualCheckExpression.eval,eval_source_pair,
    axCode,stateCode,hn,schemaHeads,gateValue,
    (decode_pairValue (c+2) (pairValue y (pairValue x 0))).1,
    (decode_pairValue (c+2) (pairValue y (pairValue x 0))).2,
    (decode_pairValue y (pairValue x 0)).1,(decode_pairValue y (pairValue x 0)).2,
    (decode_pairValue x 0).1]

#print axioms ax_value
end M6.PA.ActualCommandStepGraph

