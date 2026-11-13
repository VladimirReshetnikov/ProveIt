module
public meta import Lean
import all M6PA.Scheduler.ActualCommandStepGraph
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualCommandWordGraph
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.ActualCommandStepGraph
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal ActualHeadGraphs
/- Resolve the private scalar-template names from the unchanged imported module.
This only supplies identifiers to ordinary `simp`; all produced equalities are
checked by the Lean kernel. No declaration or environment body is changed. -/
meta section
open Lean Elab Tactic in
elab "expose_pa215_step_helpers" : tactic => do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (n,_) =>
    if n.toString.startsWith "M6.PA.ActualCommandStepGraph." &&
        ["zero","top","stack","cacheD","cacheH","tag","fields","first","second","state","imp","headValue","push"].any
          (fun suffix => n.toString.endsWith ("." ++ suffix)) then some (mkIdent n) else none
  let names := names.toArray
  evalTactic (← `(tactic| simp only [$[$names:ident],*]))

end
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The word-expression pairing constructor is exactly the fixed source pair
in every arithmetic model; the HFS execution-state codec remains distinct. -/
theorem eval_source_pair (a b : ActualWordExpression.Scalar) (p t d : V) :
    ActualCheckExpression.eval (ActualWordMacros.pair a b) p t d =
      pairValue (ActualCheckExpression.eval a p t d) (ActualCheckExpression.eval b p t d) := by
  rfl

/-- The literal MP atom, uniformly over a possibly nonstandard operand. -/
noncomputable def mpCode (b : V) : V := pairValue 1 (pairValue b 0)

private theorem select_mp (b t w d h : V) :
    stepValue (mpCode b) (stateCode t w d h) =
      ActualWordExpression.eval mp (stateCode t w d h) (mpCode b) 0 := by
  unfold stepValue stepExpr
  expose_pa215_step_helpers
  simp only [ActualWordExpression.eval,ActualCheckExpression.eval]
  simp [mpCode,(decode_pairValue 1 (pairValue b 0)).1,stateCode_ne_zero]


/-- Exact all-model MP arithmetic. Unlike the earlier standard calibration,
this applies to arbitrary operands and states in every I-Sigma-1 model. -/
theorem mp_value (b t w d h : V) :
    stepValue (mpCode b) (stateCode t w d h) =
      if ActualArithmeticGraph.eval implicationExpr t (d+b) 0 0 = h then
        stateCode (d+b) (pairValue 0 w) (d+b) 0
      else stateCode 0 w (d+b) 0 := by
  rw [select_mp]
  unfold mp
  expose_pa215_step_helpers
  have hn (x xs : V) : (x ∷ xs).[3]=xs.[2] := by
    simpa [-nth_adjoin_succ,two_add_one_eq_three] using nth_adjoin_succ x xs 2
  simp [ActualWordExpression.eval,ActualCheckExpression.eval,eval_source_pair,
    mpCode,stateCode,hn,
    (decode_pairValue 1 (pairValue b 0)).2,(decode_pairValue b 0).1]

#print axioms mp_value
end M6.PA.ActualCommandStepGraph

