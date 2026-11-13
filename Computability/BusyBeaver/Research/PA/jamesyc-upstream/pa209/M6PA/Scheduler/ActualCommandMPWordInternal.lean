module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualCommandGenInternal
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.ActualCommandStepGraph
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal ActualHeadGraphs ActualCommandWordGraph ActualCommandLiteralInternal
open M6.Source M6.Source.CommandAtomEncoding
open InternalTrace.HFSAppend
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def mpWord (b : V) : V :=
  append (append (0 ∷ 0 ∷ mpCode b ∷ 0) (axThenShifts b 0 0 10)) (0 ∷ 0)

attribute [local irreducible] ActualWordMacros.literal ActualWordMacros.mpAtom ActualWordMacros.axAtom axThenShifts

theorem mp_expr (u : ActualWordExpression.Scalar) (p a b : V) :
    ActualWordExpression.eval (ActualWordMacros.mp u) p a b=
      mpWord (ActualCheckExpression.eval u p a b) := by
  simp [ActualWordMacros.mp,ActualWordMacros.singleton,ActualWordExpression.eval,
    literal_expr,eval_mp_atom,eval_ax_atom,ActualCheckExpression.eval,mpWord,axThenShifts,
    atoms,List.map_replicate,atom,Enumeration.encodeCommand,show Cantor.pair 0 0=0 from rfl]

/-- The exact MP suffix intentionally halts when its antecedent is one;
otherwise it returns the consequent with the original stack and clean caches. -/
theorem MP_value (a b w : V) :
    wordValue (mpWord b)
      (stateCode 0 (pairValue a (pairValue (ActualArithmeticGraph.eval implicationExpr a b 0 0) w)) 0 0)=
      if a=1 then 0 else stateCode b w 0 0 := by
  have hp : wordValue (0 ∷ 0 ∷ mpCode b ∷ 0)
      (stateCode 0 (pairValue a (pairValue (ActualArithmeticGraph.eval implicationExpr a b 0 0) w)) 0 0)=
      if a=1 then 0 else stateCode b (pairValue 0 w) b 0 := by
    by_cases ha : a=1 <;> simp [word_cons,word_zero,shift_value,ha,mp_value]
  rw [mpWord,word_append,word_append,hp]
  by_cases ha : a=1
  · simp [ha]
  · simp only [ha,ite_false]
    rw [ax_shift10_value,word_cons,word_zero,shift_value]
    simp [universal_add_ne_one]

theorem MP_expr_value (u : ActualWordExpression.Scalar) (p q r a w : V) :
    wordValue (ActualWordExpression.eval (ActualWordMacros.mp u) p q r)
      (stateCode 0 (pairValue a (pairValue
        (ActualArithmeticGraph.eval implicationExpr a (ActualCheckExpression.eval u p q r) 0 0) w)) 0 0)=
      if a=1 then 0 else stateCode (ActualCheckExpression.eval u p q r) w 0 0 := by
  rw [mp_expr,MP_value]

#print axioms MP_value
#print axioms MP_expr_value
end M6.PA.ActualCommandStepGraph
