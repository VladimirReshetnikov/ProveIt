module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualCommandDiscardInternal
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.ActualCommandStepGraph
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal ActualHeadGraphs ActualCommandWordGraph ActualCommandLiteralInternal
open M6.Source M6.Source.CommandAtomEncoding M6.Source.ActualCommandMacros
open InternalTrace.HFSAppend
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem eval_ax_atom (c x y : ActualWordExpression.Scalar) (p a b : V) :
    ActualCheckExpression.eval (ActualWordMacros.axAtom c x y) p a b=
      axCode (ActualCheckExpression.eval c p a b) (ActualCheckExpression.eval x p a b)
        (ActualCheckExpression.eval y p a b) := by
  simp [ActualWordMacros.axAtom,eval_source_pair,ActualCheckExpression.eval,axCode]

noncomputable def genWord (u : V) : V :=
  append (append (append (literalValue (atoms PUSH)) (jWord u)) (0 ∷ 0))
    (axThenShifts u 0 0 10)

attribute [local irreducible] PUSH ActualWordMacros.literal ActualWordMacros.j ActualWordMacros.axAtom axThenShifts

theorem gen_expr (u : ActualWordExpression.Scalar) (p a b : V) :
    ActualWordExpression.eval (ActualWordMacros.gen u) p a b=
      genWord (ActualCheckExpression.eval u p a b) := by
  simp [ActualWordMacros.gen,ActualWordExpression.eval,j_expr,literal_expr,eval_ax_atom,
    ActualCheckExpression.eval,genWord,axThenShifts,atoms,List.map_replicate,atom,Enumeration.encodeCommand,
    show Cantor.pair 0 0=0 from rfl]

/-- The actual GEN suffix is total, including an incoming formula code one. -/
theorem GEN_value (u t w d h : V) :
    wordValue (genWord u) (stateCode t w d h)=
      stateCode (ActualArithmeticGraph.eval universalExpr u t 0 0) w 0 0 := by
  rw [genWord,word_append,word_append,word_append,PUSH_value,J_value,word_cons,word_zero,shift_value]
  simp only [zero_add,zero_ne_one,ite_false,source_left_pair,source_right_pair]
  rw [ax_shift10_value]

theorem GEN_expr_value (u : ActualWordExpression.Scalar) (p a b t w d h : V) :
    wordValue (ActualWordExpression.eval (ActualWordMacros.gen u) p a b) (stateCode t w d h)=
      stateCode (ActualArithmeticGraph.eval universalExpr (ActualCheckExpression.eval u p a b) t 0 0) w 0 0 := by
  rw [gen_expr,GEN_value]

#print axioms gen_expr
#print axioms GEN_expr_value
end M6.PA.ActualCommandStepGraph
