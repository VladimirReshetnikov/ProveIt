module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualCommandPopInternal
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.ActualCommandStepGraph
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal ActualHeadGraphs ActualCommandWordGraph ActualCommandLiteralInternal
open M6.Source M6.Source.CommandAtomEncoding M6.Source.ActualCommandMacros
open InternalTrace.HFSAppend
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def gateCodeWord (a b c : V) : V :=
  append (append (literalValue (atoms DISCARD)) (axCode c a b ∷ 0))
    (literalValue (atoms (popHeads 10)))
noncomputable def headEightWord (a b c u : V) : V :=
  append (append (append (literalValue (atoms DISCARD)) (jWord u))
    (axThenShifts c (a-u) b 9)) (literalValue (atoms H))

attribute [local irreducible] literalValue popHeads ActualWordMacros.literal ActualWordMacros.j ActualWordMacros.axAtom axThenShifts

theorem gate_expr (a b c : ActualWordExpression.Scalar) (p t d : V) :
    ActualWordExpression.eval (ActualWordMacros.gate a b c) p t d=
      gateCodeWord (ActualCheckExpression.eval a p t d) (ActualCheckExpression.eval b p t d)
        (ActualCheckExpression.eval c p t d) := by
  simp [ActualWordMacros.gate,ActualWordMacros.singleton,ActualWordExpression.eval,
    literal_expr,eval_ax_atom,gateCodeWord]

theorem gateWord_value (a b c t w : V) :
    wordValue (gateCodeWord a b c) (stateCode t w 0 0)=stateCode (gateValue a b c 0) w 0 0 := by
  rw [gateCodeWord,word_append,word_append,DISCARD_value,word_cons,word_zero,ax_value]
  simp only [zero_add]
  simpa only [schemaHeads,List.length_cons,List.length_nil] using
    popHeads_stack_value (schemaHeads a b c 0 0) (gateValue a b c 0) 0 w 0 0

theorem head8_expr (a b c u : ActualWordExpression.Scalar) (p t d : V) :
    ActualWordExpression.eval (ActualWordMacros.head8 a b c u) p t d=
      headEightWord (ActualCheckExpression.eval a p t d) (ActualCheckExpression.eval b p t d)
        (ActualCheckExpression.eval c p t d) (ActualCheckExpression.eval u p t d) := by
  simp [ActualWordMacros.head8,ActualWordExpression.eval,j_expr,literal_expr,eval_ax_atom,
    ActualCheckExpression.eval,headEightWord,axThenShifts,atoms,List.map_replicate,atom,Enumeration.encodeCommand,
    show Cantor.pair 0 0=0 from rfl]

theorem headEight_value (a b c u t w : V) (hu : u≤a) :
    wordValue (headEightWord a b c u) (stateCode t w 0 0)=
      stateCode (ActualArithmeticGraph.eval rho8Expr a b c u) w 0 0 := by
  rw [headEightWord,word_append,word_append,word_append,DISCARD_value,J_value,ax_shift9_value,H_value]
  simp [add_tsub_self_of_le hu]

#print axioms gateWord_value
#print axioms headEight_value
end M6.PA.ActualCommandStepGraph

