module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualCommandJInternal
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.ActualCommandStepGraph
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal ActualHeadGraphs ActualCommandWordGraph ActualCommandLiteralInternal
open M6.Source M6.Source.CommandAtomEncoding M6.Source.ActualCommandMacros
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def discardWord (c : V) : V :=
  InternalTrace.HFSAppend.append (mpCode c ∷ axThenShifts c 0 0 10) (mpCode 0 ∷ 0)

theorem discardWord_value (c t w : V) (hc : c≠0) :
    wordValue (discardWord c) (stateCode t w 0 0)=stateCode 0 w 0 0 := by
  have he : ActualArithmeticGraph.eval implicationExpr t c 0 0≠0 := by
    simp [implication_eq_zero,hc]
  have hu : ActualArithmeticGraph.eval universalExpr c 0 0 0≠0 :=
    ne_of_gt (lt_of_lt_of_le (show (0 : V)<2 by simp) (universal_ge_two c 0))
  have hf : ActualArithmeticGraph.eval implicationExpr
      (ActualArithmeticGraph.eval universalExpr c 0 0 0) 0 0 0≠0 := by
    simp [implication_eq_zero,hu]
  rw [discardWord,word_append,word_cons,word_zero,word_cons,mp_value]
  simp only [zero_add,he,ite_false]
  rw [ax_shift10_value,mp_value]
  simp [hf]

theorem literal_DISCARD_word : literalValue (V := V) (atoms DISCARD)=discardWord (1 : V) := by
  simp only [DISCARD,atoms,List.map_append,List.map_cons,List.map_nil,List.map_replicate,
    List.cons_append,List.nil_append,literal_append,literal_cons,literal_nil,
    ax_atom_numeral,mp_atom_numeral,Nat.cast_zero,Nat.cast_one,axThenShifts,discardWord,
    InternalTrace.HFSAppend.append_adjoin]
  rfl

/-- The exact DISCARD literal resets arbitrary clean top without changing W. -/
theorem DISCARD_value (t w : V) :
    wordValue (literalValue (atoms DISCARD)) (stateCode t w 0 0)=stateCode 0 w 0 0 := by
  rw [literal_DISCARD_word]
  exact discardWord_value 1 t w (by simp)

theorem DISCARD_expr_value (p a b t w : V) :
    wordValue (ActualWordExpression.eval (ActualWordMacros.literal (atoms DISCARD)) p a b)
      (stateCode t w 0 0)=stateCode 0 w 0 0 := by
  rw [literal_expr,DISCARD_value]

#print axioms discardWord_value
#print axioms DISCARD_expr_value
end M6.PA.ActualCommandStepGraph
