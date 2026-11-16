module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualCommandResiduesInternal
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.ActualCommandStepGraph
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal ActualHeadGraphs ActualCommandWordGraph ActualCommandLiteralInternal
open M6.Source M6.Source.CommandAtomEncoding M6.Source.ActualCommandMacros
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem ax_shift9_value (c x y t w d h : V) :
    wordValue (axThenShifts c x y 9) (stateCode t w d h)=
      stateCode (ActualArithmeticGraph.eval rho8Expr (d+x) (h+y) c d)
        (pairValue t w) 0 (ActualArithmeticGraph.eval universalExpr d h 0 0) := by
  have hs := schemaHeads_sparse (d+x) (h+y) c d h
  simp only [schemaHeads,List.forall_mem_cons,List.forall_mem_nil,and_true] at hs
  rcases hs with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  have hg := gate_sparse (d+x) (h+y) c d
  rw [axThenShifts,word_cons,ax_value]
  simp only [literalValue,List.replicate_succ,List.replicate_zero,List.foldr_cons,List.foldr_nil,
    List.cons_append,List.nil_append,schemaHeads,word_cons,word_zero,Nat.cast_zero,
    shift_sparse,hg,sparse_zero,h1,h2,h3,h4,h5,h6,h7,h8,h9]

theorem literal_PUSH_word : literalValue (V := V) (atoms PUSH)=
    InternalTrace.HFSAppend.append (axThenShifts (0 : V) 0 0 9) (mpCode 0 ∷ 0) := by
  simp only [PUSH,D,atoms,List.map_append,List.map_cons,List.map_nil,List.map_replicate,
    List.cons_append,List.nil_append,literal_append,literal_cons,literal_nil,
    ax_atom_numeral,mp_atom_numeral,Nat.cast_zero,axThenShifts,InternalTrace.HFSAppend.append_adjoin]
  rfl

/-- Actual PUSH saves arbitrary T and clears both caches uniformly. -/
theorem PUSH_value (t w d h : V) :
    wordValue (literalValue (atoms PUSH)) (stateCode t w d h)=stateCode 0 (pairValue t w) 0 0 := by
  rw [literal_PUSH_word,word_append,ax_shift9_value,word_cons,word_zero,mp_value]
  simp [implication_ne_universal]

theorem PUSH_expr_value (p a b t w d h : V) :
    wordValue (ActualWordExpression.eval (ActualWordMacros.literal (atoms PUSH)) p a b)
      (stateCode t w d h)=stateCode 0 (pairValue t w) 0 0 := by
  rw [literal_expr,PUSH_value]

#print axioms PUSH_value
#print axioms PUSH_expr_value
end M6.PA.ActualCommandStepGraph
