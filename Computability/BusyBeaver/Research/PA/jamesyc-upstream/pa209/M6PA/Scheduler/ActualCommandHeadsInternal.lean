module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualCommandGateEightInternal
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.ActualCommandStepGraph
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal ActualHeadGraphs ActualCommandWordGraph ActualCommandLiteralInternal
open M6.Source M6.Source.CommandAtomEncoding M6.Source.ActualCommandMacros
open InternalTrace.HFSAppend
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def selectedHeadWord (k : Nat) (a b c : V) : V :=
  append (append (literalValue (atoms DISCARD)) (axThenShifts c a b (k+1)))
    (literalValue (atoms (popHeads (9-k))))
attribute [local irreducible] ActualWordMacros.literal ActualWordMacros.axAtom

theorem selectedHead_expr (k : Nat) (a b c : ActualWordExpression.Scalar) (p t d : V) :
    ActualWordExpression.eval (ActualWordMacros.head k a b c) p t d =
      selectedHeadWord k (ActualCheckExpression.eval a p t d)
        (ActualCheckExpression.eval b p t d) (ActualCheckExpression.eval c p t d) := by
  simp [ActualWordMacros.head,ActualWordExpression.eval,literal_expr,eval_ax_atom,
    selectedHeadWord,axThenShifts,atoms,atom,Enumeration.encodeCommand,
    show Cantor.pair 0 0=0 from rfl]

 theorem ax_select1_value (a b c w : V) :
    wordValue (axThenShifts c a b 2) (stateCode 0 w 0 0) =
      stateCode (ActualArithmeticGraph.eval rho1Expr a b c 0) (([(ActualArithmeticGraph.eval rho3Expr a b c 0), (ActualArithmeticGraph.eval rho4Expr a b c 0), (ActualArithmeticGraph.eval rho5Expr a b c 0), (ActualArithmeticGraph.eval rho6Expr a b c 0), (ActualArithmeticGraph.eval rho7Expr a b c 0), (ActualArithmeticGraph.eval rho8Expr a b c 0), (ActualArithmeticGraph.eval universalExpr (0:V) 0 0 0)] ++ [0]).foldr pairValue w) 0 (ActualArithmeticGraph.eval rho2Expr a b c 0) := by
  have hs := schemaHeads_sparse a b c (0:V) 0
  simp only [schemaHeads,List.forall_mem_cons,List.forall_mem_nil,and_true] at hs
  rcases hs with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  have hg := gate_sparse a b c (0:V)
  rw [axThenShifts,word_cons,ax_value]
  simp only [zero_add,literalValue,List.replicate_succ,List.replicate_zero,List.foldr_cons,List.foldr_nil,
    List.cons_append,List.nil_append,schemaHeads,word_cons,word_zero,Nat.cast_zero,
    shift_sparse,hg,sparse_zero,h1,h2,h3,h4,h5,h6,h7,h8,h9]

 theorem selectedHead1_value (a b c t w : V) :
    wordValue (selectedHeadWord 1 a b c) (stateCode t w 0 0) =
      stateCode (ActualArithmeticGraph.eval rho1Expr a b c 0) w 0 0 := by
  rw [selectedHeadWord,word_append,word_append,DISCARD_value,ax_select1_value]
  simpa only [List.length_cons,List.length_nil] using
    popHeads_stack_value ([(ActualArithmeticGraph.eval rho3Expr a b c 0), (ActualArithmeticGraph.eval rho4Expr a b c 0), (ActualArithmeticGraph.eval rho5Expr a b c 0), (ActualArithmeticGraph.eval rho6Expr a b c 0), (ActualArithmeticGraph.eval rho7Expr a b c 0), (ActualArithmeticGraph.eval rho8Expr a b c 0), (ActualArithmeticGraph.eval universalExpr (0:V) 0 0 0)] : List V) (ActualArithmeticGraph.eval rho1Expr a b c 0) 0 w 0 (ActualArithmeticGraph.eval rho2Expr a b c 0)
#print axioms selectedHead1_value

 theorem ax_select2_value (a b c w : V) :
    wordValue (axThenShifts c a b 3) (stateCode 0 w 0 0) =
      stateCode (ActualArithmeticGraph.eval rho2Expr a b c 0) (([(ActualArithmeticGraph.eval rho4Expr a b c 0), (ActualArithmeticGraph.eval rho5Expr a b c 0), (ActualArithmeticGraph.eval rho6Expr a b c 0), (ActualArithmeticGraph.eval rho7Expr a b c 0), (ActualArithmeticGraph.eval rho8Expr a b c 0), (ActualArithmeticGraph.eval universalExpr (0:V) 0 0 0)] ++ [0]).foldr pairValue w) 0 (ActualArithmeticGraph.eval rho3Expr a b c 0) := by
  have hs := schemaHeads_sparse a b c (0:V) 0
  simp only [schemaHeads,List.forall_mem_cons,List.forall_mem_nil,and_true] at hs
  rcases hs with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  have hg := gate_sparse a b c (0:V)
  rw [axThenShifts,word_cons,ax_value]
  simp only [zero_add,literalValue,List.replicate_succ,List.replicate_zero,List.foldr_cons,List.foldr_nil,
    List.cons_append,List.nil_append,schemaHeads,word_cons,word_zero,Nat.cast_zero,
    shift_sparse,hg,sparse_zero,h1,h2,h3,h4,h5,h6,h7,h8,h9]

 theorem selectedHead2_value (a b c t w : V) :
    wordValue (selectedHeadWord 2 a b c) (stateCode t w 0 0) =
      stateCode (ActualArithmeticGraph.eval rho2Expr a b c 0) w 0 0 := by
  rw [selectedHeadWord,word_append,word_append,DISCARD_value,ax_select2_value]
  simpa only [List.length_cons,List.length_nil] using
    popHeads_stack_value ([(ActualArithmeticGraph.eval rho4Expr a b c 0), (ActualArithmeticGraph.eval rho5Expr a b c 0), (ActualArithmeticGraph.eval rho6Expr a b c 0), (ActualArithmeticGraph.eval rho7Expr a b c 0), (ActualArithmeticGraph.eval rho8Expr a b c 0), (ActualArithmeticGraph.eval universalExpr (0:V) 0 0 0)] : List V) (ActualArithmeticGraph.eval rho2Expr a b c 0) 0 w 0 (ActualArithmeticGraph.eval rho3Expr a b c 0)
#print axioms selectedHead2_value

 theorem ax_select3_value (a b c w : V) :
    wordValue (axThenShifts c a b 4) (stateCode 0 w 0 0) =
      stateCode (ActualArithmeticGraph.eval rho3Expr a b c 0) (([(ActualArithmeticGraph.eval rho5Expr a b c 0), (ActualArithmeticGraph.eval rho6Expr a b c 0), (ActualArithmeticGraph.eval rho7Expr a b c 0), (ActualArithmeticGraph.eval rho8Expr a b c 0), (ActualArithmeticGraph.eval universalExpr (0:V) 0 0 0)] ++ [0]).foldr pairValue w) 0 (ActualArithmeticGraph.eval rho4Expr a b c 0) := by
  have hs := schemaHeads_sparse a b c (0:V) 0
  simp only [schemaHeads,List.forall_mem_cons,List.forall_mem_nil,and_true] at hs
  rcases hs with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  have hg := gate_sparse a b c (0:V)
  rw [axThenShifts,word_cons,ax_value]
  simp only [zero_add,literalValue,List.replicate_succ,List.replicate_zero,List.foldr_cons,List.foldr_nil,
    List.cons_append,List.nil_append,schemaHeads,word_cons,word_zero,Nat.cast_zero,
    shift_sparse,hg,sparse_zero,h1,h2,h3,h4,h5,h6,h7,h8,h9]

 theorem selectedHead3_value (a b c t w : V) :
    wordValue (selectedHeadWord 3 a b c) (stateCode t w 0 0) =
      stateCode (ActualArithmeticGraph.eval rho3Expr a b c 0) w 0 0 := by
  rw [selectedHeadWord,word_append,word_append,DISCARD_value,ax_select3_value]
  simpa only [List.length_cons,List.length_nil] using
    popHeads_stack_value ([(ActualArithmeticGraph.eval rho5Expr a b c 0), (ActualArithmeticGraph.eval rho6Expr a b c 0), (ActualArithmeticGraph.eval rho7Expr a b c 0), (ActualArithmeticGraph.eval rho8Expr a b c 0), (ActualArithmeticGraph.eval universalExpr (0:V) 0 0 0)] : List V) (ActualArithmeticGraph.eval rho3Expr a b c 0) 0 w 0 (ActualArithmeticGraph.eval rho4Expr a b c 0)
#print axioms selectedHead3_value

 theorem ax_select4_value (a b c w : V) :
    wordValue (axThenShifts c a b 5) (stateCode 0 w 0 0) =
      stateCode (ActualArithmeticGraph.eval rho4Expr a b c 0) (([(ActualArithmeticGraph.eval rho6Expr a b c 0), (ActualArithmeticGraph.eval rho7Expr a b c 0), (ActualArithmeticGraph.eval rho8Expr a b c 0), (ActualArithmeticGraph.eval universalExpr (0:V) 0 0 0)] ++ [0]).foldr pairValue w) 0 (ActualArithmeticGraph.eval rho5Expr a b c 0) := by
  have hs := schemaHeads_sparse a b c (0:V) 0
  simp only [schemaHeads,List.forall_mem_cons,List.forall_mem_nil,and_true] at hs
  rcases hs with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  have hg := gate_sparse a b c (0:V)
  rw [axThenShifts,word_cons,ax_value]
  simp only [zero_add,literalValue,List.replicate_succ,List.replicate_zero,List.foldr_cons,List.foldr_nil,
    List.cons_append,List.nil_append,schemaHeads,word_cons,word_zero,Nat.cast_zero,
    shift_sparse,hg,sparse_zero,h1,h2,h3,h4,h5,h6,h7,h8,h9]

 theorem selectedHead4_value (a b c t w : V) :
    wordValue (selectedHeadWord 4 a b c) (stateCode t w 0 0) =
      stateCode (ActualArithmeticGraph.eval rho4Expr a b c 0) w 0 0 := by
  rw [selectedHeadWord,word_append,word_append,DISCARD_value,ax_select4_value]
  simpa only [List.length_cons,List.length_nil] using
    popHeads_stack_value ([(ActualArithmeticGraph.eval rho6Expr a b c 0), (ActualArithmeticGraph.eval rho7Expr a b c 0), (ActualArithmeticGraph.eval rho8Expr a b c 0), (ActualArithmeticGraph.eval universalExpr (0:V) 0 0 0)] : List V) (ActualArithmeticGraph.eval rho4Expr a b c 0) 0 w 0 (ActualArithmeticGraph.eval rho5Expr a b c 0)
#print axioms selectedHead4_value

 theorem ax_select5_value (a b c w : V) :
    wordValue (axThenShifts c a b 6) (stateCode 0 w 0 0) =
      stateCode (ActualArithmeticGraph.eval rho5Expr a b c 0) (([(ActualArithmeticGraph.eval rho7Expr a b c 0), (ActualArithmeticGraph.eval rho8Expr a b c 0), (ActualArithmeticGraph.eval universalExpr (0:V) 0 0 0)] ++ [0]).foldr pairValue w) 0 (ActualArithmeticGraph.eval rho6Expr a b c 0) := by
  have hs := schemaHeads_sparse a b c (0:V) 0
  simp only [schemaHeads,List.forall_mem_cons,List.forall_mem_nil,and_true] at hs
  rcases hs with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  have hg := gate_sparse a b c (0:V)
  rw [axThenShifts,word_cons,ax_value]
  simp only [zero_add,literalValue,List.replicate_succ,List.replicate_zero,List.foldr_cons,List.foldr_nil,
    List.cons_append,List.nil_append,schemaHeads,word_cons,word_zero,Nat.cast_zero,
    shift_sparse,hg,sparse_zero,h1,h2,h3,h4,h5,h6,h7,h8,h9]

 theorem selectedHead5_value (a b c t w : V) :
    wordValue (selectedHeadWord 5 a b c) (stateCode t w 0 0) =
      stateCode (ActualArithmeticGraph.eval rho5Expr a b c 0) w 0 0 := by
  rw [selectedHeadWord,word_append,word_append,DISCARD_value,ax_select5_value]
  simpa only [List.length_cons,List.length_nil] using
    popHeads_stack_value ([(ActualArithmeticGraph.eval rho7Expr a b c 0), (ActualArithmeticGraph.eval rho8Expr a b c 0), (ActualArithmeticGraph.eval universalExpr (0:V) 0 0 0)] : List V) (ActualArithmeticGraph.eval rho5Expr a b c 0) 0 w 0 (ActualArithmeticGraph.eval rho6Expr a b c 0)
#print axioms selectedHead5_value

 theorem ax_select6_value (a b c w : V) :
    wordValue (axThenShifts c a b 7) (stateCode 0 w 0 0) =
      stateCode (ActualArithmeticGraph.eval rho6Expr a b c 0) (([(ActualArithmeticGraph.eval rho8Expr a b c 0), (ActualArithmeticGraph.eval universalExpr (0:V) 0 0 0)] ++ [0]).foldr pairValue w) 0 (ActualArithmeticGraph.eval rho7Expr a b c 0) := by
  have hs := schemaHeads_sparse a b c (0:V) 0
  simp only [schemaHeads,List.forall_mem_cons,List.forall_mem_nil,and_true] at hs
  rcases hs with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  have hg := gate_sparse a b c (0:V)
  rw [axThenShifts,word_cons,ax_value]
  simp only [zero_add,literalValue,List.replicate_succ,List.replicate_zero,List.foldr_cons,List.foldr_nil,
    List.cons_append,List.nil_append,schemaHeads,word_cons,word_zero,Nat.cast_zero,
    shift_sparse,hg,sparse_zero,h1,h2,h3,h4,h5,h6,h7,h8,h9]

 theorem selectedHead6_value (a b c t w : V) :
    wordValue (selectedHeadWord 6 a b c) (stateCode t w 0 0) =
      stateCode (ActualArithmeticGraph.eval rho6Expr a b c 0) w 0 0 := by
  rw [selectedHeadWord,word_append,word_append,DISCARD_value,ax_select6_value]
  simpa only [List.length_cons,List.length_nil] using
    popHeads_stack_value ([(ActualArithmeticGraph.eval rho8Expr a b c 0), (ActualArithmeticGraph.eval universalExpr (0:V) 0 0 0)] : List V) (ActualArithmeticGraph.eval rho6Expr a b c 0) 0 w 0 (ActualArithmeticGraph.eval rho7Expr a b c 0)
#print axioms selectedHead6_value

 theorem ax_select7_value (a b c w : V) :
    wordValue (axThenShifts c a b 8) (stateCode 0 w 0 0) =
      stateCode (ActualArithmeticGraph.eval rho7Expr a b c 0) (([(ActualArithmeticGraph.eval universalExpr (0:V) 0 0 0)] ++ [0]).foldr pairValue w) 0 (ActualArithmeticGraph.eval rho8Expr a b c 0) := by
  have hs := schemaHeads_sparse a b c (0:V) 0
  simp only [schemaHeads,List.forall_mem_cons,List.forall_mem_nil,and_true] at hs
  rcases hs with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  have hg := gate_sparse a b c (0:V)
  rw [axThenShifts,word_cons,ax_value]
  simp only [zero_add,literalValue,List.replicate_succ,List.replicate_zero,List.foldr_cons,List.foldr_nil,
    List.cons_append,List.nil_append,schemaHeads,word_cons,word_zero,Nat.cast_zero,
    shift_sparse,hg,sparse_zero,h1,h2,h3,h4,h5,h6,h7,h8,h9]

 theorem selectedHead7_value (a b c t w : V) :
    wordValue (selectedHeadWord 7 a b c) (stateCode t w 0 0) =
      stateCode (ActualArithmeticGraph.eval rho7Expr a b c 0) w 0 0 := by
  rw [selectedHeadWord,word_append,word_append,DISCARD_value,ax_select7_value]
  simpa only [List.length_cons,List.length_nil] using
    popHeads_stack_value ([(ActualArithmeticGraph.eval universalExpr (0:V) 0 0 0)] : List V) (ActualArithmeticGraph.eval rho7Expr a b c 0) 0 w 0 (ActualArithmeticGraph.eval rho8Expr a b c 0)
#print axioms selectedHead7_value
end M6.PA.ActualCommandStepGraph

