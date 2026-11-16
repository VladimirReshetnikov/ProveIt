module
public import PA196.Arithmetic.WordAlgebra
@[expose] public section

namespace PA196.Arithmetic.CommandStep
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open M6.PA M6.PA.SourceCantorInternal HeadGraphs CommandWord LiteralWords VectorAppend Commands
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def selectedHeadWord (j : Nat) (D H A : V) : V :=
  append (append (literalValue (atoms discard)) (axThenShifts A D H (j + 1)))
    (literalValue (atoms (pops (8 - j))))

theorem selectedHead_expr (j : Nat) (D H A : WordExpression.Scalar) (p t d : V) :
    WordExpression.eval (WordMacros.head j D H A) p t d =
      selectedHeadWord j (Scalar.eval D p t d) (Scalar.eval H p t d) (Scalar.eval A p t d) := by
  simp [WordMacros.head, WordExpression.eval, literal_expr, eval_ax_atom,
    selectedHeadWord, axThenShifts, atoms, atom]

theorem ax_select1_value (D H A w : V) :
    wordValue (axThenShifts A D H 2) (stateCode 0 w 0 0) =
      stateCode (ActualArithmeticGraph.eval head6Expr D A H 0) (([(ActualArithmeticGraph.eval head4Expr D A H 0), (ActualArithmeticGraph.eval head3Expr D A H 0), (ActualArithmeticGraph.eval head2Expr D A H 0), (ActualArithmeticGraph.eval head1Expr D H 0 0), (ActualArithmeticGraph.eval rho8Expr D A H 0), (ActualArithmeticGraph.eval universalExpr (0 : V) 0 0 0)] ++ [0]).foldr pairValue w) 0 (ActualArithmeticGraph.eval head5Expr D H 0 0) := by
  have hs := schemaHeads_sparse D H A (0 : V) 0
  simp only [schemaHeads, List.forall_mem_cons, List.forall_mem_nil, and_true] at hs
  rcases hs with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  have hg := gate_sparse H D A (0 : V)
  rw [axThenShifts, word_cons, ax_value]
  simp only [zero_add, literalValue, List.replicate_succ, List.replicate_zero,
    List.foldr_cons, List.foldr_nil, List.cons_append, List.nil_append,
    schemaHeads, word_cons, word_zero, Nat.cast_zero, shift_sparse, hg,
    sparse_zero, h1,h2,h3,h4,h5,h6,h7,h8]

theorem selectedHead1_value (D H A t w : V) :
    wordValue (selectedHeadWord 1 D H A) (stateCode t w 0 0) =
      stateCode (ActualArithmeticGraph.eval head6Expr D A H 0) w 0 0 := by
  rw [selectedHeadWord, word_append, word_append, discard_value, ax_select1_value]
  simpa only [List.length_cons, List.length_nil] using
    pops_stack_value ([(ActualArithmeticGraph.eval head4Expr D A H 0), (ActualArithmeticGraph.eval head3Expr D A H 0), (ActualArithmeticGraph.eval head2Expr D A H 0), (ActualArithmeticGraph.eval head1Expr D H 0 0), (ActualArithmeticGraph.eval rho8Expr D A H 0), (ActualArithmeticGraph.eval universalExpr (0 : V) 0 0 0)] : List V) (ActualArithmeticGraph.eval head6Expr D A H 0) 0 w 0 (ActualArithmeticGraph.eval head5Expr D H 0 0)

theorem ax_select2_value (D H A w : V) :
    wordValue (axThenShifts A D H 3) (stateCode 0 w 0 0) =
      stateCode (ActualArithmeticGraph.eval head5Expr D H 0 0) (([(ActualArithmeticGraph.eval head3Expr D A H 0), (ActualArithmeticGraph.eval head2Expr D A H 0), (ActualArithmeticGraph.eval head1Expr D H 0 0), (ActualArithmeticGraph.eval rho8Expr D A H 0), (ActualArithmeticGraph.eval universalExpr (0 : V) 0 0 0)] ++ [0]).foldr pairValue w) 0 (ActualArithmeticGraph.eval head4Expr D A H 0) := by
  have hs := schemaHeads_sparse D H A (0 : V) 0
  simp only [schemaHeads, List.forall_mem_cons, List.forall_mem_nil, and_true] at hs
  rcases hs with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  have hg := gate_sparse H D A (0 : V)
  rw [axThenShifts, word_cons, ax_value]
  simp only [zero_add, literalValue, List.replicate_succ, List.replicate_zero,
    List.foldr_cons, List.foldr_nil, List.cons_append, List.nil_append,
    schemaHeads, word_cons, word_zero, Nat.cast_zero, shift_sparse, hg,
    sparse_zero, h1,h2,h3,h4,h5,h6,h7,h8]

theorem selectedHead2_value (D H A t w : V) :
    wordValue (selectedHeadWord 2 D H A) (stateCode t w 0 0) =
      stateCode (ActualArithmeticGraph.eval head5Expr D H 0 0) w 0 0 := by
  rw [selectedHeadWord, word_append, word_append, discard_value, ax_select2_value]
  simpa only [List.length_cons, List.length_nil] using
    pops_stack_value ([(ActualArithmeticGraph.eval head3Expr D A H 0), (ActualArithmeticGraph.eval head2Expr D A H 0), (ActualArithmeticGraph.eval head1Expr D H 0 0), (ActualArithmeticGraph.eval rho8Expr D A H 0), (ActualArithmeticGraph.eval universalExpr (0 : V) 0 0 0)] : List V) (ActualArithmeticGraph.eval head5Expr D H 0 0) 0 w 0 (ActualArithmeticGraph.eval head4Expr D A H 0)

theorem ax_select3_value (D H A w : V) :
    wordValue (axThenShifts A D H 4) (stateCode 0 w 0 0) =
      stateCode (ActualArithmeticGraph.eval head4Expr D A H 0) (([(ActualArithmeticGraph.eval head2Expr D A H 0), (ActualArithmeticGraph.eval head1Expr D H 0 0), (ActualArithmeticGraph.eval rho8Expr D A H 0), (ActualArithmeticGraph.eval universalExpr (0 : V) 0 0 0)] ++ [0]).foldr pairValue w) 0 (ActualArithmeticGraph.eval head3Expr D A H 0) := by
  have hs := schemaHeads_sparse D H A (0 : V) 0
  simp only [schemaHeads, List.forall_mem_cons, List.forall_mem_nil, and_true] at hs
  rcases hs with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  have hg := gate_sparse H D A (0 : V)
  rw [axThenShifts, word_cons, ax_value]
  simp only [zero_add, literalValue, List.replicate_succ, List.replicate_zero,
    List.foldr_cons, List.foldr_nil, List.cons_append, List.nil_append,
    schemaHeads, word_cons, word_zero, Nat.cast_zero, shift_sparse, hg,
    sparse_zero, h1,h2,h3,h4,h5,h6,h7,h8]

theorem selectedHead3_value (D H A t w : V) :
    wordValue (selectedHeadWord 3 D H A) (stateCode t w 0 0) =
      stateCode (ActualArithmeticGraph.eval head4Expr D A H 0) w 0 0 := by
  rw [selectedHeadWord, word_append, word_append, discard_value, ax_select3_value]
  simpa only [List.length_cons, List.length_nil] using
    pops_stack_value ([(ActualArithmeticGraph.eval head2Expr D A H 0), (ActualArithmeticGraph.eval head1Expr D H 0 0), (ActualArithmeticGraph.eval rho8Expr D A H 0), (ActualArithmeticGraph.eval universalExpr (0 : V) 0 0 0)] : List V) (ActualArithmeticGraph.eval head4Expr D A H 0) 0 w 0 (ActualArithmeticGraph.eval head3Expr D A H 0)

theorem ax_select4_value (D H A w : V) :
    wordValue (axThenShifts A D H 5) (stateCode 0 w 0 0) =
      stateCode (ActualArithmeticGraph.eval head3Expr D A H 0) (([(ActualArithmeticGraph.eval head1Expr D H 0 0), (ActualArithmeticGraph.eval rho8Expr D A H 0), (ActualArithmeticGraph.eval universalExpr (0 : V) 0 0 0)] ++ [0]).foldr pairValue w) 0 (ActualArithmeticGraph.eval head2Expr D A H 0) := by
  have hs := schemaHeads_sparse D H A (0 : V) 0
  simp only [schemaHeads, List.forall_mem_cons, List.forall_mem_nil, and_true] at hs
  rcases hs with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  have hg := gate_sparse H D A (0 : V)
  rw [axThenShifts, word_cons, ax_value]
  simp only [zero_add, literalValue, List.replicate_succ, List.replicate_zero,
    List.foldr_cons, List.foldr_nil, List.cons_append, List.nil_append,
    schemaHeads, word_cons, word_zero, Nat.cast_zero, shift_sparse, hg,
    sparse_zero, h1,h2,h3,h4,h5,h6,h7,h8]

theorem selectedHead4_value (D H A t w : V) :
    wordValue (selectedHeadWord 4 D H A) (stateCode t w 0 0) =
      stateCode (ActualArithmeticGraph.eval head3Expr D A H 0) w 0 0 := by
  rw [selectedHeadWord, word_append, word_append, discard_value, ax_select4_value]
  simpa only [List.length_cons, List.length_nil] using
    pops_stack_value ([(ActualArithmeticGraph.eval head1Expr D H 0 0), (ActualArithmeticGraph.eval rho8Expr D A H 0), (ActualArithmeticGraph.eval universalExpr (0 : V) 0 0 0)] : List V) (ActualArithmeticGraph.eval head3Expr D A H 0) 0 w 0 (ActualArithmeticGraph.eval head2Expr D A H 0)

theorem ax_select5_value (D H A w : V) :
    wordValue (axThenShifts A D H 6) (stateCode 0 w 0 0) =
      stateCode (ActualArithmeticGraph.eval head2Expr D A H 0) (([(ActualArithmeticGraph.eval rho8Expr D A H 0), (ActualArithmeticGraph.eval universalExpr (0 : V) 0 0 0)] ++ [0]).foldr pairValue w) 0 (ActualArithmeticGraph.eval head1Expr D H 0 0) := by
  have hs := schemaHeads_sparse D H A (0 : V) 0
  simp only [schemaHeads, List.forall_mem_cons, List.forall_mem_nil, and_true] at hs
  rcases hs with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  have hg := gate_sparse H D A (0 : V)
  rw [axThenShifts, word_cons, ax_value]
  simp only [zero_add, literalValue, List.replicate_succ, List.replicate_zero,
    List.foldr_cons, List.foldr_nil, List.cons_append, List.nil_append,
    schemaHeads, word_cons, word_zero, Nat.cast_zero, shift_sparse, hg,
    sparse_zero, h1,h2,h3,h4,h5,h6,h7,h8]

theorem selectedHead5_value (D H A t w : V) :
    wordValue (selectedHeadWord 5 D H A) (stateCode t w 0 0) =
      stateCode (ActualArithmeticGraph.eval head2Expr D A H 0) w 0 0 := by
  rw [selectedHeadWord, word_append, word_append, discard_value, ax_select5_value]
  simpa only [List.length_cons, List.length_nil] using
    pops_stack_value ([(ActualArithmeticGraph.eval rho8Expr D A H 0), (ActualArithmeticGraph.eval universalExpr (0 : V) 0 0 0)] : List V) (ActualArithmeticGraph.eval head2Expr D A H 0) 0 w 0 (ActualArithmeticGraph.eval head1Expr D H 0 0)

theorem ax_select6_value (D H A w : V) :
    wordValue (axThenShifts A D H 7) (stateCode 0 w 0 0) =
      stateCode (ActualArithmeticGraph.eval head1Expr D H 0 0) (([(ActualArithmeticGraph.eval universalExpr (0 : V) 0 0 0)] ++ [0]).foldr pairValue w) 0 (ActualArithmeticGraph.eval rho8Expr D A H 0) := by
  have hs := schemaHeads_sparse D H A (0 : V) 0
  simp only [schemaHeads, List.forall_mem_cons, List.forall_mem_nil, and_true] at hs
  rcases hs with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  have hg := gate_sparse H D A (0 : V)
  rw [axThenShifts, word_cons, ax_value]
  simp only [zero_add, literalValue, List.replicate_succ, List.replicate_zero,
    List.foldr_cons, List.foldr_nil, List.cons_append, List.nil_append,
    schemaHeads, word_cons, word_zero, Nat.cast_zero, shift_sparse, hg,
    sparse_zero, h1,h2,h3,h4,h5,h6,h7,h8]

theorem selectedHead6_value (D H A t w : V) :
    wordValue (selectedHeadWord 6 D H A) (stateCode t w 0 0) =
      stateCode (ActualArithmeticGraph.eval head1Expr D H 0 0) w 0 0 := by
  rw [selectedHeadWord, word_append, word_append, discard_value, ax_select6_value]
  simpa only [List.length_cons, List.length_nil] using
    pops_stack_value ([(ActualArithmeticGraph.eval universalExpr (0 : V) 0 0 0)] : List V) (ActualArithmeticGraph.eval head1Expr D H 0 0) 0 w 0 (ActualArithmeticGraph.eval rho8Expr D A H 0)

noncomputable def rho8Word (a b c u : V) : V :=
  append (append (append (literalValue (atoms discard)) (offsetWord u))
    (axThenShifts b (a - u) c 8)) (literalValue (atoms pop))

theorem rho8_expr (a b c u : WordExpression.Scalar) (p t d : V) :
    WordExpression.eval (WordMacros.rho8 a b c u) p t d =
      rho8Word (Scalar.eval a p t d) (Scalar.eval b p t d)
        (Scalar.eval c p t d) (Scalar.eval u p t d) := by
  simp [WordMacros.rho8, WordExpression.eval, literal_expr, eval_ax_atom,
    offset_expr, rho8Word, axThenShifts, atoms, atom, Scalar.eval]

theorem rho8Word_value (a b c u t w : V) (hu : u ≤ a) :
    wordValue (rho8Word a b c u) (stateCode t w 0 0) =
      stateCode (ActualArithmeticGraph.eval rho8Expr a b c u) w 0 0 := by
  rw [rho8Word, word_append, word_append, word_append, discard_value,
    offset_value, ax_shift8_value, pop_value]
  simp [add_tsub_cancel_of_le hu]

noncomputable def gateWord (a b c : V) : V :=
  append (append (literalValue (atoms discard)) (axCode c b a ∷ 0))
    (literalValue (atoms (pops 9)))

theorem gate_expr (a b c : WordExpression.Scalar) (p t d : V) :
    WordExpression.eval (WordMacros.gate a b c) p t d =
      gateWord (Scalar.eval a p t d) (Scalar.eval b p t d) (Scalar.eval c p t d) := by
  simp [WordMacros.gate, WordMacros.singleton, WordExpression.eval,
    literal_expr, eval_ax_atom, gateWord]

theorem gateWord_value (a b c t w : V) :
    wordValue (gateWord a b c) (stateCode t w 0 0) =
      stateCode (gateValue a b c 0) w 0 0 := by
  rw [gateWord, word_append, word_append, discard_value, word_cons, word_zero, ax_value]
  simp only [zero_add]
  simpa only [schemaHeads, List.length_cons, List.length_nil] using
    pops_stack_value (schemaHeads b a c 0 0) (gateValue a b c 0) 0 w 0 0

theorem gen_expr (u : WordExpression.Scalar) (p t d : V) :
    WordExpression.eval (WordMacros.gen u) p t d = genWord (Scalar.eval u p t d) := by
  simp [WordMacros.gen, WordExpression.eval, literal_expr, eval_ax_atom,
    offset_expr, genWord, axThenShifts, atoms, atom, Scalar.eval]

theorem mp_expr (b : WordExpression.Scalar) (p t d : V) :
    WordExpression.eval (WordMacros.mp b) p t d = mpWord (Scalar.eval b p t d) := by
  simp [WordMacros.mp, WordMacros.singleton, WordExpression.eval, literal_expr,
    eval_mp_atom, eval_ax_atom, mpWord, axThenShifts, atoms, atom, Scalar.eval]

#print axioms selectedHead1_value
#print axioms selectedHead6_value
#print axioms rho8Word_value
#print axioms gateWord_value
end PA196.Arithmetic.CommandStep
