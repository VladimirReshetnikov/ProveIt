module
public import PA196.Arithmetic.LiteralWords
public import PA196.Arithmetic.Residues
@[expose] public section

/-! The nine-item command-word algebra in arbitrary IΣ₁ models. All register
and formula parameters below may be nonstandard model elements. -/
namespace PA196.Arithmetic.CommandStep
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open M6.PA M6.PA.SourceCantorInternal HeadGraphs CommandWord LiteralWords VectorAppend
open Commands
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem source_left_pair (a b : V) : decodeLeft (pairValue a b) = a := (decode_pairValue a b).1
@[simp] theorem source_right_pair (a b : V) : decodeRight (pairValue a b) = b := (decode_pairValue a b).2
@[simp] theorem sparse_zero : Sparse (0 : V) := Or.inl rfl

theorem shift_sparse (t x w d h : V) (ht : Sparse t) (hh : Sparse h) :
    stepValue 0 (stateCode t (pairValue x w) d h) = stateCode h w d x := by
  rw [shift_value, ite_eq_right (sparse_add_ne_one ht hh)]
  simp only [source_left_pair, source_right_pair]

noncomputable def axThenShifts (c x y : V) (n : Nat) : V :=
  axCode c x y ∷ literalValue (List.replicate n 0)

theorem ax_shift8_value (c x y t w d h : V) :
    wordValue (axThenShifts c x y 8) (stateCode t w d h) =
      stateCode (ActualArithmeticGraph.eval rho8Expr (d + x) c (h + y) d)
        (pairValue t w) 0 (ActualArithmeticGraph.eval universalExpr d h 0 0) := by
  have hs := schemaHeads_sparse (d + x) (h + y) c d h
  simp only [schemaHeads, List.forall_mem_cons, List.forall_mem_nil, and_true] at hs
  rcases hs with ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hg := gate_sparse (h + y) (d + x) c d
  rw [axThenShifts, word_cons, ax_value]
  simp only [literalValue, List.replicate_succ, List.replicate_zero, List.foldr_cons,
    List.foldr_nil, List.cons_append, List.nil_append, schemaHeads, word_cons,
    word_zero, Nat.cast_zero, shift_sparse, hg, sparse_zero, h1, h2, h3, h4, h5, h6, h7, h8]

theorem ax_shift9_value (c x y t w d h : V) :
    wordValue (axThenShifts c x y 9) (stateCode t w d h) =
      stateCode (ActualArithmeticGraph.eval universalExpr d h 0 0) w 0 t := by
  have hs := schemaHeads_sparse (d + x) (h + y) c d h
  simp only [schemaHeads, List.forall_mem_cons, List.forall_mem_nil, and_true] at hs
  rcases hs with ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hg := gate_sparse (h + y) (d + x) c d
  rw [axThenShifts, word_cons, ax_value]
  simp only [literalValue, List.replicate_succ, List.replicate_zero, List.foldr_cons,
    List.foldr_nil, List.cons_append, List.nil_append, schemaHeads, word_cons,
    word_zero, Nat.cast_zero, shift_sparse, hg, sparse_zero, h1, h2, h3, h4, h5, h6, h7, h8]

theorem ax_shift_succ (c x y s : V) (n : Nat) :
    wordValue (axThenShifts c x y (n + 1)) s = stepValue 0 (wordValue (axThenShifts c x y n) s) := by
  have hw : axThenShifts c x y (n + 1) = append (axThenShifts c x y n) (0 ∷ (0 : V)) := by
    simp only [axThenShifts, List.replicate_succ', literal_append, literal_cons,
      literal_nil, Nat.cast_zero, append_adjoin]
  rw [hw, word_append, word_cons, word_zero]

theorem ax_shift10_value (c x y t w d h : V) :
    wordValue (axThenShifts c x y 10) (stateCode t w d h) =
      stateCode t (decodeRight w) 0 (decodeLeft w) := by
  rw [show (10 : Nat) = 9 + 1 by decide, ax_shift_succ, ax_shift9_value, shift_value,
    ite_eq_right (universal_add_ne_one d h t)]

theorem literal_pop_word : literalValue (V := V) (atoms Commands.pop) = axThenShifts (0 : V) 0 0 10 := by
  simp only [Commands.pop, atoms, List.map_append, List.map_cons, List.map_nil,
    List.map_replicate, List.cons_append, List.nil_append, literal_cons,
    literal_nil, ax_atom_numeral, Nat.cast_zero, axThenShifts]
  rfl

theorem pop_value (t w d h : V) :
    wordValue (literalValue (atoms Commands.pop)) (stateCode t w d h) =
      stateCode t (decodeRight w) 0 (decodeLeft w) := by
  rw [literal_pop_word, ax_shift10_value]

theorem literal_push_word : literalValue (V := V) (atoms Commands.push) =
    append (axThenShifts (0 : V) 0 0 8) (mpCode 0 ∷ 0) := by
  simp only [Commands.push, atoms, List.map_append, List.map_cons, List.map_nil,
    List.map_replicate, List.cons_append, List.nil_append, literal_append,
    literal_cons, literal_nil, ax_atom_numeral, mp_atom_numeral, Nat.cast_zero,
    axThenShifts, append_adjoin]
  rfl

theorem push_value (t w d h : V) :
    wordValue (literalValue (atoms Commands.push)) (stateCode t w d h) =
      stateCode 0 (pairValue t w) 0 0 := by
  rw [literal_push_word, word_append, ax_shift8_value, word_cons, word_zero, mp_value]
  simp [implication_ne_universal]

noncomputable def offsetWord (u : V) : V := if u = 0 then 0 else mpCode u ∷ 0

theorem offset_expr (u : WordExpression.Scalar) (p a b : V) :
    WordExpression.eval (WordMacros.offset u) p a b = offsetWord (Scalar.eval u p a b) := by
  simp [WordMacros.offset, WordMacros.singleton, WordExpression.eval, Scalar.eval,
    eval_mp_atom, offsetWord]

theorem offset_value (u w : V) :
    wordValue (offsetWord u) (stateCode 0 w 0 0) = stateCode 0 w u 0 := by
  by_cases hu : u = 0
  · simp [offsetWord, hu]
  · have he : ActualArithmeticGraph.eval implicationExpr 0 u 0 0 ≠ 0 := by
      simpa [implication_eq_zero] using hu
    simp [offsetWord, hu, word_cons, mp_value, he]

noncomputable def discardWord (c : V) : V :=
  append (mpCode c ∷ axThenShifts c 0 0 9) (mpCode 0 ∷ 0)

theorem discardWord_value (c t w : V) (hc : c ≠ 0) :
    wordValue (discardWord c) (stateCode t w 0 0) = stateCode 0 w 0 0 := by
  have he : ActualArithmeticGraph.eval implicationExpr t c 0 0 ≠ 0 := by
    simp [implication_eq_zero, hc]
  have hu : ActualArithmeticGraph.eval universalExpr c 0 0 0 ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (show (0 : V) < 2 by simp) (universal_ge_two c 0))
  have hf : ActualArithmeticGraph.eval implicationExpr
      (ActualArithmeticGraph.eval universalExpr c 0 0 0) 0 0 0 ≠ 0 := by
    simp [implication_eq_zero, hu]
  rw [discardWord, word_append, word_cons, word_zero, word_cons, mp_value]
  simp only [zero_add, he, ite_false]
  rw [ax_shift9_value, mp_value]
  simp [hf]

theorem literal_discard_word : literalValue (V := V) (atoms Commands.discard) = discardWord (1 : V) := by
  simp only [Commands.discard, atoms, List.map_append, List.map_cons, List.map_nil,
    List.map_replicate, List.cons_append, List.nil_append, literal_append, literal_cons,
    literal_nil, ax_atom_numeral, mp_atom_numeral, Nat.cast_zero, Nat.cast_one,
    axThenShifts, discardWord, append_adjoin]
  rfl

theorem discard_value (t w : V) :
    wordValue (literalValue (atoms Commands.discard)) (stateCode t w 0 0) = stateCode 0 w 0 0 := by
  rw [literal_discard_word]
  exact discardWord_value 1 t w (by simp)

noncomputable def genWord (u : V) : V :=
  append (append (append (literalValue (atoms Commands.push)) (offsetWord u)) (0 ∷ 0))
    (axThenShifts u 0 0 9)

theorem gen_value (u t w d h : V) :
    wordValue (genWord u) (stateCode t w d h) =
      stateCode (ActualArithmeticGraph.eval universalExpr u t 0 0) w 0 0 := by
  rw [genWord, word_append, word_append, word_append, push_value, offset_value,
    word_cons, word_zero, shift_value]
  simp only [zero_add, zero_ne_one, ite_false, source_left_pair, source_right_pair]
  rw [ax_shift9_value]

noncomputable def mpWord (b : V) : V :=
  append (append (0 ∷ 0 ∷ mpCode b ∷ 0) (axThenShifts b 0 0 9)) (0 ∷ 0)

theorem mpWord_value (a b w : V) :
    wordValue (mpWord b)
      (stateCode 0 (pairValue a (pairValue (ActualArithmeticGraph.eval implicationExpr a b 0 0) w)) 0 0) =
      if a = 1 then 0 else stateCode b w 0 0 := by
  have hp : wordValue (0 ∷ 0 ∷ mpCode b ∷ 0)
      (stateCode 0 (pairValue a (pairValue (ActualArithmeticGraph.eval implicationExpr a b 0 0) w)) 0 0) =
      if a = 1 then 0 else stateCode b (pairValue 0 w) b 0 := by
    by_cases ha : a = 1 <;> simp [word_cons, word_zero, shift_value, ha, mp_value]
  rw [mpWord, word_append, word_append, hp]
  by_cases ha : a = 1
  · simp [ha]
  · simp only [ha, ite_false]
    rw [ax_shift9_value, word_cons, word_zero, shift_value]
    simp [universal_add_ne_one]

theorem pops_value_zero (s : V) : wordValue (literalValue (atoms (pops 0))) s = s := by
  simp [pops, atoms]

theorem pops_value_succ (n : Nat) (t x w d h : V) :
    wordValue (literalValue (atoms (pops (n + 1)))) (stateCode t (pairValue x w) d h) =
      wordValue (literalValue (atoms (pops n))) (stateCode t w 0 x) := by
  simp only [pops, atoms, List.map_append, literal_append, word_append]
  change wordValue (literalValue (atoms (pops n)))
    (wordValue (literalValue (atoms Commands.pop)) (stateCode t (pairValue x w) d h)) = _
  rw [pop_value, source_left_pair, source_right_pair]
  rfl

theorem pops_stack_value (xs : List V) (t x w d h : V) :
    wordValue (literalValue (atoms (pops (xs.length + 1))))
      (stateCode t ((xs ++ [x]).foldr pairValue w) d h) = stateCode t w 0 x := by
  induction xs generalizing d h with
  | nil =>
    simpa only [List.nil_append, List.foldr_cons, List.foldr_nil, List.length_nil, pops_value_zero] using
      pops_value_succ 0 t x w d h
  | cons y ys ih =>
    simp only [List.length_cons, List.cons_append, List.foldr_cons]
    rw [pops_value_succ]
    exact ih 0 y

#print axioms ax_shift9_value
#print axioms push_value
#print axioms discard_value
#print axioms gen_value
#print axioms mpWord_value
end PA196.Arithmetic.CommandStep
