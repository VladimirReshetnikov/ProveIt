module
public import PA196.Arithmetic.CommandWord
@[expose] public section

/-! Exact command equations with arbitrary model-valued parameters.
These are not restrictions to standard natural-number register contents. -/
namespace PA196.Arithmetic.CommandStep
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open M6.PA M6.PA.SourceCantorInternal HeadGraphs CommandWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem eval_source_pair (a b : WordExpression.Scalar) (p t d : V) :
    Scalar.eval (pair a b) p t d = pairValue (Scalar.eval a p t d) (Scalar.eval b p t d) := rfl

noncomputable def mpCode (b : V) : V := pairValue 1 (pairValue b 0)
noncomputable def axCode (c x y : V) : V := pairValue (c + 2) (pairValue y (pairValue x 0))

private theorem select_mp (b t w d h : V) :
    stepValue (mpCode b) (stateCode t w d h) =
      WordExpression.eval mp (stateCode t w d h) (mpCode b) 0 := by
  simp only [stepValue, stepExpr, zero, tag, WordExpression.eval, Scalar.eval]
  simp [mpCode, (decode_pairValue 1 (pairValue b 0)).1, stateCode_ne_zero]

theorem mp_value (b t w d h : V) :
    stepValue (mpCode b) (stateCode t w d h) =
      if ActualArithmeticGraph.eval implicationExpr t (d + b) 0 0 = h then
        stateCode (d + b) (pairValue 0 w) (d + b) 0
      else stateCode 0 w (d + b) 0 := by
  rw [select_mp]
  simp [mp, zero, top, stack, cacheD, cacheH, tag, fields, first, state, imp,
    WordExpression.eval, Scalar.eval, eval_source_pair, mpCode, stateCode,
    (decode_pairValue 1 (pairValue b 0)).2, (decode_pairValue b 0).1]

noncomputable def schemaHeads (D H A d h : V) : List V :=
  [ActualArithmeticGraph.eval head6Expr D A H d,
   ActualArithmeticGraph.eval head5Expr D H 0 d,
   ActualArithmeticGraph.eval head4Expr D A H d,
   ActualArithmeticGraph.eval head3Expr D A H d,
   ActualArithmeticGraph.eval head2Expr D A H d,
   ActualArithmeticGraph.eval head1Expr D H 0 d,
   ActualArithmeticGraph.eval rho8Expr D A H d,
   ActualArithmeticGraph.eval universalExpr d h 0 0]

noncomputable def gateValue (a b c d : V) : V :=
  if c = a then 0 else if c = b then 0 else ActualArithmeticGraph.eval bundleExpr a b c d

private theorem select_ax (c x y t w d h : V) :
    stepValue (axCode c x y) (stateCode t w d h) =
      WordExpression.eval ax (stateCode t w d h) (axCode c x y) 0 := by
  have hp : (1 : V) < c + 2 :=
    lt_of_lt_of_le (show (1 : V) < 2 by simp) (show (2 : V) ≤ c + 2 by simp)
  have h0 : c + 2 ≠ (0 : V) := ne_of_gt (lt_trans (by simp) hp)
  have h1 : c + 2 ≠ (1 : V) := ne_of_gt hp
  simp only [stepValue, stepExpr, zero, tag, WordExpression.eval, Scalar.eval]
  simp [axCode, (decode_pairValue (c + 2) (pairValue y (pairValue x 0))).1,
    stateCode_ne_zero, h0, h1]

/-- Nine pushed entries, including the saved top, with the new gate argument
order and the original offset preserved in the restricted head. -/
theorem ax_value (c x y t w d h : V) :
    stepValue (axCode c x y) (stateCode t w d h) =
      stateCode (gateValue (h + y) (d + x) c d)
        ((schemaHeads (d + x) (h + y) c d h ++ [t]).foldr pairValue w) 0 0 := by
  rw [select_ax]
  simp [ax, zero, top, stack, cacheD, cacheH, tag, fields, first, second,
    state, headValue, push, WordExpression.eval, Scalar.eval, eval_source_pair,
    axCode, stateCode, schemaHeads, gateValue,
    (decode_pairValue (c + 2) (pairValue y (pairValue x 0))).1,
    (decode_pairValue (c + 2) (pairValue y (pairValue x 0))).2,
    (decode_pairValue y (pairValue x 0)).1,
    (decode_pairValue y (pairValue x 0)).2, (decode_pairValue x 0).1]

#print axioms mp_value
#print axioms ax_value
end PA196.Arithmetic.CommandStep
