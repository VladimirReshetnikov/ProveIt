import DiophantineConsistency.SharingSeed38Syntax

/-! UNCOMPILED split draft; no new checked claim. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed38

/-- Candidate first-residual evaluation; not yet checked by Lean. -/
theorem firstResidual_zeroWitness (p : Fin 4 → ℤ) (x : ℤ) :
    (firstResidual p).eval (zeroWitness x) = -(p 0 + 1) ^ 2 := by
  simp [firstResidual, zeroWitness, Expr.eval]
  ring

/-- Candidate nonnegativity helper for every finite squared residual sum. -/
theorem eval_sumSquares_nonneg (es : List (Expr (Fin 39))) (v : Fin 39 → ℤ) :
    0 ≤ (QuarticSyntax.sumExpressions (es.map fun e => e * e)).eval v := by
  induction es with
  | nil => simp [QuarticSyntax.sumExpressions, Expr.eval]
  | cons e es ih =>
    simp only [List.map_cons, QuarticSyntax.sumExpressions, Expr.eval_add, Expr.eval_mul]
    exact add_nonneg (mul_self_nonneg _) ih

/-- Candidate all-input normalization, assuming the first port is positive. -/
theorem seed_normalized (p : Fin 4 → ℤ) (hp : 0 < p 0) (x : ℤ) :
    (seed p).eval (zeroWitness x) ≠ 0 := by
  have hne : (firstResidual p).eval (zeroWitness x) ≠ 0 := by
    rw [firstResidual_zeroWitness]
    nlinarith
  have hs : 0 < (firstResidual p).eval (zeroWitness x) *
      (firstResidual p).eval (zeroWitness x) := mul_self_pos.mpr hne
  have ht := eval_sumSquares_nonneg (remainingResiduals p) (zeroWitness x)
  have hpos : 0 < (seed p).eval (zeroWitness x) := by
    simpa only [seed, Expr.eval_add, Expr.eval_mul] using add_pos_of_pos_of_nonneg hs ht
  exact ne_of_gt hpos


end DiophantineConsistency.SharingSeed38
