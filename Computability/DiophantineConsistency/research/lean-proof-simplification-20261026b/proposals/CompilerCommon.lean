import DiophantineConsistency.QuarticCost
import DiophantineConsistency.WeightedExpressionDegree

/-! Reusable executable sum-of-squares lemmas.  These move duplicated semantic
and cost arguments into a public API without changing any polynomial data. -/
namespace DiophantineConsistency.ProofSimplification.CompilerCommon

variable {σ : Type*}

@[simp] theorem eval_sumExpressions (es : List (Expr σ)) (v : σ → ℤ) :
    (QuarticSyntax.sumExpressions es).eval v = (es.map (fun e => e.eval v)).sum := by
  induction es <;> simp_all [QuarticSyntax.sumExpressions]

def sumSquares {n : ℕ} (rows : Fin n → Expr σ) : Expr σ :=
  QuarticSyntax.sumExpressions (List.ofFn fun i => rows i * rows i)

theorem sumSquares_zero_iff {n : ℕ} (rows : Fin n → Expr σ) (v : σ → ℤ) :
    (sumSquares rows).eval v = 0 ↔ ∀ i, (rows i).eval v = 0 := by
  rw [sumSquares, eval_sumExpressions]
  simp only [List.map_ofFn, Fin.sum_ofFn, Function.comp_apply, Expr.eval_mul]
  simpa only [Finset.mem_univ, forall_true_left] using
    (Finset.sum_mul_self_eq_zero_iff (Finset.univ : Finset (Fin n))
      (fun i => (rows i).eval v))

theorem sumSquares_degree {n d : ℕ} (rows : Fin n → Expr σ)
    (hd : ∀ i, (rows i).toPolynomial.totalDegree ≤ d) :
    (sumSquares rows).toPolynomial.totalDegree ≤ 2*d := by
  rw [sumSquares, QuarticSyntax.polynomial_sumExpressions]
  simp only [List.map_ofFn, Fin.sum_ofFn, Function.comp_apply, Expr.toPolynomial]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  simpa only [two_mul] using
    (MvPolynomial.totalDegree_mul (rows i).toPolynomial (rows i).toPolynomial).trans
      (Nat.add_le_add (hd i) (hd i))

theorem sumExpressions_cost (es : List (Expr σ)) (b : ℕ)
    (h : ∀ e ∈ es, e.binaryOps ≤ b) :
    (QuarticSyntax.sumExpressions es).binaryOps ≤ (b+1)*es.length := by
  induction es with
  | nil => simp [QuarticSyntax.sumExpressions, Expr.binaryOps]
  | cons e es ih =>
    have he := h e (by simp)
    have ht := ih (fun e he => h e (by simp [he]))
    change 1 + e.binaryOps + (QuarticSyntax.sumExpressions es).binaryOps ≤ _
    simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

/-- Existing weighted-degree machinery supplies unweighted degree for free. -/
theorem unweighted_degree (e : Expr σ) :
    e.toPolynomial.totalDegree ≤ e.weightedDegree (fun _ => 1) := by
  simpa only [Expr.evalRing_X] using
    e.degree_evalRing_le (fun _ => 1) MvPolynomial.X (fun _ => by simp)

#print axioms sumSquares_zero_iff
#print axioms sumSquares_degree
end DiophantineConsistency.ProofSimplification.CompilerCommon
