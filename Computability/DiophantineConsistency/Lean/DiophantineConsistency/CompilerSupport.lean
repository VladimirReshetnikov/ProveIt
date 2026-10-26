import DiophantineConsistency.QuarticSyntax
import Mathlib.Data.Sum.Basic

/-! Shared finite-residual facts used by circuit compilers. -/
namespace DiophantineConsistency.CompilerSupport

theorem eval_sumExpressions {σ : Type*} (es : List (Expr σ)) (v : σ → ℤ) :
    (QuarticSyntax.sumExpressions es).eval v = (es.map (fun e => e.eval v)).sum := by
  induction es <;> simp_all [QuarticSyntax.sumExpressions]

theorem sumSquares_zero_iff {σ : Type*} {n : ℕ}
    (es : Fin n → Expr σ) (v : σ → ℤ) :
    (QuarticSyntax.sumExpressions (List.ofFn fun i => es i * es i)).eval v = 0 ↔
      ∀ i, (es i).eval v = 0 := by
  rw [eval_sumExpressions]
  simp only [List.map_ofFn, Fin.sum_ofFn, Function.comp_apply, Expr.eval_mul]
  simpa only [Finset.mem_univ, forall_true_left] using
    (Finset.sum_mul_self_eq_zero_iff (Finset.univ : Finset (Fin n))
      (fun i => (es i).eval v))

theorem sumSquares_degree_le {σ : Type*} {n : ℕ}
    (es : Fin n → Expr σ) (d : ℕ) (h : ∀ i, (es i).toPolynomial.totalDegree ≤ d) :
    (QuarticSyntax.sumExpressions (List.ofFn fun i => es i * es i)).toPolynomial.totalDegree
      ≤ 2 * d := by
  rw [QuarticSyntax.polynomial_sumExpressions]
  simp only [List.map_ofFn, Fin.sum_ofFn, Function.comp_apply, Expr.toPolynomial]
  simpa only [pow_two] using
    (Diophantine.totalDegree_sum_pow_le Finset.univ
      (fun i => (es i).toPolynomial) 2 d (fun i _ => h i))

theorem natCast_sumRec {α β : Type*} (x : α → ℕ) (w : β → ℕ) :
    (fun i => ((Sum.rec x w i : ℕ) : ℤ)) = natAssignment x w := by
  funext i
  cases i <;> rfl

end DiophantineConsistency.CompilerSupport
