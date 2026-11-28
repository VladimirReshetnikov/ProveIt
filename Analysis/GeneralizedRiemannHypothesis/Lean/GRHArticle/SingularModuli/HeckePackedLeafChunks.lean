import GRHArticle.SingularModuli.HeckeChunkedPrefixCertificate

/-!
# Packing consecutive coefficient blocks

Packing each block before any coefficient transformation bounds the depth
of kernel evaluation for long coefficient prefixes.
-/

namespace GRHArticle.SingularModuli.IntegerPolynomialExpression

private theorem packedEval_cons (w : ℕ) (a : ℤ) (l : List ℤ) :
    (coefficients (a::l)).packedEval w =
      a + (2:ℤ)^w * (coefficients l).packedEval w := by
  rw [packedEval_eq_eval, packedEval_eq_eval]
  simp only [polynomial, coefficientListPolynomial, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_X]

theorem packedEval_append (w : ℕ) (l r : List ℤ) :
    (coefficients (l ++ r)).packedEval w =
      (coefficients l).packedEval w + (2:ℤ)^(w*l.length) * (coefficients r).packedEval w := by
  induction l with
  | nil =>
    simp [packedEval_eq_eval, polynomial, coefficientListPolynomial]
  | cons a l ih =>
    rw [List.cons_append, packedEval_cons, packedEval_cons, ih]
    simp only [List.length_cons, Nat.mul_succ, pow_add]
    ring

/-- Evaluate consecutive blocks in the original coefficient order. -/
def packedLeafChunks (w : ℕ) : List (List ℤ) → ℤ
  | [] => 0
  | l :: ls => (coefficients l).packedEval w + (2:ℤ)^(w*l.length) * packedLeafChunks w ls

theorem packedLeafChunks_eq (w : ℕ) (ls : List (List ℤ)) :
    packedLeafChunks w ls = (coefficients ls.flatten).packedEval w := by
  induction ls with
  | nil => simp [packedLeafChunks, packedEval_eq_eval, polynomial, coefficientListPolynomial]
  | cons l ls ih =>
    rw [packedLeafChunks, List.flatten_cons, packedEval_append, ih]

end GRHArticle.SingularModuli.IntegerPolynomialExpression
