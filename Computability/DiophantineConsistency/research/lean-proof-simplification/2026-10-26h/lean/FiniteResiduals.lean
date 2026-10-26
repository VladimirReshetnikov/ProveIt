import DiophantineConsistency.QuadraticRegisterSystem
import Mathlib.Data.Sum.Basic

/-! Shared residual facts and applications to three existing compilers.
All data and theorem hypotheses at the call sites are unchanged. -/

namespace DiophantineConsistency.ProofRefactor

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

theorem sumExpressions_cost {σ : Type*} (es : List (Expr σ)) (b : ℕ)
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

theorem natCast_sumRec {α β : Type*} (x : α → ℕ) (w : β → ℕ) :
    (fun i => ((Sum.rec x w i : ℕ) : ℤ)) = natAssignment x w := by
  funext i
  cases i <;> rfl

section Signed

open ArithmeticDAG DAGQuartic
variable {inputs fixed : ℕ}

theorem signed_expression_zero_iff (nodes : List (Node inputs fixed)) (output : ℕ)
    (p : Fin fixed → ℤ) (v : Variables inputs nodes.length → ℤ) :
    (expression nodes output p).eval v = 0 ↔
      ∀ i, (residual nodes output p i).eval v = 0 :=
  sumSquares_zero_iff _ _

theorem signed_polynomial_degree (nodes : List (Node inputs fixed)) (output : ℕ)
    (p : Fin fixed → ℤ) : (DAGQuartic.polynomial nodes output p).totalDegree ≤ 4 :=
  sumSquares_degree_le _ 2 (residual_degree nodes output p)

theorem signed_exists_polynomial_zero_iff (nodes : List (Node inputs fixed))
    (htop : Topological nodes) (output : ℕ) (ho : output < nodes.length)
    (p : Fin fixed → ℤ) :
    (∃ v : Variables inputs nodes.length → ℕ,
      MvPolynomial.eval (fun i => (v i : ℤ)) (DAGQuartic.polynomial nodes output p) = 0) ↔
      ∃ x : Fin inputs → ℕ, value nodes output p (fun i => (x i : ℤ)) = 0 := by
  rw [Sum.exists_sum]
  simpa only [DAGQuartic.polynomial, Expr.eval_toPolynomial, natCast_sumRec, assignment, natAssignment] using
    (exists_congr (fun x => exists_zero_iff nodes htop output ho p x))

end Signed

section Natural

open ArithmeticDAG NaturalDAGQuartic
variable {inputs fixed : ℕ}

theorem natural_expression_zero_iff (nodes : List (Node inputs fixed)) (left right : ℕ)
    (p : Fin fixed → ℤ) (v : Variables inputs nodes.length → ℤ) :
    (expression nodes left right p).eval v = 0 ↔
      ∀ i, (residual nodes left right p i).eval v = 0 :=
  sumSquares_zero_iff _ _

theorem natural_polynomial_degree (nodes : List (Node inputs fixed)) (left right : ℕ)
    (p : Fin fixed → ℤ) : (NaturalDAGQuartic.polynomial nodes left right p).totalDegree ≤ 4 :=
  sumSquares_degree_le _ 2 (residual_degree nodes left right p)

theorem natural_exists_polynomial_zero_iff (nodes : List (Node inputs fixed))
    (htop : Topological nodes) (left right : ℕ) (hl : left < nodes.length) (hr : right < nodes.length)
    (p : Fin fixed → ℤ) (ha : Allowed nodes p) :
    (∃ v : Variables inputs nodes.length → ℕ,
      MvPolynomial.eval (fun i => (v i : ℤ)) (NaturalDAGQuartic.polynomial nodes left right p) = 0) ↔
      ∃ x : Fin inputs → ℕ,
        value nodes left p (fun i => (x i : ℤ)) = value nodes right p (fun i => (x i : ℤ)) := by
  rw [Sum.exists_sum]
  simpa only [NaturalDAGQuartic.polynomial, Expr.eval_toPolynomial, natCast_sumRec, assignment, natAssignment] using
    (exists_congr (fun x => exists_zero_iff nodes htop left right hl hr p ha x))

end Natural

section System

open NaturalRegisterProgram QuadraticRegisterSystem
variable {n : ℕ} {p : Program n}

theorem system_expression_zero_iff (s : System p) (v : Fin n ⊕ Fin p.nodes.length → ℤ) :
    s.expression.eval v = 0 ↔ ∀ i, (s.residual i).eval v = 0 :=
  sumSquares_zero_iff _ _

theorem system_expression_degree (s : System p) : s.expression.toPolynomial.totalDegree ≤ 4 :=
  sumSquares_degree_le _ 2 s.residual_degree

end System

#print axioms sumSquares_zero_iff
#print axioms sumSquares_degree_le
#print axioms DAGQuartic.expression_zero_iff
#print axioms signed_expression_zero_iff
#print axioms DAGQuartic.polynomial_degree
#print axioms signed_polynomial_degree
#print axioms DAGQuartic.exists_polynomial_zero_iff
#print axioms signed_exists_polynomial_zero_iff
#print axioms NaturalDAGQuartic.expression_zero_iff
#print axioms natural_expression_zero_iff
#print axioms NaturalDAGQuartic.polynomial_degree
#print axioms natural_polynomial_degree
#print axioms NaturalDAGQuartic.exists_polynomial_zero_iff
#print axioms natural_exists_polynomial_zero_iff
#print axioms QuadraticRegisterSystem.System.expression_zero_iff
#print axioms system_expression_zero_iff
#print axioms QuadraticRegisterSystem.System.expression_degree
#print axioms system_expression_degree

end DiophantineConsistency.ProofRefactor
