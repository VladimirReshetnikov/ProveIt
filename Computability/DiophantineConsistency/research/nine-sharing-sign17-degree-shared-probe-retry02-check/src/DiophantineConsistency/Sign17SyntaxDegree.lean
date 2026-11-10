import DiophantineConsistency.Sign17CurrentExpressionDef

/-! SOURCE-ONLY: syntactic degree bounds for integer expressions. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17SyntaxDegree

/-- The usual structural upper bound on the total degree of an expression. -/
def degree {σ : Type*} : Expr σ → ℕ
  | .constant _ => 0
  | .var _ => 1
  | .add a b | .sub a b => max (degree a) (degree b)
  | .mul a b => degree a + degree b

theorem polynomial_degree_le {σ : Type*} (e : Expr σ) :
    e.toPolynomial.totalDegree ≤ degree e := by
  induction e with
  | constant z =>
    change (MvPolynomial.C z : MvPolynomial σ ℤ).totalDegree ≤ 0
    rw [MvPolynomial.totalDegree_C]
  | var i => simp [Expr.toPolynomial, degree]
  | add a b ha hb => exact (MvPolynomial.totalDegree_add _ _).trans (max_le_max ha hb)
  | sub a b ha hb => exact (MvPolynomial.totalDegree_sub _ _).trans (max_le_max ha hb)
  | mul a b ha hb => exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add ha hb)
end DiophantineConsistency.Sign17SyntaxDegree
#print axioms DiophantineConsistency.Sign17SyntaxDegree.polynomial_degree_le
