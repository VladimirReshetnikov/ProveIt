import DiophantineConsistency.Sign14AxisDiagonalDegree
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14AxisDiagonal
open MvPolynomial Sign17UnivariateDegree Sign14AxisBinding

def univariateVars (i : Fin 14) : P := Polynomial.X

theorem unique_eval (e : Expr (Fin 14)) :
    (MvPolynomial.uniqueAlgEquiv ℤ (Fin 1)) (e.evalRing diagonalVars) =
      e.evalRing univariateVars := by
  induction e <;> simp_all [Expr.evalRing, diagonalVars, univariateVars,
    MvPolynomial.uniqueAlgEquiv_apply, MvPolynomial.eval₂_X]
  all_goals simp

theorem direct_axis (p : Fin 4 → ℤ) :
    (MvPolynomial.uniqueAlgEquiv ℤ (Fin 1))
      (diagonal (Sign14AbstractExpression.expression p).toPolynomial) =
      (SharingSeed14Degree124.seed p).evalRing axis := by
  rw [diagonal_eval, unique_eval]
  change ((SharingSeed14Degree124.seed p).subst
    (Fin.cons (.constant 1) (fun i => .var i))).evalRing univariateVars = _
  rw [ModelJonesSyntax.evalRing_subst]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · fin_cases j <;> rfl


end DiophantineConsistency.Sign14AxisDiagonal
#print axioms DiophantineConsistency.Sign14AxisDiagonal.unique_eval
#print axioms DiophantineConsistency.Sign14AxisDiagonal.direct_axis
