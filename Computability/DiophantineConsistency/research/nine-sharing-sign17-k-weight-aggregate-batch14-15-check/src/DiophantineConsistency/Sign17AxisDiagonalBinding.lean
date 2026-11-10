import DiophantineConsistency.Sign17AxisDiagonalDegree
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17AxisDiagonal
open MvPolynomial Sign17UnivariateDegree Sign17AxisRootBinding

def univariateVars (i : Fin 17) : P := if i = 16 then 0 else Polynomial.X

theorem unique_eval (e : Expr (Fin 17)) :
    (MvPolynomial.uniqueAlgEquiv ℤ (Fin 1)) (e.evalRing diagonalVars) =
      e.evalRing univariateVars := by
  induction e <;> simp_all [Expr.evalRing, diagonalVars, univariateVars,
    MvPolynomial.uniqueAlgEquiv_apply, MvPolynomial.eval₂_X]
  all_goals split_ifs <;> simp

theorem direct_axis (p : Fin 4 → ℤ) :
    (MvPolynomial.uniqueAlgEquiv ℤ (Fin 1))
      (diagonal (Sign17AbstractExpression.expression p).toPolynomial) =
      (SharingSeed17Degree96.seed p).evalRing axis := by
  rw [diagonal_eval, unique_eval]
  change ((SharingSeed17Degree96.seed p).subst
    (Fin.cons (.constant 1) (fun i => .var i))).evalRing univariateVars = _
  rw [ModelJonesSyntax.evalRing_subst]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · fin_cases j <;> rfl


end DiophantineConsistency.Sign17AxisDiagonal
#print axioms DiophantineConsistency.Sign17AxisDiagonal.unique_eval
#print axioms DiophantineConsistency.Sign17AxisDiagonal.direct_axis
