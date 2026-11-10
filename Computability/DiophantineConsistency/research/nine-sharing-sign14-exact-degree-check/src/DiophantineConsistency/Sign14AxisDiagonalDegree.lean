import DiophantineConsistency.Sign14AxisSeedDegree

/-! SOURCE-ONLY: a degree-nonincreasing multivariate axis specialization. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14AxisDiagonal
open MvPolynomial Sign17UnivariateDegree Sign14AxisBinding

def diagonalVars (i : Fin 14) : MvPolynomial (Fin 1) ℤ :=
  X 0

noncomputable def diagonal (p : MvPolynomial (Fin 14) ℤ) : MvPolynomial (Fin 1) ℤ :=
  MvPolynomial.eval₂ MvPolynomial.C diagonalVars p

theorem diagonal_totalDegree_le (p : MvPolynomial (Fin 14) ℤ) :
    (diagonal p).totalDegree ≤ p.totalDegree := by
  classical
  unfold diagonal
  rw [MvPolynomial.eval₂_eq]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  refine le_trans (Finset.sum_le_sum (fun i hi => ?_)) (MvPolynomial.le_totalDegree hd)
  change (diagonalVars i ^ d i).totalDegree ≤ d i
  refine (MvPolynomial.totalDegree_pow _ _).trans ?_
  unfold diagonalVars
  simp

theorem diagonal_eval (e : Expr (Fin 14)) :
    diagonal e.toPolynomial = e.evalRing diagonalVars := by
  induction e <;> simp_all [diagonal, Expr.toPolynomial, Expr.evalRing]
  exact map_intCast (MvPolynomial.eval₂Hom MvPolynomial.C diagonalVars) _


end DiophantineConsistency.Sign14AxisDiagonal
#print axioms DiophantineConsistency.Sign14AxisDiagonal.diagonal_totalDegree_le
#print axioms DiophantineConsistency.Sign14AxisDiagonal.diagonal_eval
