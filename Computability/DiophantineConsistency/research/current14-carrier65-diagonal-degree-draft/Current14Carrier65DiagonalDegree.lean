import DiophantineConsistency.Sign17UnivariateDegreeProbe

/-! Candidate degree-nonincreasing all-equal diagonal for fourteen variables. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Current14Carrier65Diagonal
open MvPolynomial Sign17UnivariateDegree

def diagonalVars (_ : Fin 14) : MvPolynomial (Fin 1) ℤ := X 0

def diagonal (p : MvPolynomial (Fin 14) ℤ) : MvPolynomial (Fin 1) ℤ :=
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
  simp [diagonalVars]

theorem diagonal_eval (e : Expr (Fin 14)) :
    diagonal e.toPolynomial = e.evalRing diagonalVars := by
  induction e <;> simp_all [diagonal, Expr.toPolynomial, Expr.evalRing]
  exact map_intCast (MvPolynomial.eval₂Hom MvPolynomial.C diagonalVars) _

theorem unique_eval (e : Expr (Fin 14)) :
    (MvPolynomial.uniqueAlgEquiv ℤ (Fin 1)) (e.evalRing diagonalVars) =
      e.evalRing (fun _ => Polynomial.X) := by
  induction e <;> simp_all [Expr.evalRing, diagonalVars,
    MvPolynomial.uniqueAlgEquiv_apply, MvPolynomial.eval₂_X]

theorem univariate_degree_le (e : Expr (Fin 14)) :
    (e.evalRing (fun _ => Polynomial.X)).natDegree ≤ e.toPolynomial.totalDegree := by
  have h := mapped_degree_le (diagonal e.toPolynomial)
  rw [diagonal_eval, unique_eval] at h
  exact h.trans (diagonal_totalDegree_le e.toPolynomial)

end DiophantineConsistency.Current14Carrier65Diagonal

#print axioms DiophantineConsistency.Current14Carrier65Diagonal.diagonal_totalDegree_le
#print axioms DiophantineConsistency.Current14Carrier65Diagonal.unique_eval
#print axioms DiophantineConsistency.Current14Carrier65Diagonal.univariate_degree_le
