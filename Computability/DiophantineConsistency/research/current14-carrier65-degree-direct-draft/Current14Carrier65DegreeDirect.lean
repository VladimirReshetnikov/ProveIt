import DiophantineConsistency.Current14Carrier65DiagonalWhole
import DiophantineConsistency.Current14Carrier65DegreeUpper
import DiophantineConsistency.Current14Carrier65DiagonalDegree

/-! Candidate direct polynomial transport, avoiding the expression import union. -/
noncomputable section
namespace DiophantineConsistency.Current14Carrier65DegreeDirect
open MvPolynomial Current14Carrier65Diagonal

def diagonalHom : MvPolynomial (Fin 14) ℤ →+* Polynomial ℤ :=
  (MvPolynomial.uniqueAlgEquiv ℤ (Fin 1)).toRingHom.comp
    (MvPolynomial.eval₂Hom MvPolynomial.C diagonalVars)

theorem diagonal_C (z : ℤ) : diagonalHom (MvPolynomial.C z) = Polynomial.C z := by
  simp [diagonalHom, diagonalVars, MvPolynomial.uniqueAlgEquiv_apply]

theorem diagonal_X (i : Fin 14) : diagonalHom (MvPolynomial.X i) = Polynomial.X := by
  simp [diagonalHom, diagonalVars, MvPolynomial.uniqueAlgEquiv_apply, MvPolynomial.eval₂_X]

theorem diagonal_value (p : Fin 4 → ℤ) :
    (MvPolynomial.uniqueAlgEquiv ℤ (Fin 1)) (diagonal (Carrier65.polynomial p)) =
      Current14Carrier65DiagonalWhole.axisValue p := by
  have h := Carrier65.value_map diagonalHom (fun j => MvPolynomial.C (p j)) MvPolynomial.X
  have h' : diagonalHom (Carrier65.polynomial p) = Current14Carrier65DiagonalWhole.axisValue p := by
    simpa only [Carrier65.polynomial, Current14Carrier65DiagonalWhole.axisValue,
      Current14Carrier65DiagonalBinding.axisVars, diagonal_C, diagonal_X] using h
  exact h'

theorem polynomial_degree_ge (p : Fin 4 → ℤ) (hp : p 0 ≠ 0) :
    150 ≤ (Carrier65.polynomial p).totalDegree := by
  have h := Sign17UnivariateDegree.mapped_degree_le (diagonal (Carrier65.polynomial p))
  have hd := diagonal_totalDegree_le (Carrier65.polynomial p)
  rw [diagonal_value, Current14Carrier65DiagonalWhole.axis_degree p hp] at h
  exact h.trans hd

theorem polynomial_exact (p : Fin 4 → ℤ) (hp : p 0 ≠ 0) :
    (Carrier65.polynomial p).totalDegree = 150 :=
  Nat.le_antisymm (Current14Carrier65DegreeUpper.polynomial_degree_le p)
    (polynomial_degree_ge p hp)

end DiophantineConsistency.Current14Carrier65DegreeDirect

#print axioms DiophantineConsistency.Current14Carrier65DegreeDirect.diagonal_value
#print axioms DiophantineConsistency.Current14Carrier65DegreeDirect.polynomial_degree_ge
#print axioms DiophantineConsistency.Current14Carrier65DegreeDirect.polynomial_exact
