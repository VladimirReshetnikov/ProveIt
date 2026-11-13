import DiophantineConsistency.Current14Carrier65OtherFields
import DiophantineConsistency.Current14Carrier65DiagonalDegree

/-! Candidate upper bound for actual rank on the all-equal axis. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Current14Carrier65DiagonalRank
open Sign17UnivariateDegree Current14Carrier65QInputs
  Current14Carrier65OtherWeights Current14Carrier65OtherFields

def axisVars (_ : Fin 14) : P := Polynomial.X
def axisCore (p : Fin 4 → ℤ) : Carrier65.Core P :=
  Carrier65.core (fun j => Polynomial.C (p j)) axisVars

theorem rank_degree_le (p : Fin 4 → ℤ) : (axisCore p).rank.natDegree ≤ 4 := by
  have hdiag := Current14Carrier65Diagonal.univariate_degree_le (rank p)
  have hpoly := polynomial_bound (rank p)
  rw [rank_weight, Expr.evalRing_X] at hpoly
  have h := hdiag.trans hpoly
  rw [rank_eval] at h
  change (axisCore p).rank.natDegree ≤ 4 at h
  exact h

end DiophantineConsistency.Current14Carrier65DiagonalRank

#print axioms DiophantineConsistency.Current14Carrier65DiagonalRank.rank_degree_le
