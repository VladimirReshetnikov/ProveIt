import DiophantineConsistency.WeightedExpressionDegree
import Mathlib.Data.Fin.VecNotation

/-! Proposed generic degree ingredient; no whole-polynomial degree is claimed. -/
namespace DiophantineConsistency.Current14Carrier65QDegree

/-- Variables are `X, a, c, H, gamma`, in that order. -/
def qSyntax : Expr (Fin 5) :=
  let X : Expr (Fin 5) := .var 0
  let a : Expr (Fin 5) := .var 1
  let c : Expr (Fin 5) := .var 2
  let H : Expr (Fin 5) := .var 3
  let gamma : Expr (Fin 5) := .var 4
  (X + gamma * H) ^ 2 + 2 * a * c * (X + gamma * H) - H * c ^ 2

def qWeights : Fin 5 → ℕ := ![2, 6, 5, 6, 1]

theorem q_weight : qSyntax.weightedDegree qWeights = 18 := by decide +kernel

theorem q_eval {R : Type*} [CommRing R] (v : Fin 5 → R) :
    qSyntax.evalRing v = (v 0 + v 4 * v 3) ^ 2 +
      2 * v 1 * v 2 * (v 0 + v 4 * v 3) - v 3 * (v 2) ^ 2 := by
  simp only [qSyntax, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_pow, Expr.evalRing_var, Expr.evalRing_ofNat, Int.cast_ofNat]

theorem q_degree_le {σ : Type*} (v : Fin 5 → MvPolynomial σ ℤ)
    (hv : ∀ j, (v j).totalDegree ≤ qWeights j) :
    ((v 0 + v 4 * v 3) ^ 2 +
      2 * v 1 * v 2 * (v 0 + v 4 * v 3) - v 3 * (v 2) ^ 2).totalDegree ≤ 18 := by
  have h := Expr.degree_evalRing_le qSyntax qWeights v hv
  rw [q_weight, q_eval] at h
  exact h

end DiophantineConsistency.Current14Carrier65QDegree

#print axioms DiophantineConsistency.Current14Carrier65QDegree.q_weight
#print axioms DiophantineConsistency.Current14Carrier65QDegree.q_eval
#print axioms DiophantineConsistency.Current14Carrier65QDegree.q_degree_le
