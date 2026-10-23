import DiophantineConsistency.GapFinalizerDegree66
import DiophantineConsistency.GapPositiveRecipe66

/-! # Degree bounds for both counted H2082 polynomial presentations -/

namespace DiophantineConsistency.GapPolynomialDegree66

theorem positivePolynomial_degree_le (p : Fin 11 → ℤ) :
    (GapCircuit66.positivePolynomial p).totalDegree ≤ 1845940 := by
  change (GapCircuit66.positiveValue (fun k => MvPolynomial.C (p k))
    MvPolynomial.X).totalDegree ≤ 1845940
  rw [GapCircuitTranslation66.positiveValue_eq_naturalValue]
  apply GapFinalizerDegree66.naturalValue_degree_le
  intro i
  exact (MvPolynomial.totalDegree_sub _ _).trans (by simp)

theorem sourcePolynomial_degree_le (ports : Fin 4 → ℤ) (a : ℕ) :
    (GapNinePolynomial66.polynomial ports a).totalDegree ≤ 1845940 := by
  rw [← GapCircuitRecipe66.naturalPolynomial_eq_recipe]
  exact GapFinalizerDegree66.naturalPolynomial_degree_le _

theorem positiveSourcePolynomial_degree_le (ports : Fin 4 → ℤ) (a : ℕ) :
    (GapPositiveRecipe66.positivePolynomial ports a).totalDegree ≤ 1845940 := by
  rw [← GapPositiveRecipe66.positivePolynomial_eq_recipe]
  exact positivePolynomial_degree_le _

end DiophantineConsistency.GapPolynomialDegree66
