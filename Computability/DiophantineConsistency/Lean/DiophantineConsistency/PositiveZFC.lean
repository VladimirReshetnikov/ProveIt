import DiophantineConsistency.ExplicitZFC
import DiophantineConsistency.PositiveDomain

/-! # The closed consistency equation on nine strictly positive integers -/

namespace DiophantineConsistency.PositiveZFC

open SetTheory LeanProofs.BoundedZFCConsistency

/-- The same fixed nine-variable equation under the exact shift `u=v-1`. -/
def expression : Expr (Fin 9) := ExplicitZFC.expression.positiveShift

noncomputable def polynomial : MvPolynomial (Fin 9) ℤ := expression.toPolynomial

theorem hasZero_iff_refutation :
    (∃ v : Fin 9 → ℤ, (∀ i, 0 < v i) ∧ expression.eval v = 0) ↔
      BProv ZFCax_s [] Form.fBot :=
  (Expr.hasPositiveZero_positiveShift_iff _).trans ExplicitZFC.syntax_hasZero_iff_refutation

theorem noZero_iff_conZFC :
    (¬ ∃ v : Fin 9 → ℤ, (∀ i, 0 < v i) ∧ expression.eval v = 0) ↔ ConZFC :=
  not_congr hasZero_iff_refutation

theorem noPolynomialZero_iff_conZFC :
    (¬ ∃ v : Fin 9 → ℤ, (∀ i, 0 < v i) ∧ MvPolynomial.eval v polynomial = 0) ↔ ConZFC := by
  simpa only [polynomial, Expr.eval_toPolynomial] using noZero_iff_conZFC

end DiophantineConsistency.PositiveZFC
