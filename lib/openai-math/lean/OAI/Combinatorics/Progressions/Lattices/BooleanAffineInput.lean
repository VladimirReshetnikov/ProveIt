import OAI.Combinatorics.Progressions.Polynomial.BooleanPolynomialBudget

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def booleanAffineInput {I α : Type*} [Fintype α] [DecidableEq α]
    (a : Option α → MvPolynomial I ℝ) (t : Finset α) : MvPolynomial I ℝ :=
  ∑ r, MvPolynomial.C (booleanFeature r t : ℝ) * a r

theorem booleanAffineInput_eval {I α : Type*} [Fintype α] [DecidableEq α]
    (a : Option α → MvPolynomial I ℝ) (t : Finset α) (x : I → ℝ) :
    MvPolynomial.eval x (booleanAffineInput a t) =
      ∑ r, (booleanFeature r t : ℝ) * MvPolynomial.eval x (a r) := by
  simp only [booleanAffineInput, map_sum, map_mul, MvPolynomial.eval_C]

theorem booleanAffineInput_mass_le {I α : Type*} [Fintype α] [DecidableEq α]
    (a : Option α → MvPolynomial I ℝ) (t : Finset α) {A : ℝ}
    (ha : ∀ r, realPolynomialMass (a r) ≤ A) :
    realPolynomialMass (booleanAffineInput a t) ≤ ((Fintype.card α : ℝ) + 1) * A := by
  classical
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _r : Option α, A := by
      apply Finset.sum_le_sum
      intro r _
      apply (realPolynomialMass_C_mul_le _ _).trans
      simpa only [one_mul] using mul_le_mul (booleanFeature_abs_le_one r t)
        (ha r) (realPolynomialMass_nonneg _) zero_le_one
    _ = _ := by simp

theorem booleanAffineInput_totalDegree_le {I α : Type*} [Fintype α] [DecidableEq α]
    (a : Option α → MvPolynomial I ℝ) (t : Finset α) {e : ℕ}
    (ha : ∀ r, (a r).totalDegree ≤ e) : (booleanAffineInput a t).totalDegree ≤ e := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro r _
  exact (MvPolynomial.totalDegree_mul _ _).trans (by
    simpa only [MvPolynomial.totalDegree_C, zero_add] using ha r)

end Erdos3

end

end OAI
