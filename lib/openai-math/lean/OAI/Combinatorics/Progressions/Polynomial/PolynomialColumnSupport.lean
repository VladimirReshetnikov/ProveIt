import OAI.Combinatorics.Progressions.Polynomial.PolynomialParameterContinuity

namespace OAI

section

namespace Erdos3

theorem polynomialColumns_norm_le_on_box {P I J : Type*} [Fintype P] [Fintype I] [Fintype J]
    (p : I → J → MvPolynomial P ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ i j, realPolynomialMass (p i j) ≤ C) (x : P → ℝ) (hx : ‖x‖ ≤ 1) :
    ‖polynomialColumns p x‖ ≤ Fintype.card J * C := by
  apply matrixSupCLM_norm_le _ hC
  intro i j
  exact (mvPolynomial_eval_abs_le_sum_coeff (p i j) x
    (fun k => (norm_le_pi_norm x k).trans hx)).trans (hc i j)

end Erdos3

end

end OAI
