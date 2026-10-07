import OAI.Combinatorics.Progressions.Polynomial.TranslationPhaseQuotient

namespace OAI

section

namespace Erdos3

open MvPolynomial

variable {B : Type*} [Fintype B]

theorem translationPhaseCharacter_left_increment_bound
    (D₀ : MvPolynomial B ℝ) (z g : PolynomialTranslationGroupOver ℝ B)
    (β : B → ℝ) {d : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hdegree : D₀.totalDegree ≤ d)
    (hres : ∀ i, |β i - g.base i| ≤ 1)
    (hnew : ∀ i, |β i - g.base i - z.base i| ≤ 1)
    (hbase : ∀ i, |z.base i| ≤ ε) (hmass : realPolynomialMass z.polynomial ≤ ε) :
    ‖(Real.fourierChar (translationPhaseArgument D₀ (z * g) β) : ℂ) -
      (Real.fourierChar (translationPhaseArgument D₀ g β) : ℂ)‖ ≤
      (2 * Real.pi) * (1 + realPolynomialMass D₀ * Fintype.card B * d) * ε := by
  have hphase := translationPhaseArgument_left_increment_bound D₀ z g β
    hε hdegree hres hnew hbase hmass
  exact (real_fourierChar_norm_sub_le _ _).trans
    ((mul_le_mul_of_nonneg_left hphase (by positivity)).trans_eq (by ring))

theorem translationPhaseCharacter_left_increment_mass_bound
    (D₀ : MvPolynomial B ℝ) (z g : PolynomialTranslationGroupOver ℝ B)
    (β : B → ℝ) {d : ℕ} {ε M : ℝ} (hε : 0 ≤ ε)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ M)
    (hres : ∀ i, |β i - g.base i| ≤ 1)
    (hnew : ∀ i, |β i - g.base i - z.base i| ≤ 1)
    (hbase : ∀ i, |z.base i| ≤ ε) (hmass : realPolynomialMass z.polynomial ≤ ε) :
    ‖(Real.fourierChar (translationPhaseArgument D₀ (z * g) β) : ℂ) -
      (Real.fourierChar (translationPhaseArgument D₀ g β) : ℂ)‖ ≤
      (2 * Real.pi) * (1 + M * Fintype.card B * d) * ε := by
  apply (translationPhaseCharacter_left_increment_bound D₀ z g β hε hdegree
    hres hnew hbase hmass).trans
  gcongr

theorem translationPhaseFunction_left_increment_on_chart_bound
    (D₀ : MvPolynomial B ℝ) (z g : PolynomialTranslationGroupOver ℝ B)
    (β : B → ℤ) {d : ℕ} {ε M : ℝ} (hε : 0 ≤ ε)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ M)
    (hchart : ∀ i, |g.base i - (β i : ℝ)| < 1 / 2)
    (hchart' : ∀ i, |(z * g).base i - (β i : ℝ)| < 1 / 2)
    (hbase : ∀ i, |z.base i| ≤ ε) (hmass : realPolynomialMass z.polynomial ≤ ε) :
    ‖translationPhaseFunction D₀ (z * g) - translationPhaseFunction D₀ g‖ ≤
      (2 * Real.pi) * (1 + M * Fintype.card B * d) * ε := by
  rw [translationPhaseFunction_on_chart D₀ (z * g) β hchart',
    translationPhaseFunction_on_chart D₀ g β hchart]
  apply translationPhaseCharacter_left_increment_mass_bound D₀ z g
    (fun i => (β i : ℝ)) hε hdegree hD ?_ ?_ hbase hmass
  · intro i
    rw [abs_sub_comm]
    exact (hchart i).le.trans (by norm_num)
  · intro i
    have he : (β i : ℝ) - g.base i - z.base i =
        -((z * g).base i - (β i : ℝ)) := by
      simp only [PolynomialTranslationGroupOver.base_mul, Pi.add_apply]
      ring
    rw [he, abs_neg]
    exact (hchart' i).le.trans (by norm_num)

end Erdos3

end

end OAI
