import OAI.Combinatorics.Progressions.Fourier.TranslationPhaseCharacterBounds

namespace OAI

section

namespace Erdos3

open MvPolynomial

variable {B : Type*} [Fintype B]

theorem translationPhaseArgument_left_increment_point_bound
    (D₀ : MvPolynomial B ℝ) (z g : PolynomialTranslationGroupOver ℝ B)
    (β : B → ℝ) {d : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hdegree : D₀.totalDegree ≤ d)
    (hres : ∀ i, |β i - g.base i| ≤ 1)
    (hnew : ∀ i, |β i - g.base i - z.base i| ≤ 1)
    (hbase : ∀ i, |z.base i| ≤ ε)
    (hp : |eval (β - g.base) z.polynomial| ≤ ε) :
    |translationPhaseArgument D₀ (z * g) β - translationPhaseArgument D₀ g β| ≤
      (1 + realPolynomialMass D₀ * Fintype.card B * d) * ε := by
  rw [translationPhaseArgument_left_increment]
  have hdiff (i : B) : |(β - g.base - z.base) i - (β - g.base) i| ≤ ε := by
    change |β i - g.base i - z.base i - (β i - g.base i)| ≤ ε
    rw [show β i - g.base i - z.base i - (β i - g.base i) = -z.base i by ring,
      abs_neg]
    exact hbase i
  have hD : |eval (β - g.base - z.base) D₀ - eval (β - g.base) D₀| ≤
      realPolynomialMass D₀ * Fintype.card B * d * ε := by
    have h := abs_aeval_sub_aeval_mass_box_bound D₀
      (β - g.base - z.base) (β - g.base) (B := 1)
      le_rfl hε hnew hres hdiff hdegree
    simpa only [MvPolynomial.aeval_eq_eval, one_pow, mul_one] using h
  calc
    _ ≤ |eval (β - g.base) z.polynomial| +
      |eval (β - g.base - z.base) D₀ - eval (β - g.base) D₀| := abs_add_le _ _
    _ ≤ ε + realPolynomialMass D₀ * Fintype.card B * d * ε := add_le_add hp hD
    _ = _ := by ring

theorem translationPhaseArgument_left_increment_point_mass_bound
    (D₀ : MvPolynomial B ℝ) (z g : PolynomialTranslationGroupOver ℝ B)
    (β : B → ℝ) {d : ℕ} {ε M : ℝ} (hε : 0 ≤ ε)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ M)
    (hres : ∀ i, |β i - g.base i| ≤ 1)
    (hnew : ∀ i, |β i - g.base i - z.base i| ≤ 1)
    (hbase : ∀ i, |z.base i| ≤ ε)
    (hp : |eval (β - g.base) z.polynomial| ≤ ε) :
    |translationPhaseArgument D₀ (z * g) β - translationPhaseArgument D₀ g β| ≤
      (1 + M * Fintype.card B * d) * ε := by
  apply (translationPhaseArgument_left_increment_point_bound D₀ z g β hε hdegree
    hres hnew hbase hp).trans
  gcongr

theorem translationPhaseCharacter_left_increment_point_bound
    (D₀ : MvPolynomial B ℝ) (z g : PolynomialTranslationGroupOver ℝ B)
    (β : B → ℝ) {d : ℕ} {ε M : ℝ} (hε : 0 ≤ ε)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ M)
    (hres : ∀ i, |β i - g.base i| ≤ 1)
    (hnew : ∀ i, |β i - g.base i - z.base i| ≤ 1)
    (hbase : ∀ i, |z.base i| ≤ ε)
    (hp : |eval (β - g.base) z.polynomial| ≤ ε) :
    ‖(Real.fourierChar (translationPhaseArgument D₀ (z * g) β) : ℂ) -
      (Real.fourierChar (translationPhaseArgument D₀ g β) : ℂ)‖ ≤
      (2 * Real.pi) * (1 + M * Fintype.card B * d) * ε := by
  have hphase := translationPhaseArgument_left_increment_point_mass_bound D₀ z g β
    hε hdegree hD hres hnew hbase hp
  exact (real_fourierChar_norm_sub_le _ _).trans
    ((mul_le_mul_of_nonneg_left hphase (by positivity)).trans_eq (by ring))

omit [Fintype B] in

theorem translation_residual_unit_boxes_of_quarter
    (z g : PolynomialTranslationGroupOver ℝ B) (β : B → ℝ) {ε : ℝ}
    (hε : ε ≤ 1 / 4) (hres : ∀ i, |β i - g.base i| ≤ 1 / 4)
    (hbase : ∀ i, |z.base i| ≤ ε) :
    (∀ i, |β i - g.base i| ≤ 1) ∧
      ∀ i, |β i - g.base i - z.base i| ≤ 1 := by
  constructor
  · intro i
    exact (hres i).trans (by norm_num)
  · intro i
    apply (abs_sub _ _).trans
    have hr := hres i
    have hz := hbase i
    linarith

theorem translationPhaseArgument_left_increment_quarter_point_bound
    (D₀ : MvPolynomial B ℝ) (z g : PolynomialTranslationGroupOver ℝ B)
    (β : B → ℝ) {d : ℕ} {ε M : ℝ} (hε : 0 ≤ ε) (hεquarter : ε ≤ 1 / 4)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ M)
    (hres : ∀ i, |β i - g.base i| ≤ 1 / 4)
    (hbase : ∀ i, |z.base i| ≤ ε)
    (hp : |eval (β - g.base) z.polynomial| ≤ ε) :
    |translationPhaseArgument D₀ (z * g) β - translationPhaseArgument D₀ g β| ≤
      (1 + M * Fintype.card B * d) * ε := by
  obtain ⟨hres', hnew⟩ := translation_residual_unit_boxes_of_quarter z g β hεquarter hres hbase
  exact translationPhaseArgument_left_increment_point_mass_bound D₀ z g β
    hε hdegree hD hres' hnew hbase hp

theorem translationPhaseCharacter_left_increment_quarter_point_bound
    (D₀ : MvPolynomial B ℝ) (z g : PolynomialTranslationGroupOver ℝ B)
    (β : B → ℝ) {d : ℕ} {ε M : ℝ} (hε : 0 ≤ ε) (hεquarter : ε ≤ 1 / 4)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ M)
    (hres : ∀ i, |β i - g.base i| ≤ 1 / 4)
    (hbase : ∀ i, |z.base i| ≤ ε)
    (hp : |eval (β - g.base) z.polynomial| ≤ ε) :
    ‖(Real.fourierChar (translationPhaseArgument D₀ (z * g) β) : ℂ) -
      (Real.fourierChar (translationPhaseArgument D₀ g β) : ℂ)‖ ≤
      (2 * Real.pi) * (1 + M * Fintype.card B * d) * ε := by
  obtain ⟨hres', hnew⟩ := translation_residual_unit_boxes_of_quarter z g β hεquarter hres hbase
  exact translationPhaseCharacter_left_increment_point_bound D₀ z g β
    hε hdegree hD hres' hnew hbase hp

end Erdos3

end

end OAI
