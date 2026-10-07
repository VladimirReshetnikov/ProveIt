import OAI.Combinatorics.Progressions.Probability.ScaledCoefficientLaw

namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def continuousPolynomialDensity {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (P : Finset J) (j₀ : J) (R σ : ℝ) : (J → ℝ) → ℝ :=
  scaledCoefficientDensity e T (coefficientProfileCenter P (principalProfileSize R P.card))
    (coefficientProfileWidth P j₀ (R / 4) (principalProfileSize R P.card)
      (tailProfileSize R σ (Fintype.card J)))

theorem continuousPolynomialDensity_width_pos {J : Type*} [Fintype J]
    (P : Finset J) (j₀ : J) {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ) (j : J) :
    0 < coefficientProfileWidth P j₀ (R / 4) (principalProfileSize R P.card)
      (tailProfileSize R σ (Fintype.card J)) j :=
  coefficientProfileWidth_pos P j₀ (by positivity) (principalProfileSize_pos hR _)
    (tailProfileSize_pos hR hσ _) j

theorem continuousPolynomialDensity_probability {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (hT : ∀ v, 0 < T v) (P : Finset J) (j₀ : J)
    {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ) :
    IsProbabilityMeasure (realDensityMeasure volume (continuousPolynomialDensity e T P j₀ R σ)) :=
  scaledCoefficientDensity_probability e T hT _ _
    (continuousPolynomialDensity_width_pos P j₀ hR hσ)

theorem continuousPolynomialDensity_box {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (hT : ∀ v, 0 < T v) (P : Finset J) (j₀ : J)
    (hj₀ : j₀ ∉ P) {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    {a : J → ℝ} (ha : continuousPolynomialDensity e T P j₀ R σ a ≠ 0)
    (x : V → ℝ) (hx : ∀ v, |x v| ≤ T v) :
    |MvPolynomial.eval x (monomialArrayPolynomial e a)| ≤ 3 * R / 4 := by
  have hb := scaledCoefficientDensity_box_bound e T hT _ _
    (continuousPolynomialDensity_width_pos P j₀ hR hσ) ha x hx
  exact hb.trans ((coefficientProfile_budget P j₀ hj₀ (principalProfileSize_pos hR _).le
    (tailProfileSize_pos hR hσ _).le).trans (allocatedProfile_budget hR.le hσ1 _ _))

theorem continuousPolynomialDensity_principal {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (hT : ∀ v, 0 < T v) (P : Finset J) (j₀ : J)
    (hj₀ : j₀ ∉ P) {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ)
    {a : J → ℝ} (ha : continuousPolynomialDensity e T P j₀ R σ a ≠ 0)
    {j : J} (hj : j ∈ P) :
    principalProfileSize R P.card < a j * monomialScale T (e j) ∧
      a j * monomialScale T (e j) < 2 * principalProfileSize R P.card := by
  have hne : j ≠ j₀ := fun heq => hj₀ (heq ▸ hj)
  have hb := scaledCoefficientDensity_support e T hT _ _
    (continuousPolynomialDensity_width_pos P j₀ hR hσ) ha j
  simp only [coefficientProfileCenter, coefficientProfileWidth, hj, hne, ↓reduceIte] at hb
  have hγ := principalProfileSize_pos hR P.card
  constructor <;> linarith [(abs_lt.mp hb).1, (abs_lt.mp hb).2]

theorem continuousPolynomialDensity_tail {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (hT : ∀ v, 0 < T v) (P : Finset J) (j₀ : J)
    {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ)
    {a : J → ℝ} (ha : continuousPolynomialDensity e T P j₀ R σ a ≠ 0)
    {j : J} (hj : j ∉ P) (hne : j ≠ j₀) :
    |a j| * monomialScale T (e j) < 3 * tailProfileSize R σ (Fintype.card J) / 4 := by
  have hb := scaledCoefficientDensity_support e T hT _ _
    (continuousPolynomialDensity_width_pos P j₀ hR hσ) ha j
  simpa only [coefficientProfileCenter, coefficientProfileWidth, hj, hne, ↓reduceIte,
    sub_zero, abs_mul, abs_of_pos (monomialScale_pos T hT (e j))] using hb

theorem continuousPolynomialDensity_constant {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (hT : ∀ v, 0 < T v) (P : Finset J) (j₀ : J)
    (hj₀ : j₀ ∉ P) (he : e j₀ = 0) {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ)
    {a : J → ℝ} (ha : continuousPolynomialDensity e T P j₀ R σ a ≠ 0) :
    |a j₀| < 3 * (R / 4) / 4 := by
  have hb := scaledCoefficientDensity_support e T hT _ _
    (continuousPolynomialDensity_width_pos P j₀ hR hσ) ha j₀
  simpa only [coefficientProfileCenter, coefficientProfileWidth, hj₀, ↓reduceIte,
    he, monomialScale_zero, mul_one, sub_zero] using hb

theorem continuousPolynomialDensity_ae_box {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (hT : ∀ v, 0 < T v) (P : Finset J) (j₀ : J)
    (hj₀ : j₀ ∉ P) {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    ∀ᵐ a ∂realDensityMeasure volume (continuousPolynomialDensity e T P j₀ R σ),
      ∀ x : V → ℝ, (∀ v, |x v| ≤ T v) →
        |MvPolynomial.eval x (monomialArrayPolynomial e a)| ≤ 3 * R / 4 :=
  realDensityMeasure_ae_of_support volume _ (scaledCoefficientDensity_measurable e T _ _) _
    (fun _ ha => continuousPolynomialDensity_box e T hT P j₀ hj₀ hR hσ hσ1 ha)

end Erdos3

end

end OAI
