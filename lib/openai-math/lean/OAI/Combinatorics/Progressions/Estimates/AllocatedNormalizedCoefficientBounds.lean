import OAI.Combinatorics.Progressions.Geometry.AllocatedArraySupport

namespace OAI

section

namespace Erdos3
open MeasureTheory

theorem continuousPolynomialDensity_coefficient_bound {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (hT : ∀ v, 0 < T v) (P : Finset J) (j₀ : J)
    (hj₀ : j₀ ∉ P) {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    {a : J → ℝ} (ha : continuousPolynomialDensity e T P j₀ R σ a ≠ 0) (j : J) :
    |a j| * monomialScale T (e j) ≤ 3 * R / 4 := by
  have hb := scaledCoefficientDensity_coefficient_bound e T hT _ _
    (continuousPolynomialDensity_width_pos P j₀ hR hσ) ha j
  exact hb.trans (allocatedProfile_term_bound P j₀ hj₀ hR hσ hσ1 j)

theorem continuousPolynomialDensity_coefficient_le_radius {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (hT : ∀ v, 0 < T v) (P : Finset J) (j₀ : J)
    (hj₀ : j₀ ∉ P) {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    {a : J → ℝ} (ha : continuousPolynomialDensity e T P j₀ R σ a ≠ 0) (j : J) :
    |a j| * monomialScale T (e j) ≤ R :=
  (continuousPolynomialDensity_coefficient_bound e T hT P j₀ hj₀ hR hσ hσ1 ha j).trans
    (by linarith)

theorem continuousPolynomialDensity_ae_coefficient_le_radius {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (hT : ∀ v, 0 < T v) (P : Finset J) (j₀ : J)
    (hj₀ : j₀ ∉ P) {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    ∀ᵐ a ∂realDensityMeasure volume (continuousPolynomialDensity e T P j₀ R σ),
      ∀ j, |a j| * monomialScale T (e j) ≤ R :=
  realDensityMeasure_ae_of_support volume _ (scaledCoefficientDensity_measurable e T _ _) _
    (fun _ ha => continuousPolynomialDensity_coefficient_le_radius e T hT P j₀ hj₀ hR hσ hσ1 ha)

theorem allocatedIntegerCoefficient_le_radius {J V : Type*} [Fintype J]
    (P : Finset J) (j₀ : J) (h K L s : ℕ) (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
    (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
    (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
    (R σ : ℝ) (hR : 0 < R) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hgap : L ^ h < K → (principalSamplingGapRatio (principalProfileSize R P.card) * L) ^ h ≤ K)
    (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ tailProfileSize R σ (Fintype.card J) * L)
    (hj₀ : j₀ ∉ P) (he₀ : e j₀ = 0)
    (hprincipal : ∀ j ∈ P, monomialScale T (e j) =
      (integerAxisSideLength h K L (principalProfileSize R P.card) : ℝ) ^ h)
    (j : J) {k : ℤ}
    (hk : k ∈ (allocatedIntegerPolynomialCoordinatePMF P j₀ h K L s hh hK hL T hT hTL e he
      R σ hR hσ hgap hεL j).support) :
    |(k : ℝ) / K| * monomialScale T (e j) ≤ R :=
  (allocatedIntegerCoefficient_bound P j₀ h K L s hh hK hL T hT hTL e he R σ hR hσ hσ1
    hgap hεL hj₀ he₀ hprincipal j hk).trans (by linarith)

end Erdos3

end

end OAI
