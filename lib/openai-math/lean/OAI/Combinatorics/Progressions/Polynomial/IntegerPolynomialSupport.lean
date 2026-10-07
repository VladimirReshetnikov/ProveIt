import OAI.Combinatorics.Progressions.Polynomial.IntegerPolynomialActiveProfileSupport

namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {J V : Type*} [Fintype J]
variable (P : Finset J) (j₀ : J) (h K L s : ℕ)
variable (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (R σ : ℝ) (hR : 0 < R) (hσ : 0 < σ)

variable (hgap : L ^ h < K → (principalSamplingGapRatio (principalProfileSize R P.card) * L) ^ h ≤ K)
variable (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ (tailProfileSize R σ (Fintype.card J)) * L)

noncomputable def allocatedIntegerPolynomialCoordinatePMF : J → PMF ℤ :=
  integerPolynomialCoordinatePMF P j₀ h K L s hh hK hL T hT hTL e he (R / 4) (principalProfileSize R P.card) (tailProfileSize R σ (Fintype.card J))
    (by positivity) (principalProfileSize_pos hR _) (tailProfileSize_pos hR hσ _) hgap hεL

local notation "laws" => allocatedIntegerPolynomialCoordinatePMF P j₀ h K L s hh hK hL T hT hTL
  e he R σ hR hσ hgap hεL

theorem allocatedIntegerPolynomial_probability :
    IsProbabilityMeasure (Measure.pi (fun j => (laws j).toMeasure)) := by infer_instance

theorem allocatedIntegerPolynomial_box (hj₀ : j₀ ∉ P) (he₀ : e j₀ = 0) (hσ1 : σ ≤ 1)
    (hprincipal : ∀ j ∈ P, monomialScale T (e j) = (integerAxisSideLength h K L (principalProfileSize R P.card) : ℝ) ^ h)
    (a : J → ℤ) (ha : ∀ j, a j ∈ (laws j).support) (x : V → ℝ) (hx : ∀ v, |x v| ≤ T v) :
    |MvPolynomial.eval x (monomialArrayPolynomial e (fun j => (a j : ℝ) / K))| ≤ 3 * R / 4 := by
  have hb := integerPolynomialCoordinatePMF_box P j₀ h K L s hh hK hL T hT hTL e he
    (R / 4) (principalProfileSize R P.card) (tailProfileSize R σ (Fintype.card J)) (by positivity) (principalProfileSize_pos hR _) (tailProfileSize_pos hR hσ _)
    hgap hεL hj₀ he₀ hprincipal a ha x hx
  exact hb.trans (allocatedProfile_budget hR.le hσ1 _ _)

theorem allocatedIntegerPolynomial_ae_box (hj₀ : j₀ ∉ P) (he₀ : e j₀ = 0) (hσ1 : σ ≤ 1)
    (hprincipal : ∀ j ∈ P, monomialScale T (e j) = (integerAxisSideLength h K L (principalProfileSize R P.card) : ℝ) ^ h) :
    ∀ᵐ a ∂Measure.pi (fun j => (laws j).toMeasure),
      ∀ x : V → ℝ, (∀ v, |x v| ≤ T v) →
        |MvPolynomial.eval x (monomialArrayPolynomial e (fun j => (a j : ℝ) / K))| ≤ 3 * R / 4 := by
  have hb := integerPolynomialLaw_ae_box P j₀ h K L s hh hK hL T hT hTL e he
    (R / 4) (principalProfileSize R P.card) (tailProfileSize R σ (Fintype.card J)) (by positivity) (principalProfileSize_pos hR _) (tailProfileSize_pos hR hσ _)
    hgap hεL hj₀ he₀ hprincipal
  filter_upwards [hb] with a ha
  intro x hx
  exact (ha x hx).trans (allocatedProfile_budget hR.le hσ1 _ _)

theorem allocatedIntegerPolynomial_integer_box (hj₀ : j₀ ∉ P) (he₀ : e j₀ = 0) (hσ1 : σ ≤ 1)
    (hprincipal : ∀ j ∈ P, monomialScale T (e j) = (integerAxisSideLength h K L (principalProfileSize R P.card) : ℝ) ^ h)
    (a : J → ℤ) (ha : ∀ j, a j ∈ (laws j).support) (x : V → ℤ) (hx : ∀ v, |(x v : ℝ)| ≤ T v) :
    |(MvPolynomial.eval x (integerMonomialArrayPolynomial e a) : ℝ) / K| ≤ 3 * R / 4 := by
  rw [← integerMonomialArrayPolynomial_normalized_eval]
  exact allocatedIntegerPolynomial_box P j₀ h K L s hh hK hL T hT hTL e he R σ hR hσ hgap hεL
    hj₀ he₀ hσ1 hprincipal a ha _ hx

end Erdos3

end

end OAI
