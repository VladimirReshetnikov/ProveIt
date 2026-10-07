import OAI.Combinatorics.Progressions.Probability.CoefficientJetDensityFactors

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {J V : Type*} [Fintype J]
variable (P : Finset J) (j₀ : J) (h K L s : ℕ)
variable (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (ρ γ ε : ℝ) (hρ : 0 < ρ) (hγ : 0 < γ) (hε : 0 < ε)
variable (hgap : L^h < K → (principalSamplingGapRatio γ*L)^h ≤ K)
variable (hεL : 8*(probabilityProfileLipschitz : ℝ) ≤ ε*L)
variable (ha : L^h < K) (henormous : L^(s+1) < K)
variable (hconst : 8*(probabilityProfileLipschitz : ℝ) ≤ ρ*K)
variable (hj₀ : j₀ ∉ P) (he₀ : e j₀ = 0)
variable (hprincipal : ∀ j ∈ P, monomialScale T (e j) = (L : ℝ)^h)

local notation "centers" => coefficientProfileCenter P γ
local notation "widths" => coefficientProfileWidth P j₀ ρ γ ε
local notation "scales" => fun j => (K : ℝ)/monomialScale T (e j)
local notation "laws" => integerPolynomialCoordinatePMF P j₀ h K L s hh hK hL T hT hTL e he
  ρ γ ε hρ hγ hε hgap hεL

include hh hL hT hTL he hγ hε hgap hεL ha henormous hconst he₀ hprincipal in
omit [Fintype J] in
theorem integerPolynomialProfile_width_large (j : J) :
    8*(probabilityProfileLipschitz : ℝ) ≤ widths j * ((K : ℝ)/monomialScale T (e j)) := by
  classical
  by_cases hj : j = j₀
  · subst j
    simpa only [coefficientProfileWidth, ↓reduceIte, he₀, monomialScale_zero, div_one] using hconst
  · by_cases hp : j ∈ P
    · simpa only [coefficientProfileWidth, hj, hp, ↓reduceIte, hprincipal j hp] using
        integerAxisPrincipal_width hh hL hγ (hgap ha)
    · simp only [coefficientProfileWidth, hj, hp, ↓reduceIte]
      calc
        _ ≤ (ε/monomialScale T (e j))*(K : ℝ) :=
          integerAxisTail_width T hT hL hTL hε hεL (e j) (he j) henormous
        _ = _ := by ring

include ha henormous hj₀ he₀ hprincipal in
omit [Fintype J] in
theorem integerPolynomialCoordinatePMF_normalized
    (hwidth : ∀ j, 8*(probabilityProfileLipschitz : ℝ) ≤ widths j * ((K : ℝ)/monomialScale T (e j)))
    (j : J) :
    laws j = normalizedIntegerPMF ((K : ℝ)/monomialScale T (e j)) (centers j) (widths j)
      (div_pos (by exact_mod_cast hK) (monomialScale_pos T hT (e j)))
      (coefficientProfileWidth_pos P j₀ hρ hγ hε j) (hwidth j) := by
  classical
  by_cases hj : j = j₀
  · subst j
    have hc : 8*(probabilityProfileLipschitz : ℝ) ≤ ρ*K := by
      simpa only [coefficientProfileWidth, ↓reduceIte, he₀, monomialScale_zero, div_one] using hwidth j₀
    simp only [integerPolynomialCoordinatePMF, ↓reduceIte, coefficientProfileCenter, hj₀,
      coefficientProfileWidth, he₀, monomialScale_zero, div_one]
    exact constantIntegerPMF_large _ _ _ _ hc
  · by_cases hp : j ∈ P
    · simp only [integerPolynomialCoordinatePMF, hj, hp, ↓reduceIte,
        integerAxisPrincipalPMF, ha, ↓reduceDIte, coefficientProfileCenter,
        coefficientProfileWidth, hprincipal j hp, principalIntegerPMF]
    · simp only [integerPolynomialCoordinatePMF, hj, hp, ↓reduceIte, integerAxisTailPMF,
        henormous, ↓reduceDIte, coefficientProfileCenter, coefficientProfileWidth]
      unfold normalizedIntegerPMF
      have hw : (ε/monomialScale T (e j))*(K : ℝ) = ε*((K : ℝ)/monomialScale T (e j)) := by ring
      simp only [zero_mul, hw]

include ha henormous hj₀ he₀ hprincipal in
theorem integerPolynomial_affinePMF
    (hwidth : ∀ j, 8*(probabilityProfileLipschitz : ℝ) ≤ widths j * ((K : ℝ)/monomialScale T (e j)))
    {R : ℝ} (hsupport : ∀ x, R < ‖x‖ → affineProductProfile centers widths x = 0)
    (hZ : 0 < coefficientWeightSum (affineProductProfile centers widths) scales) :
    independentProductPMF laws =
      coefficientPMF (affineProductProfile centers widths)
        (affineProductProfile_nonneg centers widths (coefficientProfileWidth_pos P j₀ hρ hγ hε))
        scales (fun j => div_pos (by exact_mod_cast hK) (monomialScale_pos T hT (e j))) hsupport hZ := by
  ext z
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [independentProductPMF_toReal, affineCoefficientPMF_apply centers widths scales
    (coefficientProfileWidth_pos P j₀ hρ hγ hε)
    (fun j => div_pos (by exact_mod_cast hK) (monomialScale_pos T hT (e j))) hsupport hZ]
  apply Finset.prod_congr rfl
  intro j _
  rw [integerPolynomialCoordinatePMF_normalized P j₀ h K L s hh hK hL T hT hTL e he
    ρ γ ε hρ hγ hε hgap hεL ha henormous hj₀ he₀ hprincipal hwidth j]
  rfl

include ha henormous hj₀ he₀ hprincipal in
theorem integerPolynomial_affineMeasure
    (hwidth : ∀ j, 8*(probabilityProfileLipschitz : ℝ) ≤ widths j * ((K : ℝ)/monomialScale T (e j)))
    {R : ℝ} (hsupport : ∀ x, R < ‖x‖ → affineProductProfile centers widths x = 0)
    (hZ : 0 < coefficientWeightSum (affineProductProfile centers widths) scales) :
    Measure.pi (fun j => (laws j).toMeasure) =
      (coefficientPMF (affineProductProfile centers widths)
        (affineProductProfile_nonneg centers widths (coefficientProfileWidth_pos P j₀ hρ hγ hε))
        scales (fun j => div_pos (by exact_mod_cast hK) (monomialScale_pos T hT (e j))) hsupport hZ).toMeasure := by
  rw [← integerPolynomial_affinePMF P j₀ h K L s hh hK hL T hT hTL e he
    ρ γ ε hρ hγ hε hgap hεL ha henormous hj₀ he₀ hprincipal hwidth hsupport hZ]
  exact (Measure.toPMF_toMeasure _).symm

end Erdos3

end

end OAI
