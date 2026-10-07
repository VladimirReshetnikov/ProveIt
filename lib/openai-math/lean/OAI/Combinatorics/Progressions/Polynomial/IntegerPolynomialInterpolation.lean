import OAI.Combinatorics.Progressions.Estimates.AllocatedShortAxis
import OAI.Combinatorics.Progressions.Estimates.PrincipalAxisInterpolation

namespace OAI

section

namespace Erdos3

variable {J V : Type*} [Fintype J]

noncomputable def integerPolynomialInterpolation (P : Finset J) (j₀ : J) (h K L s : ℕ)
    (T : V → ℝ) (e : J → V →₀ ℕ) (ρ γ ε : ℝ) (j : J) : ℝ → ℝ := by
  classical
  exact if j = j₀ then constantIntegerInterpolation K ρ
    else if j ∈ P then principalAxisInterpolation h K L γ
    else tailAxisInterpolation T K L s ε (e j)

noncomputable def integerPolynomialInterpolationCap (h L s : ℕ) (ρ γ ε : ℝ) : ℝ :=
  max (constantIntegerInterpolationCap ρ)
    (max (principalAxisInterpolationCap h L γ) (tailAxisInterpolationCap L s ε))

noncomputable def integerPolynomialInterpolationLip (h L s : ℕ) (ρ γ ε : ℝ) : ℝ :=
  max (constantIntegerInterpolationLip ρ)
    (max (principalAxisInterpolationLip h L γ) (tailAxisInterpolationLip L s ε))

omit [Fintype J] in
theorem integerPolynomialInterpolation_spec (P : Finset J) (j₀ : J) (h K L s : ℕ)
    (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
    (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
    (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
    (ρ γ ε : ℝ) (hρ : 0 < ρ) (hγ : 0 < γ) (hε : 0 < ε)
    (hgap : L^h < K → (principalSamplingGapRatio γ * L)^h ≤ K)
    (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L) (j : J) :
    IsIntegerMassInterpolation K
      (integerPolynomialCoordinatePMF P j₀ h K L s hh hK hL T hT hTL e he
        ρ γ ε hρ hγ hε hgap hεL j)
      (integerPolynomialInterpolationCap h L s ρ γ ε)
      (integerPolynomialInterpolationLip h L s ρ γ ε)
      (integerPolynomialInterpolation P j₀ h K L s T e ρ γ ε j) := by
  classical
  by_cases hj : j = j₀
  · simp only [integerPolynomialCoordinatePMF, integerPolynomialInterpolation, hj, ↓reduceIte]
    exact (constantIntegerInterpolation_spec K ρ (by exact_mod_cast hK) hρ).mono
      (le_max_left _ _) (le_max_left _ _)
  · by_cases hp : j ∈ P
    · simp only [integerPolynomialCoordinatePMF, integerPolynomialInterpolation, hj, hp, ↓reduceIte]
      exact (principalAxisInterpolation_spec h K L hh hK hL γ hγ hgap).mono
        ((le_max_left _ _).trans (le_max_right _ _)) ((le_max_left _ _).trans (le_max_right _ _))
    · simp only [integerPolynomialCoordinatePMF, integerPolynomialInterpolation, hj, hp, ↓reduceIte]
      exact (tailAxisInterpolation_spec T hT K L s hK hL hTL ε hε hεL (e j) (he j)).mono
        ((le_max_right _ _).trans (le_max_right _ _)) ((le_max_right _ _).trans (le_max_right _ _))

end Erdos3

end

end OAI
