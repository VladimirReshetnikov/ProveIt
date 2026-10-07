import OAI.Combinatorics.Progressions.Polynomial.ContinuousPolynomialSupport
import OAI.Combinatorics.Progressions.Polynomial.IntegerPolynomialSupport

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem allocatedProfile_term_bound {J : Type*} [Fintype J] (P : Finset J) (j₀ : J)
    (hj₀ : j₀ ∉ P) {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (j : J) :
    |coefficientProfileCenter P (principalProfileSize R P.card) j| +
      coefficientProfileWidth P j₀ (R / 4) (principalProfileSize R P.card)
        (tailProfileSize R σ (Fintype.card J)) j ≤ 3 * R / 4 := by
  classical
  apply (Finset.single_le_sum (s := Finset.univ)
    (fun i _ => add_nonneg (abs_nonneg _) (continuousPolynomialDensity_width_pos P j₀ hR hσ i).le)
    (Finset.mem_univ j)).trans
  exact (coefficientProfile_budget P j₀ hj₀ (principalProfileSize_pos hR _).le
    (tailProfileSize_pos hR hσ _).le).trans (allocatedProfile_budget hR.le hσ1 _ _)

theorem allocatedIntegerCoefficient_bound {J V : Type*} [Fintype J]
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
    |(k : ℝ) / K| * monomialScale T (e j) ≤ 3 * R / 4 := by
  have hb := integerPolynomialCoordinatePMF_bound P j₀ h K L s hh hK hL T hT hTL e he
    (R / 4) (principalProfileSize R P.card) (tailProfileSize R σ (Fintype.card J))
    (by positivity) (principalProfileSize_pos hR _) (tailProfileSize_pos hR hσ _)
    hgap hεL hj₀ he₀ hprincipal j hk
  exact hb.trans (allocatedProfile_term_bound P j₀ hj₀ hR hσ hσ1 j)

end Erdos3

end

end OAI
