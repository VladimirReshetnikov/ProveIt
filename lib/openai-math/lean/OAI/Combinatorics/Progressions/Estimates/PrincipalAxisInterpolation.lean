import OAI.Combinatorics.Progressions.Lattices.IntegerAxisPrincipalLaw
import OAI.Combinatorics.Progressions.Lattices.PrincipalIntegerInterpolation

namespace OAI

section

namespace Erdos3

noncomputable def principalAxisInterpolation (h K L : ℕ) (γ : ℝ) : ℝ → ℝ :=
  if L^h < K then principalIntegerInterpolation K ((L : ℝ)^h) γ
  else integerMassTent K (inactivePrincipalCoefficient K (inactiveDenominator γ))

noncomputable def principalAxisInterpolationCap (h L : ℕ) (γ : ℝ) : ℝ :=
  max (4 * (L : ℝ)^h / γ) ((L : ℝ)^h)

noncomputable def principalAxisInterpolationLip (h L : ℕ) (γ : ℝ) : ℝ :=
  max (8 * (probabilityProfileLipschitz : ℝ) * ((L : ℝ)^h)^2 / γ^2)
    (2 * ((L : ℝ)^h)^2)

theorem principalAxisInterpolation_spec (h K L : ℕ) (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
    (γ : ℝ) (hγ : 0 < γ)
    (hgap : L^h < K → (principalSamplingGapRatio γ * L)^h ≤ K) :
    IsIntegerMassInterpolation K (integerAxisPrincipalPMF h K L hh hK hL γ hγ hgap)
      (principalAxisInterpolationCap h L γ) (principalAxisInterpolationLip h L γ)
      (principalAxisInterpolation h K L γ) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  by_cases ha : L^h < K
  · simp only [integerAxisPrincipalPMF, principalAxisInterpolation, ha, ↓reduceDIte, ↓reduceIte]
    exact (principalIntegerInterpolation_spec K ((L : ℝ)^h) γ hKr
      (pow_pos (by exact_mod_cast hL) _) hγ (integerAxisPrincipal_width hh hL hγ (hgap ha))).mono
      (le_max_left _ _) (le_max_left _ _)
  · have hbound : (K : ℝ) ≤ (L : ℝ)^h := by exact_mod_cast (Nat.le_of_not_gt ha)
    simp only [integerAxisPrincipalPMF, principalAxisInterpolation, ha, ↓reduceDIte, ↓reduceIte,
      inactivePrincipalPMF]
    apply (integerMassTent_spec K hKr (inactivePrincipalCoefficient K (inactiveDenominator γ))).mono
    · exact hbound.trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hKr.le hbound 2) (by norm_num)).trans
        (le_max_right _ _)

end Erdos3

end

end OAI
