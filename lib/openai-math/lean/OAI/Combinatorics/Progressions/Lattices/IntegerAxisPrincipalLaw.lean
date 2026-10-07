import OAI.Combinatorics.Progressions.Probability.InactivePrincipalLaw
import OAI.Combinatorics.Progressions.Sampling.PrincipalSamplingScale

namespace OAI

section

namespace Erdos3

noncomputable def integerAxisSideLength (h K L : ℕ) (γ : ℝ) : ℕ :=
  if L ^ h < K then L else inactiveSideLength h K (inactiveDenominator γ)

theorem integerAxisSideLength_pos {h K L : ℕ} (hh : 0 < h) (hL : 0 < L) (γ : ℝ) :
    0 < integerAxisSideLength h K L γ := by
  unfold integerAxisSideLength
  split_ifs
  · exact hL
  · exact inactiveSideLength_pos hh (inactiveDenominator_pos γ)

theorem integerAxisSideLength_le {h K L : ℕ} (hh : 0 < h) (hL : 0 < L) (γ : ℝ) :
    integerAxisSideLength h K L γ ≤ L := by
  unfold integerAxisSideLength
  split_ifs with ha
  · exact le_rfl
  · exact inactiveSideLength_le hh hL (Nat.le_of_not_gt ha)

theorem integerAxisPrincipal_width {h K L : ℕ} (hh : 0 < h) (hL : 0 < L)
    {γ : ℝ} (hγ : 0 < γ)
    (hgap : (principalSamplingGapRatio γ * L) ^ h ≤ K) :
    8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * ((K : ℝ) / (L : ℝ) ^ h) := by
  apply coefficient_gap_principal_width (A := (principalSamplingGapRatio γ : ℝ)) (by exact_mod_cast hL)
    (by exact_mod_cast principalSamplingGapRatio_one_le γ) hγ hh
  · exact_mod_cast hgap
  · exact principalSamplingGapRatio_width hγ

noncomputable def integerAxisPrincipalPMF (h K L : ℕ) (hh : 0 < h) (hK : 0 < K)
    (hL : 0 < L) (γ : ℝ) (hγ : 0 < γ)
    (hgap : L ^ h < K → (principalSamplingGapRatio γ * L) ^ h ≤ K) : PMF ℤ :=
  if ha : L ^ h < K then
    principalIntegerPMF K ((L : ℝ) ^ h) γ (by exact_mod_cast hK)
      (pow_pos (by exact_mod_cast hL) _) hγ (integerAxisPrincipal_width hh hL hγ (hgap ha))
  else inactivePrincipalPMF K (inactiveDenominator γ)

theorem integerAxisPrincipalPMF_active {h K L : ℕ} (hh : 0 < h) (hK : 0 < K)
    (hL : 0 < L) {γ : ℝ} (hγ : 0 < γ)
    (hgap : L ^ h < K → (principalSamplingGapRatio γ * L) ^ h ≤ K) (ha : L ^ h < K)
    {k : ℤ} (hk : k ∈ (integerAxisPrincipalPMF h K L hh hK hL γ hγ hgap).support) :
    γ < (L : ℝ) ^ h * (k : ℝ) / K ∧ (L : ℝ) ^ h * (k : ℝ) / K < 2 * γ := by
  simp only [integerAxisPrincipalPMF, ha, ↓reduceDIte] at hk
  exact principalIntegerPMF_support (by exact_mod_cast hK)
    (pow_pos (by exact_mod_cast hL) _) hγ (integerAxisPrincipal_width hh hL hγ (hgap ha)) hk

theorem integerAxisPrincipalPMF_inactive {h K L : ℕ} (hh : 0 < h) (hK : 0 < K)
    (hL : 0 < L) {γ : ℝ} (hγ : 0 < γ)
    (hgap : L ^ h < K → (principalSamplingGapRatio γ * L) ^ h ≤ K) (ha : K ≤ L ^ h) :
    integerAxisPrincipalPMF h K L hh hK hL γ hγ hgap =
      inactivePrincipalPMF K (inactiveDenominator γ) := by
  simp [integerAxisPrincipalPMF, Nat.not_lt.mpr ha]

theorem integerAxisPrincipalPMF_bound {h K L : ℕ} (hh : 0 < h) (hK : 0 < K)
    (hL : 0 < L) {γ : ℝ} (hγ : 0 < γ)
    (hgap : L ^ h < K → (principalSamplingGapRatio γ * L) ^ h ≤ K)
    {k : ℤ} (hk : k ∈ (integerAxisPrincipalPMF h K L hh hK hL γ hγ hgap).support) :
    |(k : ℝ) / K| * (integerAxisSideLength h K L γ : ℝ) ^ h ≤ 2 * γ := by
  by_cases ha : L ^ h < K
  · have hb := integerAxisPrincipalPMF_active hh hK hL hγ hgap ha hk
    have he : |(k : ℝ) / K| * (L : ℝ) ^ h = |(L : ℝ) ^ h * (k : ℝ) / K| := by
      calc
        _ = |((k : ℝ) / K) * (L : ℝ) ^ h| := by
          rw [abs_mul, abs_of_pos (pow_pos (show (0 : ℝ) < L by exact_mod_cast hL) h)]
        _ = _ := by congr 1; ring
    simp only [integerAxisSideLength, ha, ↓reduceIte]
    rw [he, abs_of_pos (hγ.trans hb.1)]
    exact hb.2.le
  · rw [integerAxisPrincipalPMF_inactive hh hK hL hγ hgap (Nat.le_of_not_gt ha)] at hk
    rw [inactivePrincipalPMF_support hk]
    simp only [integerAxisSideLength, ha, ↓reduceIte, abs_div,
      abs_of_pos (show (0 : ℝ) < K by exact_mod_cast hK)]
    calc
      _ = |(inactivePrincipalCoefficient K (inactiveDenominator γ) : ℝ)| *
          (inactiveSideLength h K (inactiveDenominator γ) : ℝ) ^ h / K := by ring
      _ ≤ 1 / (inactiveDenominator γ : ℝ) :=
        inactivePrincipal_scaled_upper hh hK (inactiveDenominator_pos γ)
      _ ≤ γ := inactiveDenominator_bound hγ
      _ ≤ 2 * γ := by linarith

end Erdos3

end

end OAI
