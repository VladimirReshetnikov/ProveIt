import OAI.Combinatorics.Progressions.Estimates.CoefficientScaleGap
import OAI.Combinatorics.Progressions.Probability.PrincipalCoefficientLaw

namespace OAI

section

namespace Erdos3

noncomputable def principalSamplingGapRatio (γ : ℝ) : ℕ :=
  ⌈max 1 (16 * (probabilityProfileLipschitz : ℝ) / γ)⌉₊

theorem principalSamplingGapRatio_one_le (γ : ℝ) : 1 ≤ principalSamplingGapRatio γ := by
  have h : (1 : ℝ) ≤ (principalSamplingGapRatio γ : ℝ) :=
    (le_max_left _ _).trans (Nat.le_ceil _)
  exact_mod_cast h

theorem principalSamplingGapRatio_width {γ : ℝ} (hγ : 0 < γ) :
    16 * (probabilityProfileLipschitz : ℝ) ≤ γ * principalSamplingGapRatio γ := by
  have h : 16 * (probabilityProfileLipschitz : ℝ) / γ ≤ (principalSamplingGapRatio γ : ℝ) :=
    (le_max_right _ _).trans (Nat.le_ceil _)
  have hb := (div_le_iff₀ hγ).mp h
  nlinarith

theorem exists_principal_sampling_scale {I : Type*} [Fintype I]
    (K : I → ℝ) (hK : ∀ i, 0 < K i) (h : I → ℕ) (hh : ∀ i, 1 ≤ h i)
    (L₀ : ℕ) (hL₀ : 0 < L₀) {γ : ℝ} (hγ : 0 < γ) :
    ∃ L : ℕ, 0 < L ∧ L₀ ≤ L ∧ L ≤ L₀ * principalSamplingGapRatio γ ^ Fintype.card I ∧
      ∀ i, (L : ℝ) ^ h i < K i → ∃ p : PMF ℤ,
        (∀ k, (p k).toReal =
          smoothProbabilityProfile
            (((k : ℝ) - (3 * γ / 2) * (K i / (L : ℝ) ^ h i)) /
              ((γ / 2) * (K i / (L : ℝ) ^ h i))) /
            shiftedSmoothSampleSum ((3 * γ / 2) * (K i / (L : ℝ) ^ h i))
              ((γ / 2) * (K i / (L : ℝ) ^ h i))) ∧
        (∀ k ∈ p.support, γ < (L : ℝ) ^ h i * (k : ℝ) / K i ∧
          (L : ℝ) ^ h i * (k : ℝ) / K i < 2 * γ) := by
  obtain ⟨L, hL, hlo, hhi, hgap⟩ := exists_integer_coefficient_scale_gap K h L₀
    (principalSamplingGapRatio γ) hL₀ (principalSamplingGapRatio_one_le γ)
  refine ⟨L, hL, hlo, hhi, ?_⟩
  intro i hi
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hA : (1 : ℝ) ≤ principalSamplingGapRatio γ := by
    exact_mod_cast principalSamplingGapRatio_one_le γ
  have hlarge := coefficient_gap_principal_width hLr hA hγ (hh i) (hgap i hi)
    (principalSamplingGapRatio_width hγ)
  refine ⟨principalIntegerPMF (K i) ((L : ℝ) ^ h i) γ (hK i) (pow_pos hLr _) hγ hlarge, ?_, ?_⟩
  · intro k
    exact normalizedIntegerPMF_apply _ _ _ _ _ _ k
  · intro k hk
    exact principalIntegerPMF_support (hK i) (pow_pos hLr _) hγ hlarge hk

end Erdos3

end

end OAI
