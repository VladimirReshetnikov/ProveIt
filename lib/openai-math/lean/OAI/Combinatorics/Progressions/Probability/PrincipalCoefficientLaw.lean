import OAI.Combinatorics.Progressions.Lattices.IntegerRowInterpolationMixture

namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def principalRealDensity (T γ : ℝ) : ℝ → ℝ :=
  affineProbabilityProfile (3 * γ / 2 / T) (γ / 2 / T)

theorem principalRealDensity_support {T γ x : ℝ} (hT : 0 < T) (hγ : 0 < γ)
    (hx : principalRealDensity T γ x ≠ 0) : γ < T * x ∧ T * x < 2 * γ := by
  have hb := affineProbabilityProfile_support (3 * γ / 2 / T)
    (div_pos (by positivity : 0 < γ / 2) hT) hx
  have hlo := (abs_lt.mp hb).1
  have hhi := (abs_lt.mp hb).2
  have hlo' := (mul_lt_mul_of_pos_left hlo hT)
  have hhi' := (mul_lt_mul_of_pos_left hhi hT)
  field_simp at hlo' hhi'
  constructor <;> nlinarith

theorem principalRealDensity_probability {T γ : ℝ} (hT : 0 < T) (hγ : 0 < γ) :
    IsProbabilityMeasure (realDensityMeasure volume (principalRealDensity T γ)) :=
  affineCoefficientMeasure_probability _ (div_pos (by positivity : 0 < γ / 2) hT)

theorem principalRealDensity_ae {T γ : ℝ} (hT : 0 < T) (hγ : 0 < γ) :
    ∀ᵐ x ∂realDensityMeasure volume (principalRealDensity T γ),
      γ ≤ |T * x| ∧ |T * x| ≤ 2 * γ := by
  apply realDensityMeasure_ae_of_support volume _
    (affineProbabilityProfile_contDiff _ _).continuous.measurable
  intro x hx
  have hb := principalRealDensity_support hT hγ hx
  rw [abs_of_pos (hγ.trans hb.1)]
  exact ⟨hb.1.le, hb.2.le⟩

noncomputable def principalIntegerPMF (K T γ : ℝ) (hK : 0 < K) (hT : 0 < T)
    (hγ : 0 < γ) (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T)) : PMF ℤ :=
  normalizedIntegerPMF (K / T) (3 * γ / 2) (γ / 2) (div_pos hK hT) (by positivity) hlarge

theorem principalIntegerPMF_support {K T γ : ℝ} (hK : 0 < K) (hT : 0 < T)
    (hγ : 0 < γ) (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T))
    {k : ℤ} (hk : k ∈ (principalIntegerPMF K T γ hK hT hγ hlarge).support) :
    γ < T * (k : ℝ) / K ∧ T * (k : ℝ) / K < 2 * γ := by
  have hb := normalizedIntegerPMF_support (K / T) (3 * γ / 2) (γ / 2)
    (div_pos hK hT) (by positivity) hlarge hk
  have he : (k : ℝ) / (K / T) = T * (k : ℝ) / K := by field_simp
  rw [he] at hb
  constructor <;> nlinarith [(abs_lt.mp hb).1, (abs_lt.mp hb).2]

theorem principalIntegerPMF_ae {K T γ : ℝ} (hK : 0 < K) (hT : 0 < T)
    (hγ : 0 < γ) (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T)) :
    ∀ᵐ (k : ℤ) ∂(principalIntegerPMF K T γ hK hT hγ hlarge).toMeasure,
      γ ≤ |T * (k : ℝ) / K| ∧ |T * (k : ℝ) / K| ≤ 2 * γ := by
  filter_upwards [pmf_support_ae (principalIntegerPMF K T γ hK hT hγ hlarge)] with k hk
  have hb := principalIntegerPMF_support hK hT hγ hlarge hk
  rw [abs_of_pos (hγ.trans hb.1)]
  exact ⟨hb.1.le, hb.2.le⟩

end Erdos3

end

end OAI
