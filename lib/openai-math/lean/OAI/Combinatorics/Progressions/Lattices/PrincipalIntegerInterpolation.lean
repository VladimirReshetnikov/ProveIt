import OAI.Combinatorics.Progressions.Probability.PrincipalCoefficientLaw

namespace OAI

section

namespace Erdos3

noncomputable def principalIntegerInterpolation (K T γ x : ℝ) : ℝ :=
  T * normalizedIntegerInterpolation (K / T) (3 * γ / 2) (γ / 2) (T*x)

theorem principalIntegerInterpolation_grid (K T γ : ℝ) (hK : 0 < K) (hT : 0 < T)
    (hγ : 0 < γ) (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T)) (k : ℤ) :
    principalIntegerInterpolation K T γ ((k : ℝ) / K) =
      K * (principalIntegerPMF K T γ hK hT hγ hlarge k).toReal := by
  unfold principalIntegerInterpolation principalIntegerPMF
  rw [show T*((k : ℝ)/K) = (k : ℝ)/(K/T) by field_simp,
    normalizedIntegerInterpolation_grid _ _ _ (div_pos hK hT) (by positivity) hlarge]
  field_simp

theorem principalIntegerInterpolation_range (K T γ : ℝ) (hK : 0 < K) (hT : 0 < T)
    (hγ : 0 < γ) (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T)) (x : ℝ) :
    0 ≤ principalIntegerInterpolation K T γ x ∧ principalIntegerInterpolation K T γ x ≤ 4*T/γ := by
  have h := normalizedIntegerInterpolation_range (K/T) (3*γ/2) (γ/2)
    (div_pos hK hT) (by positivity) hlarge (T*x)
  refine ⟨mul_nonneg hT.le h.1, ?_⟩
  exact (mul_le_mul_of_nonneg_left h.2 hT.le).trans_eq (by ring)

theorem principalIntegerInterpolation_difference (K T γ : ℝ) (hK : 0 < K) (hT : 0 < T)
    (hγ : 0 < γ) (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T)) (x y : ℝ) :
    |principalIntegerInterpolation K T γ x - principalIntegerInterpolation K T γ y| ≤
      (8 * (probabilityProfileLipschitz : ℝ) * T^2 / γ^2) * |x-y| := by
  have h := normalizedIntegerInterpolation_difference (K/T) (3*γ/2) (γ/2)
    (div_pos hK hT) (by positivity) hlarge (T*x) (T*y)
  rw [← mul_sub, abs_mul, abs_of_pos hT] at h
  unfold principalIntegerInterpolation
  rw [← mul_sub, abs_mul, abs_of_pos hT]
  exact (mul_le_mul_of_nonneg_left h hT.le).trans_eq (by ring)

theorem principalIntegerInterpolation_spec (K T γ : ℝ) (hK : 0 < K) (hT : 0 < T)
    (hγ : 0 < γ) (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T)) :
    IsIntegerMassInterpolation K (principalIntegerPMF K T γ hK hT hγ hlarge)
      (4*T/γ) (8 * (probabilityProfileLipschitz : ℝ) * T^2 / γ^2) (principalIntegerInterpolation K T γ) :=
  ⟨principalIntegerInterpolation_grid K T γ hK hT hγ hlarge,
    principalIntegerInterpolation_range K T γ hK hT hγ hlarge,
    principalIntegerInterpolation_difference K T γ hK hT hγ hlarge⟩

end Erdos3

end

end OAI
