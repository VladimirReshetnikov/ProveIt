import OAI.Combinatorics.Progressions.Estimates.NormalizedMeshLengths

namespace OAI

section

namespace Erdos3

theorem affinePhysicalScales_lower {H L Q : ℝ} {exponent : ℕ}
    (hL : 1 ≤ L) (hQ : 0 ≤ Q) (hexponent : 1 ≤ exponent)
    (hH : Q * L ^ exponent ≤ H) : Q ≤ H ∧ Q ≤ H / L := by
  have hpower : L ≤ L ^ exponent := by
    simpa only [pow_one] using pow_le_pow_right₀ hL hexponent
  have hQL : Q * L ≤ H := (mul_le_mul_of_nonneg_left hpower hQ).trans hH
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  refine ⟨?_, (le_div_iff₀ hLpos).mpr hQL⟩
  exact (by nlinarith : Q ≤ Q * L).trans hQL

theorem affineParameterScale_lower {L Q P : ℝ} {D : ℕ}
    (hD : 0 < D) (hQ : 0 ≤ Q) (hDlog : (D : ℝ) ≤ Real.exp P)
    (hL : Q * Real.exp P ≤ L) : Q ≤ L / (D : ℝ) := by
  apply (le_div_iff₀ (by exact_mod_cast hD : (0 : ℝ) < D)).mpr
  exact (mul_le_mul_of_nonneg_left hDlog hQ).trans hL

theorem affineNormalizedScales_lower {I J : Type*} (H : I → ℝ)
    {L inverseLog lengthLog parameterLog : ℝ} {D exponent : ℕ}
    (hL : 1 ≤ L) (hD : 0 < D) (hexponent : 1 ≤ exponent)
    (hDlog : (D : ℝ) ≤ Real.exp parameterLog)
    (hparam : 4 * Real.exp (inverseLog + lengthLog + parameterLog) ≤ L)
    (hsite : ∀ i, 4 * Real.exp (inverseLog + lengthLog) * L ^ exponent ≤ H i) :
    (∀ i, 4 * Real.exp (inverseLog + lengthLog) ≤ H i) ∧
    (∀ z : Option J × I, 4 * Real.exp (inverseLog + lengthLog) ≤
      smoothPairCoefficientScale (H z.2) L z.1) ∧
    4 * Real.exp (inverseLog + lengthLog) ≤ L / (D : ℝ) := by
  have hQ : 0 ≤ 4 * Real.exp (inverseLog + lengthLog) := by positivity
  have hs (i) := affinePhysicalScales_lower hL hQ hexponent (hsite i)
  refine ⟨fun i => (hs i).1, ?_, ?_⟩
  · rintro ⟨j,i⟩
    cases j with
    | none => exact (hs i).1
    | some j => exact (hs i).2
  · apply affineParameterScale_lower hD hQ hDlog
    simpa only [Real.exp_add, mul_assoc] using hparam

end Erdos3

end

end OAI
