import OAI.Combinatorics.Progressions.Estimates.UniformScaledRetainedLogBounds

namespace OAI

section

namespace Erdos3

def uniformRetainedComplexityLog {A : Type*} [Semiring A]
    (n j t : ℕ) (p v w E : A) : A :=
  uniformSpectrumSizeLog n j t p v w + 2 + uniformSpectrumCardLog n j t p v w E +
    uniformRetainedFrequencyLog n j t p v w E + uniformRetainedDenominatorLog n j t p v w E

theorem uniformRetainedComplexityLog_bounds (n j t : ℕ) {p v w E : ℝ}
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) (hE : 0 ≤ E) :
    0 ≤ uniformRetainedComplexityLog n j t p v w E ∧
      uniformSpectrumSizeLog n j t p v w + 2 ≤ uniformRetainedComplexityLog n j t p v w E ∧
      uniformSpectrumCardLog n j t p v w E ≤ uniformRetainedComplexityLog n j t p v w E ∧
      uniformRetainedFrequencyLog n j t p v w E ≤ uniformRetainedComplexityLog n j t p v w E ∧
      uniformRetainedDenominatorLog n j t p v w E ≤ uniformRetainedComplexityLog n j t p v w E := by
  have hS := (uniformSpectrumLogs_nonneg n j t hp hv hw).2.2
  obtain ⟨_, hC, hF, hD⟩ := uniformRetainedLogs_nonneg n j t hp hv hw hE
  unfold uniformRetainedComplexityLog
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem uniformRetainedComplexity_exp_bounds (n j t : ℕ) {U V W ε p v w E : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) (hE : 0 ≤ E)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) (hWw : W ≤ Real.exp w)
    (hεE : ε⁻¹ ≤ Real.exp E) :
    let ζ := uniformBlockRetainedBias n j t U V W ε
    let Λ := uniformRetainedComplexityLog n j t p v w E
    uniformSpectrumAbsoluteCap n j t U V W + 1 ≤ Real.exp Λ ∧
      uniformSpectrumSizeConstant n j t U V W /
        ε ^ max (majorArcSpectrumExponent n j) (majorArcLengthExponent n * t) ≤ Real.exp Λ ∧
      2 * majorArcCoverConstant n j U V / ζ ^ majorArcCoverExponent n j ≤ Real.exp Λ ∧
      uniformCharacterDenominatorBound n j t U V W ζ ≤ Real.exp Λ := by
  obtain ⟨_, hS, hC, hF, hD⟩ := uniformRetainedComplexityLog_bounds n j t hp hv hw hE
  have hcap := uniformSpectrumAbsoluteCap_exp_bound n j t hU hV hW hp hv hw hUp hVv hWw
  have hS0 := (uniformSpectrumLogs_nonneg n j t hp hv hw).2.2
  have hplus := one_add_le_exp_succ (by positivity : 0 ≤ uniformSpectrumSizeLog n j t p v w + 1) hcap
  have hcap' : uniformSpectrumAbsoluteCap n j t U V W + 1 ≤
      Real.exp (uniformSpectrumSizeLog n j t p v w + 2) := by
    rw [add_comm (uniformSpectrumAbsoluteCap n j t U V W) 1]
    simpa only [add_assoc, one_add_one_eq_two] using hplus
  exact ⟨hcap'.trans (Real.exp_le_exp.mpr hS),
    (uniformSpectrumCardBound_exp_bound n j t hU hV hW hε hp hv hw hE hUp hVv hWw hεE).trans
      (Real.exp_le_exp.mpr hC),
    (uniformRetainedFrequency_exp_bound n j t hU hV hW hε hε1 hp hv hw hE hUp hVv hWw hεE).trans
      (Real.exp_le_exp.mpr hF),
    (uniformCharacterDenominatorBound_exp_bound n j t hU hV hW hε hε1 hp hv hw hE hUp hVv hWw hεE).trans
      (Real.exp_le_exp.mpr hD)⟩

theorem exists_uniformRetainedComplexityLog_bound (n j t : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ p : ℝ, 0 ≤ p →
      uniformRetainedComplexityLog n j t p p p p ≤ (p + a) ^ a := by
  let poly : Polynomial ℕ :=
    uniformRetainedComplexityLog n j t Polynomial.X Polynomial.X Polynomial.X Polynomial.X
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro p hp
  simpa [poly, uniformRetainedComplexityLog, uniformSpectrumSizeLog, uniformSpectrumCardLog,
    uniformRetainedFrequencyLog, uniformRetainedDenominatorLog, uniformRetainedBiasLog,
    uniformBlockAccuracyLog, majorArcSpectrumLog, majorArcCoverLog, majorArcLengthLog,
    majorArcBiasLog, majorArcErrorLog, majorArcLocalizationLog, Polynomial.eval₂_pow] using hbound p hp

end Erdos3

end

end OAI
