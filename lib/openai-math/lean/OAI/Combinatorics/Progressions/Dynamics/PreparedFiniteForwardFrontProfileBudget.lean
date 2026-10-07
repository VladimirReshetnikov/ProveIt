import OAI.Combinatorics.Progressions.Linear.AllocatedExternalCandidateCommonKeepPositiveKernelPreparation

namespace OAI

section

namespace Erdos3.VectorPolynomial
open AllocatedExternalCandidateProblem

theorem exists_preparedFiniteForwardFrontProfile_budget (e : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (A : ℕ), C ≤ A →
      ∀ (stageCountConstant : ℕ → ℕ) {x p gainLog stageLog : ℝ},
      0 ≤ x → p ∈ Set.Icc 0 x → gainLog ∈ Set.Icc 0 x → stageLog ∈ Set.Icc 0 x →
      2 * p + 3 ≤ preparedFiniteForwardWork A stageCountConstant 0 x ∧
      positiveKernelPreparationParameter (2 * p) ≤
        preparedFiniteForwardWork A stageCountConstant 0 x ∧
      positiveKernelMarkovPrecisionParameter (2 * p) e ≤
        preparedFiniteForwardModelPrecision A stageCountConstant 0 x gainLog stageLog := by
  obtain ⟨K, _, hparameters⟩ := exists_positiveKernelPreparationParameters_bound e
  let Q : Polynomial ℕ := (2 * Polynomial.X + Polynomial.C K) ^ K
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro A hCA stageCountConstant x p gainLog stageLog hx hp hg hs
  have hp2 : 0 ≤ 2 * p := mul_nonneg (by norm_num) hp.1
  have hparameters' := hparameters (2 * p) hp2
  have hscaled : (2 * p + K) ^ K ≤ (2 * x + K) ^ K :=
    pow_le_pow_left₀ (add_nonneg hp2 (Nat.cast_nonneg K))
      (add_le_add (mul_le_mul_of_nonneg_left hp.2 (by norm_num)) le_rfl) K
  have hpoly : (2 * x + K) ^ K ≤ (x + C) ^ C := by
    simpa [Q, Polynomial.eval₂_pow] using hbudget x hx
  have hwork : (2 * p + K) ^ K ≤ preparedFiniteForwardWork A stageCountConstant 0 x :=
    hscaled.trans (hpoly.trans
      (preparedFiniteForward_shiftedPower_le_work A C stageCountConstant 0
        (hC.trans hCA) hCA hx))
  have hmodel : preparedFiniteForwardWork A stageCountConstant 0 x ≤
      preparedFiniteForwardModelPrecision A stageCountConstant 0 x gainLog stageLog := by
    simp only [preparedFiniteForwardModelPrecision, preparedFiniteForwardPrefixLog,
      Finset.range_zero, Finset.sum_empty, zero_add]
    linarith only [hg.1, hs.1]
  exact ⟨hparameters'.1.trans hwork, hparameters'.2.1.trans hwork,
    hparameters'.2.2.2.2.trans (hwork.trans hmodel)⟩

noncomputable def preparedFiniteForwardFrontProfileExponent (e : ℕ) : ℕ :=
  Classical.choose (exists_preparedFiniteForwardFrontProfile_budget e)

theorem preparedFiniteForwardFrontProfileExponent_two_le (e : ℕ) :
    2 ≤ preparedFiniteForwardFrontProfileExponent e :=
  (Classical.choose_spec (exists_preparedFiniteForwardFrontProfile_budget e)).1

theorem preparedFiniteForwardFrontProfile_bounds (e A : ℕ)
    (stageCountConstant : ℕ → ℕ) {x p gainLog stageLog : ℝ}
    (hA : preparedFiniteForwardFrontProfileExponent e ≤ A)
    (hx : 0 ≤ x) (hp : p ∈ Set.Icc 0 x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x) :
    2 * p + 3 ≤ preparedFiniteForwardWork A stageCountConstant 0 x ∧
    positiveKernelPreparationParameter (2 * p) ≤
      preparedFiniteForwardWork A stageCountConstant 0 x ∧
    positiveKernelMarkovPrecisionParameter (2 * p) e ≤
      preparedFiniteForwardModelPrecision A stageCountConstant 0 x gainLog stageLog :=
  (Classical.choose_spec (exists_preparedFiniteForwardFrontProfile_budget e)).2
    A hA stageCountConstant hx hp hg hs

theorem preparedFiniteForwardFrontProfile_slice_bound (Cslice : ℕ)
    {x p : ℝ} (hCslice : 1 ≤ Cslice) (hx : 0 ≤ x) (hp : p ≤ x) :
    p ≤ (x + Cslice) ^ Cslice := by
  have hC : (1 : ℝ) ≤ Cslice := by exact_mod_cast hCslice
  have hbase : 1 ≤ x + Cslice := by linarith only [hx, hC]
  apply hp.trans
  apply (le_add_of_nonneg_right (Nat.cast_nonneg Cslice)).trans
  simpa only [pow_one] using pow_le_pow_right₀ hbase hCslice

end Erdos3.VectorPolynomial

end

end OAI
