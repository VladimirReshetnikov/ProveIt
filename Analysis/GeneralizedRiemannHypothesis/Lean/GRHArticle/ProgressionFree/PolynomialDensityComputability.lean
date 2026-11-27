import GRHArticle.ProgressionFree.PolynomialEffectiveApproximation
import GRHArticle.ProgressionFree.PolynomialOptimizationLower
import GRHArticle.ProgressionFree.PolynomialSmoothUpperBound

/-!
# Computing the extremal polynomial-ratio upper density

The two finite-prime bounds enclose the supremum. Combining this interval
with a rational truncation at the same precision computes a dyadic-error
approximation to the supremum over all admissible sets.
-/

namespace GRHArticle.ProgressionFree

open Filter Topology

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

/-- The full finite-prime interval with the error bound from the smooth series. -/
theorem polynomialDensityUpperApproximation_supremum_error (T : ℕ) :
    let U := polynomialDensityUpperApproximation F T
    let β := polynomialRatioDensitySupremum F
    let v := polynomialSquarefreeRoughRatio F T
    0 ≤ U - β ∧ U - β ≤ 1-v ∧ 1-v ≤ (Fintype.card F : ℝ)⁻¹^(T+1) := by
  have hv := polynomialSquarefreeRoughRatio_error F T
  have hU := polynomialDensityUpperApproximation_mem_unitInterval F T
  refine ⟨sub_nonneg.mpr (polynomialRatioDensitySupremum_le_polynomialDensityUpperApproximation F T), ?_, hv.2⟩
  calc
    _ ≤ (1-polynomialSquarefreeRoughRatio F T) * polynomialDensityUpperApproximation F T := by
      linarith only [polynomialSquarefreeRoughRatio_mul_upperApproximation_le_supremum F T]
    _ ≤ _ := mul_le_of_le_one_right hv.1 hU.2

/-- The finite-prime upper approximations converge to the extremal density. -/
theorem tendsto_polynomialDensityUpperApproximation_supremum :
    Tendsto (polynomialDensityUpperApproximation F) atTop (𝓝 (polynomialRatioDensitySupremum F)) := by
  let w := (Fintype.card F : ℝ)⁻¹
  have hq : 1 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.one_lt_card
  have hw : Tendsto (fun T : ℕ ↦ w^(T+1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (show 0 ≤ w by dsimp [w]; positivity) (inv_lt_one_of_one_lt₀ hq)).comp
      (tendsto_add_atTop_nat 1)
  have hu := (tendsto_const_nhds (f := atTop) (x := polynomialRatioDensitySupremum F)).add hw
  have hu' : Tendsto (fun T : ℕ ↦ polynomialRatioDensitySupremum F + w^(T+1)) atTop
      (𝓝 (polynomialRatioDensitySupremum F)) := by simpa only [add_zero] using hu
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu'
    (polynomialRatioDensitySupremum_le_polynomialDensityUpperApproximation F) ?_
  intro T
  have h := polynomialDensityUpperApproximation_supremum_error F T
  have he := h.2.1.trans h.2.2
  change polynomialDensityUpperApproximation F T ≤ polynomialRatioDensitySupremum F + w^(T+1)
  dsimp only [w]
  linarith only [he]

/-- Executable rational approximation to the extremal density at precision `k`. -/
def polynomialRatioDensityApprox (k : ℕ) : ℚ := polynomialSmoothDyadicApprox F k k

/-- The output of the rational program differs from the actual supremum by at
most `2^(-(k+1))` on input `k`. -/
theorem polynomialRatioDensityApprox_error (k : ℕ) :
    |(polynomialRatioDensityApprox F k : ℝ) - polynomialRatioDensitySupremum F| ≤
      (1/2:ℝ)^(k+1) := by
  have hq : (2:ℝ) ≤ Fintype.card F := by exact_mod_cast Nat.succ_le_of_lt (Fintype.one_lt_card (α := F))
  have hz : (Fintype.card F : ℝ)⁻¹ ≤ 1/2 := by
    rw [one_div]
    exact inv_anti₀ (by norm_num) hq
  obtain ⟨hl, hm, he⟩ := polynomialDensityUpperApproximation_supremum_error F k
  have hβ := (hm.trans he).trans (pow_le_pow_left₀ (by positivity) hz _)
  obtain ⟨h₀, h₁⟩ := polynomialSmoothDyadicApprox_error F k k
  unfold polynomialRatioDensityApprox
  apply abs_le.mpr
  constructor <;> linarith

end GRHArticle.ProgressionFree
