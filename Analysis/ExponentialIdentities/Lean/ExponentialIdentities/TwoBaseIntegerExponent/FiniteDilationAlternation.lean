import Mathlib

/-!
# Finite dilation filters preserve strict coefficient alternation

For a formal power series with coefficients `a n`, the finite dilation filter

`f(z) ↦ ∑ i, c i * f(s i * z)`

multiplies the coefficient of degree `n` by `∑ i, c i * (s i) ^ n`.  If all
weights are nonnegative, all scales are positive, and at least one weight is
positive, this multiplier is positive in every degree.  More generally, for
arbitrary real weights, a unique largest positive scale has asymptotically
dominant weight.  In either case a strictly alternating coefficient tail stays
strictly alternating (up to one global reversal of sign).

This is finite real algebra and elementary convergence; no assertion about the
existence of an interpolant is made here.
-/

namespace LeanProofs.TwoBaseIntegerExponent
namespace FiniteDilationAlternation

open Filter
open scoped BigOperators Topology

/-- The coefficient multiplier of a finite linear combination of dilations. -/
def dilationMultiplier {I : Type*} [Fintype I]
    (c s : I → ℝ) (n : ℕ) : ℝ :=
  ∑ i, c i * s i ^ n

/-- A nonzero positive finite dilation filter has a strictly positive
coefficient multiplier in every degree. -/
theorem dilationMultiplier_pos_of_nonnegative
    {I : Type*} [Fintype I]
    (c s : I → ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hs : ∀ i, 0 < s i)
    (hactive : ∃ i, 0 < c i)
    (n : ℕ) :
    0 < dilationMultiplier c s n := by
  classical
  obtain ⟨i₀, hi₀⟩ := hactive
  unfold dilationMultiplier
  apply Finset.sum_pos' (fun i _ ↦ mul_nonneg (hc i) (pow_nonneg (hs i).le n))
  exact ⟨i₀, Finset.mem_univ _, mul_pos hi₀ (pow_pos (hs i₀) n)⟩

/-- Positive finite dilation filters preserve any specified strict alternating
tail, with no loss in the starting index. -/
theorem eventually_strictAlternating_positiveDilation
    {I : Type*} [Fintype I]
    (a : ℕ → ℝ) (c s : I → ℝ) (orientation : ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hs : ∀ i, 0 < s i)
    (hactive : ∃ i, 0 < c i)
    (ha : ∀ᶠ n in atTop, 0 < orientation * (-1 : ℝ) ^ n * a n) :
    ∀ᶠ n in atTop,
      0 < orientation * (-1 : ℝ) ^ n *
        (a n * dilationMultiplier c s n) := by
  filter_upwards [ha] with n hn
  have hmult := dilationMultiplier_pos_of_nonnegative c s hc hs hactive n
  nlinarith [mul_pos hn hmult]

/-- A genuinely strict alternating tail cannot be eventually nonnegative. -/
theorem not_eventually_nonnegative_of_strictAlternating
    (a : ℕ → ℝ) (orientation : ℝ)
    (horientation : orientation ≠ 0)
    (ha : ∀ᶠ n in atTop, 0 < orientation * (-1 : ℝ) ^ n * a n) :
    ¬ ∀ᶠ n in atTop, 0 ≤ a n := by
  intro hnonneg
  obtain ⟨N, hN⟩ := eventually_atTop.1 ha
  obtain ⟨K, hK⟩ := eventually_atTop.1 hnonneg
  rcases lt_or_gt_of_ne horientation with horientation_neg | horientation_pos
  · let n := 2 * (N + K)
    have hNn : N ≤ n := by dsimp [n]; omega
    have hKn : K ≤ n := by dsimp [n]; omega
    have halt := hN n hNn
    have hnonneg' := hK n hKn
    have hpow : (-1 : ℝ) ^ n = 1 := by simp [n, pow_mul]
    rw [hpow] at halt
    nlinarith
  · let n := 2 * (N + K) + 1
    have hNn : N ≤ n := by dsimp [n]; omega
    have hKn : K ≤ n := by dsimp [n]; omega
    have halt := hN n hNn
    have hnonneg' := hK n hKn
    have hpow : (-1 : ℝ) ^ n = -1 := by simp [n, pow_succ, pow_mul]
    rw [hpow] at halt
    nlinarith

/-- After normalization by a distinguished strictly largest positive scale,
the multiplier tends to the coefficient at that scale. -/
theorem dilationMultiplier_normalized_tendsto
    {I : Type*} [Fintype I]
    (c s : I → ℝ) (i₀ : I)
    (hs : ∀ i, 0 < s i)
    (hmax : ∀ i, i ≠ i₀ → c i ≠ 0 → s i < s i₀) :
    Tendsto
      (fun n ↦ ∑ i, c i * (s i / s i₀) ^ n)
      atTop (nhds (c i₀)) := by
  classical
  have hterm (i : I) :
      Tendsto (fun n ↦ c i * (s i / s i₀) ^ n) atTop
        (nhds (if i = i₀ then c i₀ else 0)) := by
    by_cases hi : i = i₀
    · subst i
      simp [div_self (ne_of_gt (hs i₀))]
    · by_cases hci : c i = 0
      · simp [hi, hci]
      · have hratio_nonneg : 0 ≤ s i / s i₀ := div_nonneg (hs i).le (hs i₀).le
        have hratio_lt : s i / s i₀ < 1 :=
          (div_lt_one (hs i₀)).2 (hmax i hi hci)
        simpa [hi] using
          (tendsto_pow_atTop_nhds_zero_of_lt_one hratio_nonneg hratio_lt).const_mul (c i)
  have hsum := tendsto_finsetSum Finset.univ (fun i _ ↦ hterm i)
  simpa [Finset.sum_ite_irrel, Finset.filter_eq'] using hsum

/-- For arbitrary real weights, the weight at a unique largest positive scale
eventually fixes the sign of the complete dilation multiplier. -/
theorem eventually_dilationMultiplier_sameSign_of_uniqueMax
    {I : Type*} [Fintype I]
    (c s : I → ℝ) (i₀ : I)
    (hs : ∀ i, 0 < s i)
    (hmax : ∀ i, i ≠ i₀ → c i ≠ 0 → s i < s i₀)
    (hactive : c i₀ ≠ 0) :
    ∀ᶠ n in atTop, 0 < c i₀ * dilationMultiplier c s n := by
  classical
  have hlim := dilationMultiplier_normalized_tendsto c s i₀ hs hmax
  have hnormalized :
      ∀ᶠ n in atTop, 0 < c i₀ * (∑ i, c i * (s i / s i₀) ^ n) := by
    have htends : Tendsto
        (fun n ↦ c i₀ * (∑ i, c i * (s i / s i₀) ^ n))
        atTop (nhds (c i₀ * c i₀)) :=
      tendsto_const_nhds.mul hlim
    exact htends.eventually (Ioi_mem_nhds (mul_self_pos.mpr hactive))
  filter_upwards [hnormalized] with n hn
  have hscale : 0 < s i₀ ^ n := pow_pos (hs i₀) n
  have hfactor :
      dilationMultiplier c s n =
        s i₀ ^ n * (∑ i, c i * (s i / s i₀) ^ n) := by
    unfold dilationMultiplier
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hbase : s i₀ * (s i / s i₀) = s i := by
      field_simp [ne_of_gt (hs i₀)]
    calc
      c i * s i ^ n = c i * (s i₀ * (s i / s i₀)) ^ n := by rw [hbase]
      _ = s i₀ ^ n * (c i * (s i / s i₀) ^ n) := by rw [mul_pow]; ring
  rw [hfactor]
  nlinarith [mul_pos hscale hn]

/-- A finite signed dilation filter with a unique largest active scale cannot
destroy a strictly alternating tail.  Its leading weight can only reverse the
global orientation. -/
theorem eventually_strictAlternating_finiteDilation_uniqueMax
    {I : Type*} [Fintype I]
    (a : ℕ → ℝ) (c s : I → ℝ) (i₀ : I) (orientation : ℝ)
    (hs : ∀ i, 0 < s i)
    (hmax : ∀ i, i ≠ i₀ → c i ≠ 0 → s i < s i₀)
    (hactive : c i₀ ≠ 0)
    (ha : ∀ᶠ n in atTop, 0 < orientation * (-1 : ℝ) ^ n * a n) :
    ∀ᶠ n in atTop,
      0 < (orientation * c i₀) * (-1 : ℝ) ^ n *
        (a n * dilationMultiplier c s n) := by
  have hmult := eventually_dilationMultiplier_sameSign_of_uniqueMax
    c s i₀ hs hmax hactive
  filter_upwards [ha, hmult] with n hn hm
  nlinarith [mul_pos hn hm]

/-- In particular, no nonzero finite signed dilation filter with a unique
largest active positive scale can turn a strict alternating tail into an
eventually nonnegative sequence. -/
theorem not_eventually_nonnegative_finiteDilation_uniqueMax
    {I : Type*} [Fintype I]
    (a : ℕ → ℝ) (c s : I → ℝ) (i₀ : I) (orientation : ℝ)
    (hs : ∀ i, 0 < s i)
    (hmax : ∀ i, i ≠ i₀ → c i ≠ 0 → s i < s i₀)
    (hactive : c i₀ ≠ 0)
    (horientation : orientation ≠ 0)
    (ha : ∀ᶠ n in atTop, 0 < orientation * (-1 : ℝ) ^ n * a n) :
    ¬ ∀ᶠ n in atTop, 0 ≤ a n * dilationMultiplier c s n := by
  apply not_eventually_nonnegative_of_strictAlternating
    (fun n ↦ a n * dilationMultiplier c s n) (orientation * c i₀)
  · exact mul_ne_zero horientation hactive
  · exact eventually_strictAlternating_finiteDilation_uniqueMax
      a c s i₀ orientation hs hmax hactive ha

end FiniteDilationAlternation
end LeanProofs.TwoBaseIntegerExponent
