import FabiusFunction.FabiusRawQBinomialFormula
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

set_option autoImplicit false

open scoped BigOperators Topology
open Finset Filter

namespace Fabius

noncomputable section

/-- Number of terms in the inner prefix at scale `p`.  This is nearest-integer
rounding with half-integers rounded upward. -/
def fabiusDiscreteLimitRangeLength (x : ℝ) (p : ℕ) : ℕ :=
  ⌊(2 : ℝ) ^ p * x + 1 / 2⌋₊

/-- The range length is the successor of the user's inclusive Wolfram upper
bound `Floor[2^p*x-1/2]`.  Thus `range length` is exactly the safe Lean
encoding of that sum, including the empty case where the upper bound is `-1`. -/
theorem fabiusDiscreteLimitRangeLength_eq_floor_add_one
    {x : ℝ} (hx : 0 ≤ x) (p : ℕ) :
    (fabiusDiscreteLimitRangeLength x p : ℤ) =
      ⌊(2 : ℝ) ^ p * x - 1 / 2⌋ + 1 := by
  rw [fabiusDiscreteLimitRangeLength]
  have hnonneg : 0 ≤ (2 : ℝ) ^ p * x + 1 / 2 := by positivity
  rw [Int.natCast_floor_eq_floor hnonneg]
  rw [show (2 : ℝ) ^ p * x + 1 / 2 =
      ((2 : ℝ) ^ p * x - 1 / 2) + 1 by ring,
    Int.floor_add_one]

theorem fabiusDiscreteLimitRangeLength_eq_zero_iff
    (x : ℝ) (p : ℕ) :
    fabiusDiscreteLimitRangeLength x p = 0 ↔
      (2 : ℝ) ^ p * x < 1 / 2 := by
  rw [fabiusDiscreteLimitRangeLength, Nat.floor_eq_zero]
  constructor <;> intro h <;> linarith

/-- The literal finite expression inside the user's `DiscreteLimit`.  The
inner finite range has length `floor(2^(n+k)*x+1/2)`, equivalently inclusive
upper endpoint `floor(2^(n+k)*x-1/2)` when `x ≥ 0`. -/
def fabiusDiscreteLimitApproximation
    (K : Type*) [RCLike K] (q : K) (x : ℝ) (n : ℕ) : K :=
  (1 / ((2 : K) ^ (n ^ 2) * (halfQPochhammer n : K))) *
    ∑ k ∈ Finset.range (n + 1),
      ((halfQBinomial n k : K) /
          ((4 : K) ^ k.choose 2 * ((n + k).factorial : K))) *
        ∑ r ∈ Finset.range (fabiusDiscreteLimitRangeLength x (n + k)),
          (-1 : K) ^ thueMorseBit r *
            ((r : K) - (2 : K) ^ (n + k) * (x : K) + q) ^ (n + k)

/-- Rational translation, evaluated in the real scalar field. -/
def fabiusDiscreteLimitApproximationRat
    (q : ℚ) (x : ℝ) (n : ℕ) : ℝ :=
  fabiusDiscreteLimitApproximation ℝ (q : ℝ) x n

/-- A translation in the Gaussian rationals, evaluated in `ℂ`. -/
def fabiusDiscreteLimitApproximationGaussianRat
    (a b : ℚ) (x : ℝ) (n : ℕ) : ℂ :=
  fabiusDiscreteLimitApproximation ℂ
    ((a : ℂ) + (b : ℂ) * Complex.I) x n

/-- Arbitrary real translation. -/
def fabiusDiscreteLimitApproximationReal
    (q x : ℝ) (n : ℕ) : ℝ :=
  fabiusDiscreteLimitApproximation ℝ q x n

/-- Arbitrary complex translation. -/
def fabiusDiscreteLimitApproximationComplex
    (q : ℂ) (x : ℝ) (n : ℕ) : ℂ :=
  fabiusDiscreteLimitApproximation ℂ q x n

private theorem choose_succ_two_toeplitz (j : ℕ) :
    (j + 1).choose 2 = j.choose 2 + j := by
  rw [show j + 1 = Nat.succ j by omega, Nat.choose_succ_succ]
  simp [Nat.choose_one_right, add_comm]

/-- The outer Toeplitz weight obtained by putting `j = n-k` in the user's
q-binomial approximant. -/
def discreteLimitWeight (n j : ℕ) : ℚ :=
  (-1 : ℚ) ^ j * halfQBinomial n j *
      (1 / 2 : ℚ) ^ ((j + 1).choose 2) /
    halfQPochhammer n

theorem sum_range_discreteLimitWeight (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), discreteLimitWeight n j) = 1 := by
  simp_rw [discreteLimitWeight]
  rw [← Finset.sum_div]
  simp_rw [choose_succ_two_toeplitz, pow_add]
  have h := halfQBinomial_theorem n (1 / 2)
  rw [show finiteQPochhammer (1 / 2) (1 / 2) n =
      halfQPochhammer n by rfl] at h
  have hnum :
      (∑ j ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ j * halfQBinomial n j *
          ((1 / 2 : ℚ) ^ j.choose 2 * (1 / 2 : ℚ) ^ j)) =
        halfQPochhammer n := by
    rw [← h]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  rw [hnum]
  exact div_self (halfQPochhammer_ne_zero n)

private theorem quarter_add_pow_le_halfQPochhammer_succ (n : ℕ) :
    (1 / 4 : ℚ) + (1 / 2 : ℚ) ^ (n + 2) ≤
      halfQPochhammer (n + 1) := by
  induction n with
  | zero => norm_num [halfQPochhammer_succ]
  | succ n ih =>
      rw [halfQPochhammer_succ]
      have hpow_nonneg : 0 ≤ (1 / 2 : ℚ) ^ (n + 2) := by positivity
      have hpow_le : (1 / 2 : ℚ) ^ (n + 2) ≤ 1 / 4 := by
        rw [show n + 2 = 2 + n by omega, pow_add]
        norm_num
        exact pow_le_one₀ (by norm_num) (by norm_num)
      have hfac_nonneg : 0 ≤ 1 - (1 / 2 : ℚ) ^ (n + 2) := by linarith
      have hmul := mul_le_mul_of_nonneg_right ih hfac_nonneg
      calc
        (1 / 4 : ℚ) + (1 / 2 : ℚ) ^ (n + 3) ≤
            ((1 / 4 : ℚ) + (1 / 2 : ℚ) ^ (n + 2)) *
              (1 - (1 / 2 : ℚ) ^ (n + 2)) := by
                rw [show n + 3 = (n + 2) + 1 by omega, pow_succ]
                nlinarith
        _ ≤ halfQPochhammer (n + 1) *
              (1 - (1 / 2 : ℚ) ^ (n + 2)) := hmul

theorem one_fourth_le_halfQPochhammer (n : ℕ) :
    (1 / 4 : ℚ) ≤ halfQPochhammer n := by
  cases n with
  | zero => norm_num
  | succ n =>
      exact le_trans (le_add_of_nonneg_right (by positivity))
        (quarter_add_pow_le_halfQPochhammer_succ n)

private theorem finiteQPochhammer_neg_half_mul_half_le_one (n : ℕ) :
    finiteQPochhammer (-1 / 2) (1 / 2) n * halfQPochhammer n ≤ 1 := by
  rw [finiteQPochhammer, halfQPochhammer, finiteQPochhammer,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_le_one
  · intro j _hj
    let a : ℚ := (1 / 2 : ℚ) ^ (j + 1)
    have ha0 : 0 ≤ a := by dsimp [a]; positivity
    have ha1 : a ≤ 1 := by
      dsimp [a]
      exact pow_le_one₀ (by norm_num) (by norm_num)
    have hterm :
        (1 - (-1 / 2 : ℚ) * (1 / 2 : ℚ) ^ j) *
            (1 - (1 / 2 : ℚ) * (1 / 2 : ℚ) ^ j) =
          (1 + a) * (1 - a) := by
      dsimp [a]
      rw [pow_succ]
      ring
    rw [hterm]
    nlinarith
  · intro j _hj
    let a : ℚ := (1 / 2 : ℚ) ^ (j + 1)
    have hsquare : 0 ≤ a ^ 2 := sq_nonneg _
    have hterm :
        (1 - (-1 / 2 : ℚ) * (1 / 2 : ℚ) ^ j) *
            (1 - (1 / 2 : ℚ) * (1 / 2 : ℚ) ^ j) =
          (1 + a) * (1 - a) := by
      dsimp [a]
      rw [pow_succ]
      ring
    rw [hterm]
    nlinarith

private theorem abs_discreteLimitWeight {n j : ℕ} (hj : j ≤ n) :
    |discreteLimitWeight n j| =
      halfQBinomial n j * (1 / 2 : ℚ) ^ ((j + 1).choose 2) /
        halfQPochhammer n := by
  rw [discreteLimitWeight, abs_div, abs_mul, abs_mul, abs_pow, abs_pow]
  rw [abs_of_pos (halfQBinomial_pos hj),
    abs_of_pos (halfQPochhammer_pos n)]
  norm_num

theorem sum_abs_discreteLimitWeight_le (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), |discreteLimitWeight n j|) ≤ 16 := by
  have hplus := halfQBinomial_theorem n (-1 / 2)
  have hsum :
      (∑ j ∈ Finset.range (n + 1),
          halfQBinomial n j *
            (1 / 2 : ℚ) ^ ((j + 1).choose 2)) =
        finiteQPochhammer (-1 / 2) (1 / 2) n := by
    rw [← hplus]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [choose_succ_two_toeplitz, pow_add]
    rw [show (-1 / 2 : ℚ) ^ j =
        (-1 : ℚ) ^ j * (1 / 2 : ℚ) ^ j by
          rw [show (-1 / 2 : ℚ) = (-1 : ℚ) * (1 / 2 : ℚ) by norm_num,
            mul_pow]]
    have hsign : (-1 : ℚ) ^ j * (-1 : ℚ) ^ j = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    calc
      halfQBinomial n j *
          ((1 / 2 : ℚ) ^ j.choose 2 * (1 / 2 : ℚ) ^ j) =
          ((-1 : ℚ) ^ j * (-1 : ℚ) ^ j) *
            (halfQBinomial n j *
              ((1 / 2 : ℚ) ^ j.choose 2 * (1 / 2 : ℚ) ^ j)) := by
            rw [hsign, one_mul]
      _ = _ := by ring
  have hl1 :
      (∑ j ∈ Finset.range (n + 1), |discreteLimitWeight n j|) =
        finiteQPochhammer (-1 / 2) (1 / 2) n /
          halfQPochhammer n := by
    calc
      (∑ j ∈ Finset.range (n + 1), |discreteLimitWeight n j|) =
          ∑ j ∈ Finset.range (n + 1),
            halfQBinomial n j * (1 / 2 : ℚ) ^ ((j + 1).choose 2) /
              halfQPochhammer n := by
        apply Finset.sum_congr rfl
        intro j hj
        exact abs_discreteLimitWeight
          (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
      _ = _ := by rw [← Finset.sum_div, hsum]
  rw [hl1]
  have hp := halfQPochhammer_pos n
  have hpquarter := one_fourth_le_halfQPochhammer n
  have hplus_div :
      finiteQPochhammer (-1 / 2) (1 / 2) n ≤
        1 / halfQPochhammer n := by
    rw [le_div_iff₀ hp]
    exact finiteQPochhammer_neg_half_mul_half_le_one n
  have hinv_le : 1 / halfQPochhammer n ≤ 4 := by
    rw [div_le_iff₀ hp]
    linarith
  calc
    finiteQPochhammer (-1 / 2) (1 / 2) n / halfQPochhammer n ≤
        (1 / halfQPochhammer n) / halfQPochhammer n :=
      div_le_div_of_nonneg_right hplus_div hp.le
    _ = (1 / halfQPochhammer n) ^ 2 := by field_simp
    _ ≤ (4 : ℚ) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by norm_num)).2 hinv_le
    _ = 16 := by norm_num

/-- A finite-row Toeplitz convergence lemma.  The row sums are one, their
total variations are uniformly bounded, and every sampled index in a row
eventually lies in any prescribed tail. -/
theorem tendsto_weighted_rows_of_tendsto
    {K : Type*} [RCLike K]
    (w : ℕ → ℕ → K) (index : ℕ → ℕ → ℕ) (C : ℝ)
    (hC : 0 ≤ C)
    (hrow : ∀ n, (∑ j ∈ Finset.range (n + 1), w n j) = 1)
    (hvariation : ∀ n,
      (∑ j ∈ Finset.range (n + 1), ‖w n j‖) ≤ C)
    (hindex : ∀ N, ∃ N₀, ∀ n ≥ N₀, ∀ j ∈ Finset.range (n + 1),
      N ≤ index n j)
    {H : ℕ → K} {L : K} (hH : Tendsto H atTop (𝓝 L)) :
    Tendsto
      (fun n => ∑ j ∈ Finset.range (n + 1),
        w n j * H (index n j))
      atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop] at hH ⊢
  intro ε hε
  have hCp : 0 < C + 1 := by linarith
  obtain ⟨N, hN⟩ := hH (ε / (C + 1)) (div_pos hε hCp)
  obtain ⟨N₀, hN₀⟩ := hindex N
  refine ⟨N₀, fun n hn => ?_⟩
  have hpoint (j : ℕ) (hj : j ∈ Finset.range (n + 1)) :
      ‖H (index n j) - L‖ < ε / (C + 1) := by
    have h := hN (index n j) (hN₀ n hn j hj)
    simpa only [dist_eq_norm] using h
  have hdiff :
      (∑ j ∈ Finset.range (n + 1), w n j * H (index n j)) - L =
        ∑ j ∈ Finset.range (n + 1),
          w n j * (H (index n j) - L) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hrow, one_mul]
  rw [dist_eq_norm, hdiff]
  calc
    ‖∑ j ∈ Finset.range (n + 1),
        w n j * (H (index n j) - L)‖ ≤
        ∑ j ∈ Finset.range (n + 1),
          ‖w n j * (H (index n j) - L)‖ :=
      norm_sum_le _ _
    _ = ∑ j ∈ Finset.range (n + 1),
          ‖w n j‖ * ‖H (index n j) - L‖ := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [norm_mul]
    _ ≤ ∑ j ∈ Finset.range (n + 1),
          ‖w n j‖ * (ε / (C + 1)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hpoint j hj).le (norm_nonneg _)
    _ = (∑ j ∈ Finset.range (n + 1), ‖w n j‖) *
          (ε / (C + 1)) := by rw [Finset.sum_mul]
    _ ≤ C * (ε / (C + 1)) :=
      mul_le_mul_of_nonneg_right (hvariation n) (div_nonneg hε.le hCp.le)
    _ = ε * (C / (C + 1)) := by field_simp
    _ < ε * 1 := by
      exact mul_lt_mul_of_pos_left ((div_lt_one hCp).2 (by linarith)) hε
    _ = ε := mul_one ε

/-- The rational Toeplitz weight cast into an `RCLike` field. -/
def discreteLimitWeightIn (K : Type*) [RCLike K] (n j : ℕ) : K :=
  (discreteLimitWeight n j : K)

theorem sum_range_discreteLimitWeightIn
    (K : Type*) [RCLike K] (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), discreteLimitWeightIn K n j) = 1 := by
  simp_rw [discreteLimitWeightIn]
  rw [← Rat.cast_sum,
    sum_range_discreteLimitWeight]
  norm_num

theorem sum_norm_discreteLimitWeightIn_le
    (K : Type*) [RCLike K] (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), ‖discreteLimitWeightIn K n j‖) ≤ 16 := by
  have hnorm (j : ℕ) :
      ‖discreteLimitWeightIn K n j‖ = |discreteLimitWeight n j| := by
    rw [discreteLimitWeightIn, ← RCLike.ofReal_ratCast,
      RCLike.norm_ofReal, Rat.cast_abs]
  simp_rw [hnorm]
  exact_mod_cast sum_abs_discreteLimitWeight_le n

/-- Every index `2n-j` occurring in row `n` is at least `n`. -/
theorem discreteLimit_index_ge {n j : ℕ} (hj : j ∈ Finset.range (n + 1)) :
    n ≤ 2 * n - j := by
  have hjle : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  omega

/-- Specialized Toeplitz convergence for the reindexing `p = 2n-j`. -/
theorem tendsto_discreteLimitWeightIn_sum
    {K : Type*} [RCLike K] {H : ℕ → K} {L : K}
    (hH : Tendsto H atTop (𝓝 L)) :
    Tendsto
      (fun n => ∑ j ∈ Finset.range (n + 1),
        discreteLimitWeightIn K n j * H (2 * n - j))
      atTop (𝓝 L) := by
  apply tendsto_weighted_rows_of_tendsto
    (w := discreteLimitWeightIn K) (index := fun n j => 2 * n - j)
    16 (by norm_num)
    (sum_range_discreteLimitWeightIn K)
    (sum_norm_discreteLimitWeightIn_le K)
    _ hH
  intro N
  exact ⟨N, fun n hn j hj => hn.trans (discreteLimit_index_ge hj)⟩

end

end Fabius
