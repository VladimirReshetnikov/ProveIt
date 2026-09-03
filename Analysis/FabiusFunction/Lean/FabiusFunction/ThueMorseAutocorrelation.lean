import FabiusFunction.ThueMorseBasicLemmas
import FabiusFunction.ThueMorseEnumerators
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Finite autocorrelation of the Thue–Morse signs

The autocorrelation sums `R_N(k) = ∑_{n<N} ε(n)ε(n+k)` (with the shifted
index *not* reduced modulo the window) satisfy an exact two-scale
recursion which, after normalization, characterizes the limiting
autocorrelation measure of the Thue–Morse dynamical system.  This module
proves the finite layer in exact integer arithmetic.

The recursion never uses that the window is a power of two — only that
it is *even*, so that `sum_range_two_mul` splits it into its even and odd
halves.  It is therefore proved here first for a general window `2K` and
then specialized to the dyadic sums `A_m(k) = R_{2^m}(k)`.

Window layer:

* `thueMorseWindowAutocorrelation` — `R_N(k) = ∑_{n<N} ε(n)ε(n+k)`.
* `thueMorseWindowAutocorrelation_zero` — `R_0(k) = 0`.
* `thueMorseWindowAutocorrelation_succ` — the one-step window recursion
  `R_{N+1}(k) = R_N(k) + ε(N)ε(N+k)`.
* `thueMorseWindowAutocorrelation_zero_shift` — `R_N(0) = N`.
* `thueMorseWindowAutocorrelation_two_mul_even` —
  `R_{2K}(2r) = 2·R_K(r)`.
* `thueMorseWindowAutocorrelation_two_mul_odd` —
  `R_{2K}(2r+1) = -(R_K(r) + R_K(r+1))`.
* `abs_thueMorseWindowAutocorrelation_le` — the trivial bound
  `|R_N(k)| ≤ N`.

Dyadic layer, `A_m(k) = R_{2^m}(k)`
(`thueMorseAutocorrelation_eq_window`):

* `thueMorseAutocorrelation_zero_shift` — `A_m(0) = 2^m`.
* `thueMorseAutocorrelation_succ_even` — `A_{m+1}(2r) = 2·A_m(r)`.
* `thueMorseAutocorrelation_succ_odd` —
  `A_{m+1}(2r+1) = -(A_m(r) + A_m(r+1))`.
* `abs_thueMorseAutocorrelation_le` — `|A_m(k)| ≤ 2^m`.
* `three_mul_thueMorseAutocorrelation_one` — the closed value at shift
  one: `3·A_m(1) = -2^m - 2·(-1)^m`; and its shift-two companion
  `three_mul_thueMorseAutocorrelation_two`,
  `3·A_{m+1}(2) = -2^{m+1} - 4·(-1)^m`.

Normalized limits, read off those closed forms:

* `tendsto_neg_half_pow` — the auxiliary limit `(-1/2)^m → 0`.
* `tendsto_thueMorseAutocorrelation_zero_shift` — `A_m(0)/2^m → 1`.
* `tendsto_thueMorseAutocorrelation_one` — `A_m(1)/2^m → -1/3`.
* `tendsto_thueMorseAutocorrelation_two` — `A_m(2)/2^m → -1/3`.

Everything below the limits is a finite sum manipulation through the
two-scale sign laws `ε(2j) = ε(j)`, `ε(2j+1) = -ε(j)`; no measure theory
enters, and the three limits are elementary consequences of the exact
closed forms.  The existence of the normalized limit
`η(k) = lim A_m(k)/2^m` at a *general* shift `k`, and its spectral
consequences, remain analytic frontiers.
-/

set_option autoImplicit false

open Finset Filter Topology

namespace Fabius

/-! ## The window autocorrelation -/

/-- The finite Thue–Morse autocorrelation over an arbitrary window,
`R_N(k) = ∑_{n<N} ε(n)·ε(n+k)`, unnormalized and unreduced. -/
def thueMorseWindowAutocorrelation (N k : ℕ) : ℤ :=
  ∑ n ∈ range N, thueMorseSign n * thueMorseSign (n + k)

/-- An empty window carries no correlation. -/
@[simp] theorem thueMorseWindowAutocorrelation_zero (k : ℕ) :
    thueMorseWindowAutocorrelation 0 k = 0 := by
  rw [thueMorseWindowAutocorrelation, Finset.range_zero, Finset.sum_empty]

/-- Growing the window by one appends a single sign product. -/
theorem thueMorseWindowAutocorrelation_succ (N k : ℕ) :
    thueMorseWindowAutocorrelation (N + 1) k =
      thueMorseWindowAutocorrelation N k +
        thueMorseSign N * thueMorseSign (N + k) := by
  rw [thueMorseWindowAutocorrelation, thueMorseWindowAutocorrelation,
    Finset.sum_range_succ]

/-- Zero shift over an arbitrary window: `R_N(0) = N`. -/
theorem thueMorseWindowAutocorrelation_zero_shift (N : ℕ) :
    thueMorseWindowAutocorrelation N 0 = (N : ℤ) := by
  rw [thueMorseWindowAutocorrelation]
  have hterm : ∀ n ∈ range N,
      thueMorseSign n * thueMorseSign (n + 0) = 1 := by
    intro n _
    rw [Nat.add_zero, thueMorseSign_mul_self]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range]
  ring

/-- **Even shifts halve the window.**  `R_{2K}(2r) = 2·R_K(r)`.  Only
evenness of the window enters, through `sum_range_two_mul`; the window
need not be a power of two. -/
theorem thueMorseWindowAutocorrelation_two_mul_even (K r : ℕ) :
    thueMorseWindowAutocorrelation (2 * K) (2 * r) =
      2 * thueMorseWindowAutocorrelation K r := by
  rw [thueMorseWindowAutocorrelation, thueMorseWindowAutocorrelation,
    sum_range_two_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show 2 * j + (2 * r) = 2 * (j + r) by ring, thueMorseSign_two_mul,
    thueMorseSign_two_mul,
    show 2 * j + 1 + 2 * r = 2 * (j + r) + 1 by ring,
    thueMorseSign_two_mul_add_one, thueMorseSign_two_mul_add_one]
  ring

/-- **Odd shifts mix the two neighbors.**
`R_{2K}(2r+1) = -(R_K(r) + R_K(r+1))`.  Again only evenness of the
window enters. -/
theorem thueMorseWindowAutocorrelation_two_mul_odd (K r : ℕ) :
    thueMorseWindowAutocorrelation (2 * K) (2 * r + 1) =
      -(thueMorseWindowAutocorrelation K r +
        thueMorseWindowAutocorrelation K (r + 1)) := by
  rw [thueMorseWindowAutocorrelation, thueMorseWindowAutocorrelation,
    thueMorseWindowAutocorrelation, sum_range_two_mul,
    ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show 2 * j + (2 * r + 1) = 2 * (j + r) + 1 by ring,
    thueMorseSign_two_mul, thueMorseSign_two_mul_add_one,
    show 2 * j + 1 + (2 * r + 1) = 2 * (j + (r + 1)) by ring,
    thueMorseSign_two_mul_add_one, thueMorseSign_two_mul]
  ring

/-- The trivial bound `|R_N(k)| ≤ N`: the window sum has `N` terms and
each of them is a sign.  Its one use below is the dyadic specialization
`abs_thueMorseAutocorrelation_le`, which places every normalized
autocorrelation in `[-1, 1]`; the three limits do not go through it, they
come from the exact closed forms. -/
theorem abs_thueMorseWindowAutocorrelation_le (N k : ℕ) :
    |thueMorseWindowAutocorrelation N k| ≤ (N : ℤ) := by
  have hterm : ∀ n ∈ range N,
      |thueMorseSign n * thueMorseSign (n + k)| = 1 := by
    intro n _
    rw [abs_mul, abs_thueMorseSign, abs_thueMorseSign,
      one_mul]
  calc |thueMorseWindowAutocorrelation N k|
      ≤ ∑ n ∈ range N, |thueMorseSign n * thueMorseSign (n + k)| := by
        rw [thueMorseWindowAutocorrelation]
        exact Finset.abs_sum_le_sum_abs _ _
    _ = (N : ℤ) := by
        rw [Finset.sum_congr rfl hterm, Finset.sum_const,
          Finset.card_range]
        ring

/-! ## The dyadic autocorrelation -/

/-- The finite Thue–Morse autocorrelation
`A_m(k) = ∑_{n<2^m} ε(n)·ε(n+k)`, unnormalized and unreduced. -/
def thueMorseAutocorrelation (m k : ℕ) : ℤ :=
  ∑ n ∈ range (2 ^ m), thueMorseSign n * thueMorseSign (n + k)

/-- The dyadic autocorrelation is the window autocorrelation taken at the
window length `2^m`. -/
theorem thueMorseAutocorrelation_eq_window (m k : ℕ) :
    thueMorseAutocorrelation m k =
      thueMorseWindowAutocorrelation (2 ^ m) k := rfl

/-- Zero shift: `A_m(0) = 2^m`. -/
theorem thueMorseAutocorrelation_zero_shift (m : ℕ) :
    thueMorseAutocorrelation m 0 = 2 ^ m := by
  rw [thueMorseAutocorrelation_eq_window,
    thueMorseWindowAutocorrelation_zero_shift]
  norm_cast

/-- Even shifts reduce scale: `A_{m+1}(2r) = 2·A_m(r)`. -/
theorem thueMorseAutocorrelation_succ_even (m r : ℕ) :
    thueMorseAutocorrelation (m + 1) (2 * r) =
      2 * thueMorseAutocorrelation m r := by
  rw [thueMorseAutocorrelation_eq_window,
    thueMorseAutocorrelation_eq_window,
    show (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m by rw [pow_succ]; ring,
    thueMorseWindowAutocorrelation_two_mul_even]

/-- Odd shifts mix the two neighbors:
`A_{m+1}(2r+1) = -(A_m(r) + A_m(r+1))`. -/
theorem thueMorseAutocorrelation_succ_odd (m r : ℕ) :
    thueMorseAutocorrelation (m + 1) (2 * r + 1) =
      -(thueMorseAutocorrelation m r + thueMorseAutocorrelation m (r + 1)) := by
  rw [thueMorseAutocorrelation_eq_window,
    thueMorseAutocorrelation_eq_window,
    thueMorseAutocorrelation_eq_window,
    show (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m by rw [pow_succ]; ring,
    thueMorseWindowAutocorrelation_two_mul_odd]

/-- The trivial dyadic bound `|A_m(k)| ≤ 2^m`, so that every normalized
autocorrelation `A_m(k)/2^m` lies in `[-1, 1]`. -/
theorem abs_thueMorseAutocorrelation_le (m k : ℕ) :
    |thueMorseAutocorrelation m k| ≤ 2 ^ m := by
  have h := abs_thueMorseWindowAutocorrelation_le (2 ^ m) k
  rw [← thueMorseAutocorrelation_eq_window] at h
  have hcast : ((2 ^ m : ℕ) : ℤ) = 2 ^ m := by norm_cast
  rwa [hcast] at h

/-! ## Closed values at the shifts one and two -/

/-- The closed value at shift one: `3·A_m(1) = -2^m - 2·(-1)^m`.  After
normalization, `A_m(1)/2^m → -1/3`, the first nontrivial value of the
limiting Thue–Morse autocorrelation. -/
theorem three_mul_thueMorseAutocorrelation_one (m : ℕ) :
    3 * thueMorseAutocorrelation m 1 = -(2 ^ m) - 2 * (-1) ^ m := by
  induction m with
  | zero =>
      norm_num [thueMorseAutocorrelation, thueMorseSign, binaryWeight]
  | succ m ih =>
      have h := thueMorseAutocorrelation_succ_odd m 0
      rw [Nat.mul_zero, Nat.zero_add] at h
      rw [h, thueMorseAutocorrelation_zero_shift]
      have hp : (2 : ℤ) ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
      have hn : ((-1 : ℤ)) ^ (m + 1) = -((-1) ^ m) := by rw [pow_succ]; ring
      linarith [ih]

/-- The closed value at shift two: `3·A_{m+1}(2) = -2^{m+1} - 4·(-1)^m`;
after normalization, `A_m(2)/2^m → -1/3` as well. -/
theorem three_mul_thueMorseAutocorrelation_two (m : ℕ) :
    3 * thueMorseAutocorrelation (m + 1) 2 =
      -(2 ^ (m + 1)) - 4 * (-1) ^ m := by
  have h := thueMorseAutocorrelation_succ_even m 1
  rw [Nat.mul_one] at h
  have h1 := three_mul_thueMorseAutocorrelation_one m
  have hp : (2 : ℤ) ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
  rw [h]
  linarith [h1]

/-! ## Normalized limits -/

/-- The alternating dyadic geometric sequence `(-1/2)^m` tends to zero:
its ratio has absolute value `1/2 < 1`. -/
theorem tendsto_neg_half_pow :
    Tendsto (fun m : ℕ => ((-1 : ℝ) / 2) ^ m) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_abs_lt_one
    (by rw [abs_div, abs_neg, abs_one, abs_two]; norm_num)

/-- The common limit shape of the two closed forms:
`-1/3 + (-2/3)·(-1/2)^m → -1/3`. -/
private theorem tendsto_neg_third_add :
    Tendsto (fun m : ℕ => -1 / 3 + (-2 / 3) * ((-1 : ℝ) / 2) ^ m) atTop
      (𝓝 (-1 / 3)) := by
  have hbase : Tendsto
      (fun m : ℕ => -1 / 3 + (-2 / 3) * ((-1 : ℝ) / 2) ^ m) atTop
      (𝓝 (-1 / 3 + (-2 / 3) * 0)) :=
    tendsto_const_nhds.add (tendsto_neg_half_pow.const_mul (-2 / 3))
  simpa using hbase

/-- The normalized autocorrelation at shift zero is constantly one, so
`A_m(0)/2^m → 1 = η(0)`. -/
theorem tendsto_thueMorseAutocorrelation_zero_shift :
    Tendsto (fun m : ℕ => (thueMorseAutocorrelation m 0 : ℝ) / 2 ^ m)
      atTop (𝓝 1) := by
  have hval : ∀ m : ℕ,
      (thueMorseAutocorrelation m 0 : ℝ) / 2 ^ m = 1 := by
    intro m
    rw [thueMorseAutocorrelation_zero_shift]
    push_cast
    exact div_self (by positivity)
  exact tendsto_const_nhds.congr fun m => (hval m).symm

/-- Normalizing a closed form `3·A = -2^p - c·s` by `2^p`:
`A/2^p = -1/3 + (-c/3)·(s/2^p)`.  Both limiting autocorrelations below
are this one computation. -/
private theorem div_two_pow_of_three_mul_eq {A : ℤ} {p : ℕ} {c s : ℝ}
    (h : 3 * (A : ℝ) = -(2 : ℝ) ^ p - c * s) :
    (A : ℝ) / 2 ^ p = -1 / 3 + (-c / 3) * (s / 2 ^ p) := by
  have hne : ((2 : ℝ) ^ p) ≠ 0 := by positivity
  have hcancel : s / 2 ^ p * 2 ^ p = s := div_mul_cancel₀ _ hne
  rw [div_eq_iff hne]
  linear_combination (1 / 3 : ℝ) * h + (c / 3) * hcancel

/-- **The limiting autocorrelation at shift one.**  Dividing the closed
form `3·A_m(1) = -2^m - 2·(-1)^m` by `3·2^m` gives
`A_m(1)/2^m = -1/3 + (-2/3)·(-1/2)^m`, whence `A_m(1)/2^m → -1/3`. -/
theorem tendsto_thueMorseAutocorrelation_one :
    Tendsto (fun m : ℕ => (thueMorseAutocorrelation m 1 : ℝ) / 2 ^ m)
      atTop (𝓝 (-1 / 3)) := by
  have hval : ∀ m : ℕ, (thueMorseAutocorrelation m 1 : ℝ) / 2 ^ m =
      -1 / 3 + (-2 / 3) * ((-1 : ℝ) / 2) ^ m := by
    intro m
    have hcast : (3 : ℝ) * (thueMorseAutocorrelation m 1 : ℝ) =
        -(2 : ℝ) ^ m - 2 * (-1 : ℝ) ^ m := by
      exact_mod_cast three_mul_thueMorseAutocorrelation_one m
    rw [div_two_pow_of_three_mul_eq hcast, div_pow]
  exact tendsto_neg_third_add.congr fun m => (hval m).symm

/-- **The limiting autocorrelation at shift two.**  Dividing the closed
form `3·A_{m+1}(2) = -2^{m+1} - 4·(-1)^m` by `3·2^{m+1}` gives
`A_{m+1}(2)/2^{m+1} = -1/3 + (-2/3)·(-1/2)^m`, whence
`A_m(2)/2^m → -1/3 = η(2)` — the same value as at shift one, as it must
be, since `η(2) = η(1)` by the even branch of the recursion. -/
theorem tendsto_thueMorseAutocorrelation_two :
    Tendsto (fun m : ℕ => (thueMorseAutocorrelation m 2 : ℝ) / 2 ^ m)
      atTop (𝓝 (-1 / 3)) := by
  have hval : ∀ m : ℕ,
      (thueMorseAutocorrelation (m + 1) 2 : ℝ) / 2 ^ (m + 1) =
        -1 / 3 + (-2 / 3) * ((-1 : ℝ) / 2) ^ m := by
    intro m
    have hcast : (3 : ℝ) * (thueMorseAutocorrelation (m + 1) 2 : ℝ) =
        -(2 : ℝ) ^ (m + 1) - 4 * (-1 : ℝ) ^ m := by
      exact_mod_cast three_mul_thueMorseAutocorrelation_two m
    rw [div_two_pow_of_three_mul_eq hcast, div_pow, pow_succ]
    ring
  have key : Tendsto
      (fun m : ℕ =>
        (thueMorseAutocorrelation (m + 1) 2 : ℝ) / 2 ^ (m + 1))
      atTop (𝓝 (-1 / 3)) :=
    tendsto_neg_third_add.congr fun m => (hval m).symm
  exact (Filter.tendsto_add_atTop_iff_nat 1).mp key

end Fabius
