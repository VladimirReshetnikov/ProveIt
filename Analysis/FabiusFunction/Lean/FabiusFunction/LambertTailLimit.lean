import FabiusFunction.PolynomialQDerivative
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.AbelLimit

/-!
# The limit of the Lambert tail as `q → 1⁻`

For `0 ≤ q ≤ 1` put

`a_r(q) = q^r / [r]_q`,   `[r]_q = 1 + q + ⋯ + q^{r-1}`,

the `r`-th term of the alternating Lambert-type series `∑_r (-1)^{r-1} q^r/[r]_q`
that appears in the deleted-singularity analysis of the central binomial sums.
Here `[r]_q` is the corpus `q`-integer `Fabius.qInt`, so that `a_r(1) = 1/r`
holds on the nose, with no case distinction.

This module proves the *limit of the Lambert tail*: for every starting index
`N ≥ 1`,

`lim_{q→1⁻} ∑_{s≥0} (-1)^s a_{s+N}(q) = ∑_{s≥0} (-1)^s/(s+N)`,

whenever the right-hand series converges (`tendsto_qLambertTail`), and then the
named consequence at `N = 2m+1`,

`lim_{q→1⁻} ∑_{r≥2m+1} (-1)^{r-1} q^r/[r]_q = log 2 - H̄_{2m}`,

with `H̄_n = ∑_{r=1}^{n} (-1)^{r-1}/r` the alternating harmonic number
(`tendsto_qLambertTail_log_two`, and `tendsto_qLambertTail_alternating` in the
sign convention `(-1)^{r-1}` of the source).

## The proof

The elementary estimates are those of the source, made division-free:
`0 ≤ a_r(q)`, `a_r(q) ≤ q^r`, `a_r(q) ≤ 1/r` (because each of the `r` summands
of `[r]_q` is at least `q^r` when `0 ≤ q ≤ 1`, so `[r]_q ≥ r q^r`), and
`a_{r+1}(q) ≤ a_r(q)` (the source's `a_{r+1}/a_r = q [r]_q/[r+1]_q < 1`, cleared
of denominators).  Antitonicity plus summability give the alternating-series
error bound `|T(q) - S_n(q)| ≤ a_{n+N}(q) ≤ 1/(n+N)` *uniformly in* `q`, and
each partial sum `S_n` is continuous at `q = 1`.  A `3ε` argument — pick `n`
with `1/(n+N) < ε/3` and `|S_n(1) - L| < ε/3`, then `δ` from continuity of `S_n`
— completes the interchange of the two limits.

The value `∑_{r≥1} (-1)^{r-1}/r = log 2` is *not* in Mathlib and is proved here
(`tendsto_alternatingHarmonic`) by the same Abel-limit route Mathlib uses for
Leibniz's series: the alternating series test produces some limit `l`, Abel's
theorem identifies `l` with `lim_{x→1⁻} ∑_n (-1)^n x^n/(n+1) = lim log(1+x)/x`,
and continuity of `x ↦ log(1+x)/x` at `1` evaluates that limit as `log 2`.

## Main declarations

* `qLambertTerm`, `qLambertTerm_one`: the term `a_r(q)` and its value at `q = 1`.
* `qLambertTerm_le_pow`, `qLambertTerm_le_inv`, `qLambertTerm_succ_le`: the
  elementary estimates.
* `antitone_qLambertTerm_add`, `summable_qLambertTerm_add`: the hypotheses of the
  alternating-series error bound for the shifted family.
* `continuousAt_qLambertTerm`, `continuousAt_qLambertPartialSum`: continuity at
  `q = 1`.
* `alternatingHarmonic`, `tendsto_alternatingHarmonic`: `H̄_n → log 2`.
* `sum_range_alternating_tail`, `tendsto_sum_range_alternating_tail`: the tail of
  the alternating harmonic series after `2m` terms.
* `tendsto_qLambertTail`: the interchange theorem, for an arbitrary start `N ≥ 1`.
* `tendsto_qLambertTail_log_two`, `tendsto_qLambertTail_alternating`: the named
  limit at `N = 2m+1`.

## Scope relative to the source statement

Everything in the source proposition is proved, over `ℝ`, with no `sorry`.  Three
deliberate differences:

* The interchange is stated for an **arbitrary** starting index `N ≥ 1`, not only
  `N = 2m+1`; the generality is free.
* No hypothesis `0 < q` is imposed: the conclusion is a limit along `𝓝[<] (1:ℝ)`
  and the proof works with `δ ≤ 1/2`, which forces `q ∈ (1/2, 1)` eventually.
* The remainder after `n` terms of the tail starting at `N` is bounded here by its
  own first omitted term, `a_{n+N}(q) ≤ 1/(n+N)`.  The source bounds it by
  `a_{n+1}(q) ≤ 1/(n+1)`, which is also correct — the terms decrease, so
  `a_{n+N} ≤ a_{n+1}` — merely weaker; either bound tends to `0`.

Not covered: the surrounding results that consume this limit, anything about
complex `q` (a one-sided real limit is stated; a complex version would need a
Stolz-cone hypothesis), and the divergent-at-`q = 1` pieces of the central
infinite component.
-/

set_option autoImplicit false

open Filter Finset Topology

open scoped BigOperators

namespace Fabius

noncomputable section

variable {q : ℝ} {r N : ℕ}

/-! ## The Lambert term `a_r(q) = q^r/[r]_q` -/

/-- The `r`-th Lambert term `a_r(q) = q^r/[r]_q`, with `[r]_q = 1 + q + ⋯ + q^{r-1}`
the `q`-integer `qInt`.  At `r = 0` the denominator vanishes and the value is `0`;
accordingly every estimate below carries a hypothesis `1 ≤ r`. -/
def qLambertTerm (q : ℝ) (r : ℕ) : ℝ := q ^ r / qInt q r

/-- Unfolding lemma for `qLambertTerm`. -/
theorem qLambertTerm_def (q : ℝ) (r : ℕ) : qLambertTerm q r = q ^ r / qInt q r := rfl

/-- At `q = 1` the Lambert term is the harmonic term: `a_r(1) = 1/r`. -/
theorem qLambertTerm_one (r : ℕ) : qLambertTerm (1 : ℝ) r = 1 / (r : ℝ) := by
  rw [qLambertTerm_def, one_pow, qInt_one_left]

/-- For `0 ≤ q` and `1 ≤ r` the `q`-integer `[r]_q` is at least `1`, because the
summand `q^0 = 1` occurs and all summands are nonnegative. -/
theorem one_le_qInt (hq : 0 ≤ q) (hr : 1 ≤ r) : (1 : ℝ) ≤ qInt q r := by
  have hmem : (0 : ℕ) ∈ range r := Finset.mem_range.mpr (by omega)
  have hs0 : q ^ (0 : ℕ) ≤ ∑ i ∈ range r, q ^ i :=
    Finset.single_le_sum (f := fun i : ℕ => q ^ i) (fun i _ => pow_nonneg hq i) hmem
  have hs : (1 : ℝ) ≤ ∑ i ∈ range r, q ^ i := by rwa [pow_zero] at hs0
  simpa only [qInt] using hs

/-- For `0 ≤ q` the `q`-integer `[n]_q` is nonnegative. -/
theorem qInt_nonneg (hq : 0 ≤ q) (n : ℕ) : (0 : ℝ) ≤ qInt q n := by
  simp only [qInt]
  exact Finset.sum_nonneg fun i _ => pow_nonneg hq i

/-- The Lambert terms are nonnegative for `0 ≤ q` (including at `r = 0`, where the
convention `x/0 = 0` makes the value `0`). -/
theorem qLambertTerm_nonneg (hq : 0 ≤ q) (n : ℕ) : 0 ≤ qLambertTerm q n := by
  rw [qLambertTerm_def]
  exact div_nonneg (pow_nonneg hq n) (qInt_nonneg hq n)

/-- `a_r(q) ≤ q^r`, since `[r]_q ≥ 1`. -/
theorem qLambertTerm_le_pow (hq : 0 ≤ q) (hr : 1 ≤ r) : qLambertTerm q r ≤ q ^ r := by
  have h1 : (1 : ℝ) ≤ qInt q r := one_le_qInt hq hr
  have h0 : (0 : ℝ) < qInt q r := lt_of_lt_of_le zero_lt_one h1
  have hprod : 0 ≤ q ^ r * (qInt q r - 1) := mul_nonneg (pow_nonneg hq r) (by linarith)
  rw [qLambertTerm_def, div_le_iff₀ h0]
  linarith

/-- `a_r(q) ≤ 1/r` for `0 ≤ q ≤ 1` and `1 ≤ r`: each of the `r` summands of
`[r]_q = ∑_{i<r} q^i` is at least `q^r`, hence `[r]_q ≥ r q^r`. -/
theorem qLambertTerm_le_inv (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hr : 1 ≤ r) :
    qLambertTerm q r ≤ 1 / (r : ℝ) := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have h1 : (1 : ℝ) ≤ qInt q r := one_le_qInt hq0 hr
  have h0 : (0 : ℝ) < qInt q r := lt_of_lt_of_le zero_lt_one h1
  have hle : ∑ _i ∈ range r, q ^ r ≤ ∑ i ∈ range r, q ^ i :=
    Finset.sum_le_sum fun i hi =>
      pow_le_pow_of_le_one hq0 hq1 (Finset.mem_range.mp hi).le
  have hconst : ∑ _i ∈ range r, q ^ r = (r : ℝ) * q ^ r := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have key : (r : ℝ) * q ^ r ≤ qInt q r := by
    rw [hconst] at hle
    simpa only [qInt] using hle
  rw [qLambertTerm_def, div_le_div_iff₀ h0 hrpos]
  calc q ^ r * (r : ℝ) = (r : ℝ) * q ^ r := by ring
    _ ≤ qInt q r := key
    _ = 1 * qInt q r := (one_mul _).symm

/-- The Lambert terms decrease: `a_{r+1}(q) ≤ a_r(q)` for `0 ≤ q` and `1 ≤ r`.
This is the source's `a_{r+1}(q)/a_r(q) = q [r]_q/[r+1]_q < 1`, cleared of
denominators using `[r+1]_q = 1 + q [r]_q`. -/
theorem qLambertTerm_succ_le (hq : 0 ≤ q) (hr : 1 ≤ r) :
    qLambertTerm q (r + 1) ≤ qLambertTerm q r := by
  have h1 : (1 : ℝ) ≤ qInt q r := one_le_qInt hq hr
  have h1' : (1 : ℝ) ≤ qInt q (r + 1) := one_le_qInt hq (show 1 ≤ r + 1 by omega)
  have h0 : (0 : ℝ) < qInt q r := lt_of_lt_of_le zero_lt_one h1
  have h0' : (0 : ℝ) < qInt q (r + 1) := lt_of_lt_of_le zero_lt_one h1'
  rw [qLambertTerm_def, qLambertTerm_def, div_le_div_iff₀ h0' h0, qInt_succ' q r, pow_succ]
  linarith [pow_nonneg hq r]

/-- The shifted family `s ↦ a_{s+N}(q)` is antitone, for `0 ≤ q` and `1 ≤ N`. -/
theorem antitone_qLambertTerm_add (hq : 0 ≤ q) (hN : 1 ≤ N) :
    Antitone fun s : ℕ => qLambertTerm q (s + N) := by
  refine antitone_nat_of_succ_le fun s => ?_
  show qLambertTerm q (s + 1 + N) ≤ qLambertTerm q (s + N)
  have hidx : s + 1 + N = s + N + 1 := by omega
  rw [hidx]
  exact qLambertTerm_succ_le hq (show 1 ≤ s + N by omega)

/-- For `0 ≤ q < 1` the shifted family is summable: it is dominated by the
geometric series `q^s`. -/
theorem summable_qLambertTerm_add (hq0 : 0 ≤ q) (hq1 : q < 1) (hN : 1 ≤ N) :
    Summable fun s : ℕ => qLambertTerm q (s + N) := by
  have hle : ∀ s : ℕ, qLambertTerm q (s + N) ≤ q ^ s := by
    intro s
    calc qLambertTerm q (s + N) ≤ q ^ (s + N) :=
          qLambertTerm_le_pow hq0 (show 1 ≤ s + N by omega)
      _ ≤ q ^ s := pow_le_pow_of_le_one hq0 hq1.le (Nat.le_add_right s N)
  exact Summable.of_nonneg_of_le (fun s => qLambertTerm_nonneg hq0 _) hle
    (summable_geometric_of_lt_one hq0 hq1)

/-- The `q`-integer `q ↦ [m]_q` is a polynomial in `q`, hence continuous. -/
theorem continuous_qIntReal (m : ℕ) : Continuous fun q : ℝ => qInt q m := by
  simp only [qInt]
  exact continuous_finsetSum (range m) fun i _ => continuous_pow i

/-- Each Lambert term is continuous at `q = 1`, the denominator `[r]_1 = r` being
nonzero for `1 ≤ r`. -/
theorem continuousAt_qLambertTerm (hr : 1 ≤ r) :
    ContinuousAt (fun q : ℝ => qLambertTerm q r) 1 := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hne : qInt (1 : ℝ) r ≠ 0 := by
    rw [qInt_one_left]
    exact ne_of_gt hrpos
  have hnum : Tendsto (fun q : ℝ => q ^ r) (𝓝 1) (𝓝 ((1 : ℝ) ^ r)) :=
    (continuous_pow r).tendsto (1 : ℝ)
  have hden : Tendsto (fun q : ℝ => qInt q r) (𝓝 1) (𝓝 (qInt (1 : ℝ) r)) :=
    (continuous_qIntReal r).tendsto (1 : ℝ)
  -- `Filter.Tendsto.div` is stated in point-free form `Tendsto (f / g) _ _`
  have hdiv : Tendsto ((fun q : ℝ => q ^ r) / (fun q : ℝ => qInt q r)) (𝓝 1)
      (𝓝 ((1 : ℝ) ^ r / qInt (1 : ℝ) r)) := Filter.Tendsto.div hnum hden hne
  have hfun : Tendsto (fun q : ℝ => q ^ r / qInt q r) (𝓝 1)
      (𝓝 ((1 : ℝ) ^ r / qInt (1 : ℝ) r)) := by
    refine Filter.Tendsto.congr ?_ hdiv
    intro y
    rfl
  exact hfun

/-- Every partial sum `∑_{s<n} (-1)^s a_{s+N}(q)` is continuous at `q = 1`. -/
theorem continuousAt_qLambertPartialSum (hN : 1 ≤ N) (n : ℕ) :
    ContinuousAt (fun q : ℝ => ∑ s ∈ range n, (-1 : ℝ) ^ s * qLambertTerm q (s + N)) 1 := by
  induction n with
  | zero =>
      have hzero : ContinuousAt (fun _ : ℝ => (0 : ℝ)) 1 := continuousAt_const
      simpa only [Finset.range_zero, Finset.sum_empty] using hzero
  | succ n ih =>
      have hterm : ContinuousAt (fun q : ℝ => (-1 : ℝ) ^ n * qLambertTerm q (n + N)) 1 :=
        Filter.Tendsto.mul tendsto_const_nhds
          (continuousAt_qLambertTerm (show 1 ≤ n + N by omega))
      have hstep : ContinuousAt (fun q : ℝ =>
          (∑ s ∈ range n, (-1 : ℝ) ^ s * qLambertTerm q (s + N))
            + (-1 : ℝ) ^ n * qLambertTerm q (n + N)) 1 := Filter.Tendsto.add ih hterm
      simpa only [Finset.sum_range_succ] using hstep

/-! ## The alternating harmonic series -/

/-- The alternating harmonic number `H̄_n = ∑_{r=1}^{n} (-1)^{r-1}/r`, reindexed by
`r ↦ r + 1` so that the summation range is `Finset.range n`. -/
def alternatingHarmonic (n : ℕ) : ℝ := ∑ r ∈ range n, (-1 : ℝ) ^ r / ((r : ℝ) + 1)

/-- **The alternating harmonic series.** `H̄_n → log 2` as `n → ∞`.

Mathlib does not contain this evaluation, so it is proved here by the Abel-limit
route used for Leibniz's series: the alternating series test gives convergence to
*some* `l`; Abel's theorem transports `l` to `lim_{x→1⁻} ∑_n (-1)^n x^n/(n+1)`,
which equals `lim_{x→1⁻} log(1+x)/x = log 2` by continuity. -/
theorem tendsto_alternatingHarmonic :
    Tendsto alternatingHarmonic atTop (𝓝 (Real.log 2)) := by
  -- the series converges to some `l` by the alternating series test
  obtain ⟨l, hl⟩ : ∃ l : ℝ,
      Tendsto (fun n : ℕ => ∑ i ∈ range n, (-1 : ℝ) ^ i * (1 / ((i : ℝ) + 1)))
        atTop (𝓝 l) := by
    refine Antitone.tendsto_alternating_series_of_tendsto_zero
      (f := fun i : ℕ => 1 / ((i : ℝ) + 1)) ?_ ?_
    · intro a b hab
      have hpos : (0 : ℝ) < (a : ℝ) + 1 := by positivity
      have hmono : ((a : ℝ) + 1) ≤ (b : ℝ) + 1 := by
        have hcast : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
        linarith
      exact one_div_le_one_div_of_le hpos hmono
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
  -- Abel's limit theorem
  have habel := Real.tendsto_tsum_powerSeries_nhdsWithin_lt hl
  -- on `(0,1)` the power series is `log(1+x)/x`
  have hEq : (fun x : ℝ => ∑' n : ℕ, ((-1 : ℝ) ^ n * (1 / ((n : ℝ) + 1))) * x ^ n)
      =ᶠ[𝓝[<] (1 : ℝ)] fun x : ℝ => Real.log (1 + x) / x := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with x hx
    have hxpos : (0 : ℝ) < x := hx.1
    have hxne : x ≠ 0 := ne_of_gt hxpos
    have habs : |(-x)| < 1 := by
      rw [abs_neg, abs_of_pos hxpos]
      exact hx.2
    have key : ∀ n : ℕ, -x⁻¹ * ((-x) ^ (n + 1) / ((n : ℝ) + 1))
        = ((-1 : ℝ) ^ n * (1 / ((n : ℝ) + 1))) * x ^ n := by
      intro n
      have h1 : (-x) ^ (n + 1) = -((-1 : ℝ) ^ n * (x ^ n * x)) := by
        rw [neg_pow, pow_succ ((-1 : ℝ)) n, pow_succ x n]
        ring
      have h2 : -x⁻¹ * (-((-1 : ℝ) ^ n * (x ^ n * x)) / ((n : ℝ) + 1))
          = ((-1 : ℝ) ^ n * (1 / ((n : ℝ) + 1)) * x ^ n) * (x⁻¹ * x) := by
        ring
      rw [h1, h2, inv_mul_cancel₀ hxne, mul_one]
    have hfun : (fun n : ℕ => -x⁻¹ * ((-x) ^ (n + 1) / ((n : ℝ) + 1)))
        = fun n : ℕ => ((-1 : ℝ) ^ n * (1 / ((n : ℝ) + 1))) * x ^ n := funext key
    have hval : -x⁻¹ * -Real.log (1 - -x) = Real.log (1 + x) / x := by
      rw [sub_neg_eq_add]
      ring
    have hbase : HasSum (fun n : ℕ => -x⁻¹ * ((-x) ^ (n + 1) / ((n : ℝ) + 1)))
        (-x⁻¹ * -Real.log (1 - -x)) :=
      (Real.hasSum_pow_div_log_of_abs_lt_one habs).mul_left (-x⁻¹)
    rw [hfun, hval] at hbase
    exact hbase.tsum_eq
  have habel2 : Tendsto (fun x : ℝ => Real.log (1 + x) / x) (𝓝[<] (1 : ℝ)) (𝓝 l) :=
    Filter.Tendsto.congr' hEq habel
  -- `x ↦ log(1+x)/x` is continuous at `1`, with value `log 2`
  have hcont : Tendsto (fun x : ℝ => Real.log (1 + x) / x) (𝓝[<] (1 : ℝ))
      (𝓝 (Real.log 2)) := by
    have hin : ContinuousAt (fun x : ℝ => (1 : ℝ) + x) 1 :=
      Filter.Tendsto.add tendsto_const_nhds tendsto_id
    have hlogAt : ContinuousAt (fun x : ℝ => Real.log (1 + x)) 1 := hin.log (by norm_num)
    have hlog : Tendsto (fun x : ℝ => Real.log (1 + x)) (𝓝 (1 : ℝ))
        (𝓝 (Real.log (1 + (1 : ℝ)))) := hlogAt
    have hval2 : Real.log (1 + (1 : ℝ)) = Real.log 2 := by norm_num
    rw [hval2] at hlog
    have hid : Tendsto (fun x : ℝ => x) (𝓝 (1 : ℝ)) (𝓝 (1 : ℝ)) := tendsto_id
    have hdiv : Tendsto ((fun x : ℝ => Real.log (1 + x)) / (fun x : ℝ => x)) (𝓝 (1 : ℝ))
        (𝓝 (Real.log 2 / (1 : ℝ))) := Filter.Tendsto.div hlog hid one_ne_zero
    have hdiv' : Tendsto (fun x : ℝ => Real.log (1 + x) / x) (𝓝 (1 : ℝ))
        (𝓝 (Real.log 2 / (1 : ℝ))) := by
      refine Filter.Tendsto.congr ?_ hdiv
      intro y
      rfl
    rw [div_one] at hdiv'
    exact hdiv'.mono_left nhdsWithin_le_nhds
  have hl2 : l = Real.log 2 := tendsto_nhds_unique habel2 hcont
  rw [hl2] at hl
  have hshape : ∀ n : ℕ, alternatingHarmonic n
      = ∑ i ∈ range n, (-1 : ℝ) ^ i * (1 / ((i : ℝ) + 1)) := by
    intro n
    simp only [alternatingHarmonic, mul_one_div]
  exact Filter.Tendsto.congr (fun n => (hshape n).symm) hl

/-- The finite tail identity `∑_{s<n} (-1)^s/(s + 2m + 1) = H̄_{2m+n} - H̄_{2m}`. -/
theorem sum_range_alternating_tail (m n : ℕ) :
    ∑ s ∈ range n, (-1 : ℝ) ^ s / ((s + (2 * m + 1) : ℕ) : ℝ)
      = alternatingHarmonic (2 * m + n) - alternatingHarmonic (2 * m) := by
  have hsplit : alternatingHarmonic (2 * m + n)
      = alternatingHarmonic (2 * m)
        + ∑ s ∈ range n, (-1 : ℝ) ^ (2 * m + s) / (((2 * m + s : ℕ) : ℝ) + 1) := by
    simp only [alternatingHarmonic]
    exact Finset.sum_range_add (fun r : ℕ => (-1 : ℝ) ^ r / ((r : ℝ) + 1)) (2 * m) n
  have hterm : ∀ s : ℕ, (-1 : ℝ) ^ (2 * m + s) / (((2 * m + s : ℕ) : ℝ) + 1)
      = (-1 : ℝ) ^ s / ((s + (2 * m + 1) : ℕ) : ℝ) := by
    intro s
    have hsign : (-1 : ℝ) ^ (2 * m + s) = (-1 : ℝ) ^ s := by
      rw [pow_add, pow_mul]
      norm_num
    have hden : (((2 * m + s : ℕ) : ℝ) + 1) = ((s + (2 * m + 1) : ℕ) : ℝ) := by
      push_cast
      ring
    rw [hsign, hden]
  rw [hsplit]
  simp only [hterm]
  ring

/-- The tail of the alternating harmonic series after `2m` terms converges to
`log 2 - H̄_{2m}`. -/
theorem tendsto_sum_range_alternating_tail (m : ℕ) :
    Tendsto (fun n : ℕ => ∑ s ∈ range n, (-1 : ℝ) ^ s / ((s + (2 * m + 1) : ℕ) : ℝ))
      atTop (𝓝 (Real.log 2 - alternatingHarmonic (2 * m))) := by
  have hadd : Tendsto (fun n : ℕ => n + 2 * m) atTop atTop :=
    Filter.tendsto_add_atTop_nat (2 * m)
  have hcomp : Tendsto (fun n : ℕ => alternatingHarmonic (n + 2 * m)) atTop
      (𝓝 (Real.log 2)) := tendsto_alternatingHarmonic.comp hadd
  have hshift : Tendsto (fun n : ℕ => alternatingHarmonic (2 * m + n)) atTop
      (𝓝 (Real.log 2)) := by
    refine Filter.Tendsto.congr (fun n => ?_) hcomp
    show alternatingHarmonic (n + 2 * m) = alternatingHarmonic (2 * m + n)
    rw [Nat.add_comm n (2 * m)]
  have hsub : Tendsto (fun n : ℕ => alternatingHarmonic (2 * m + n) - alternatingHarmonic (2 * m))
      atTop (𝓝 (Real.log 2 - alternatingHarmonic (2 * m))) := hshift.sub tendsto_const_nhds
  exact Filter.Tendsto.congr (fun n => (sum_range_alternating_tail m n).symm) hsub

/-! ## The interchange of limits -/

/-- **The Lambert tail limit, for an arbitrary starting index.**

If the alternating series `∑_{s≥0} (-1)^s/(s+N)` has partial sums converging to
`L`, then the `q`-deformed tails converge to the same `L` as `q → 1⁻`:

`lim_{q→1⁻} ∑_{s≥0} (-1)^s a_{s+N}(q) = L`.

The proof is the `3ε` argument: the alternating-series remainder after `n` terms
is at most `a_{n+N}(q) ≤ 1/(n+N)` *uniformly in* `q ∈ [0,1)`, the `n`-th partial
sum is continuous at `q = 1`, and its value there is the `n`-th partial sum of
the limit series. -/
theorem tendsto_qLambertTail (hN : 1 ≤ N) {L : ℝ}
    (hL : Tendsto (fun n : ℕ => ∑ s ∈ range n, (-1 : ℝ) ^ s / ((s + N : ℕ) : ℝ))
      atTop (𝓝 L)) :
    Tendsto (fun q : ℝ => ∑' s : ℕ, (-1 : ℝ) ^ s * qLambertTerm q (s + N))
      (𝓝[<] (1 : ℝ)) (𝓝 L) := by
  -- the partial sums at `q = 1` are the partial sums of the limit series
  have hone : ∀ k : ℕ, ∑ s ∈ range k, (-1 : ℝ) ^ s * qLambertTerm 1 (s + N)
      = ∑ s ∈ range k, (-1 : ℝ) ^ s / ((s + N : ℕ) : ℝ) := by
    intro k
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [qLambertTerm_one, mul_one_div]
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  rw [Metric.tendsto_atTop] at hL
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hε3 : (0 : ℝ) < ε / 3 := by linarith
  obtain ⟨n₀, hn₀⟩ := hL (ε / 3) hε3
  obtain ⟨n₁, hn₁⟩ := exists_nat_gt (3 / ε)
  obtain ⟨n, hnn₀, hnn₁⟩ : ∃ n : ℕ, n₀ ≤ n ∧ n₁ ≤ n :=
    ⟨max n₀ n₁, le_max_left _ _, le_max_right _ _⟩
  -- (A) the limit series is already within `ε/3` of `L` after `n` terms
  have hA : |(∑ s ∈ range n, (-1 : ℝ) ^ s / ((s + N : ℕ) : ℝ)) - L| < ε / 3 :=
    hn₀ n hnn₀
  -- (B) the uniform remainder bound `1/(n+N)` is below `ε/3`
  have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn₁' : (3 : ℝ) / ε < (n : ℝ) := lt_of_lt_of_le hn₁ (by exact_mod_cast hnn₁)
  have hnN : (0 : ℝ) < (n : ℝ) + (N : ℝ) := by linarith
  have hkey : (3 : ℝ) < ε * ((n : ℝ) + (N : ℝ)) := by
    have h4 : (3 : ℝ) < (n : ℝ) * ε := (div_lt_iff₀ hε).mp hn₁'
    have h5 : (0 : ℝ) ≤ ε * (N : ℝ) := mul_nonneg hε.le (Nat.cast_nonneg N)
    linarith
  have hB : 1 / ((n + N : ℕ) : ℝ) < ε / 3 := by
    rw [Nat.cast_add, div_lt_div_iff₀ hnN (by norm_num : (0 : ℝ) < 3)]
    linarith
  -- continuity of the `n`-th partial sum at `q = 1`
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ :=
    Metric.continuousAt_iff.mp (continuousAt_qLambertPartialSum hN n) (ε / 3) hε3
  refine ⟨min δ₀ (1 / 2), lt_min hδ₀pos (by norm_num), ?_⟩
  intro x hx hdist
  have hx1 : x < 1 := hx
  have hxd : |x - 1| < 1 / 2 := lt_of_lt_of_le hdist (min_le_right _ _)
  have hx0 : (0 : ℝ) ≤ x := by
    have h := (abs_lt.mp hxd).1
    linarith
  -- (i) the alternating-series remainder
  have hbnd : qLambertTerm x (n + N) ≤ 1 / ((n + N : ℕ) : ℝ) :=
    qLambertTerm_le_inv hx0 hx1.le (show 1 ≤ n + N by omega)
  have herr : |(∑' s : ℕ, (-1 : ℝ) ^ s * qLambertTerm x (s + N))
      - (∑ s ∈ range n, (-1 : ℝ) ^ s * qLambertTerm x (s + N))| ≤ qLambertTerm x (n + N) :=
    alternating_series_error_bound (fun s : ℕ => qLambertTerm x (s + N))
      (antitone_qLambertTerm_add hx0 hN) (summable_qLambertTerm_add hx0 hx1 hN) n
  -- (ii) continuity of the partial sum
  have hii : |(∑ s ∈ range n, (-1 : ℝ) ^ s * qLambertTerm x (s + N))
      - (∑ s ∈ range n, (-1 : ℝ) ^ s * qLambertTerm 1 (s + N))| < ε / 3 :=
    hδ₀ (lt_of_lt_of_le hdist (min_le_left _ _))
  -- (iii) the value of the partial sum at `q = 1`
  have hiii : |(∑ s ∈ range n, (-1 : ℝ) ^ s * qLambertTerm 1 (s + N)) - L| < ε / 3 := by
    rw [hone n]
    exact hA
  show |(∑' s : ℕ, (-1 : ℝ) ^ s * qLambertTerm x (s + N)) - L| < ε
  have hsplit1 := abs_sub_le (∑' s : ℕ, (-1 : ℝ) ^ s * qLambertTerm x (s + N))
    (∑ s ∈ range n, (-1 : ℝ) ^ s * qLambertTerm x (s + N)) L
  have hsplit2 := abs_sub_le (∑ s ∈ range n, (-1 : ℝ) ^ s * qLambertTerm x (s + N))
    (∑ s ∈ range n, (-1 : ℝ) ^ s * qLambertTerm 1 (s + N)) L
  linarith

/-! ## The named limit -/

/-- **Limit of the Lambert tail.**  For every `m ≥ 0`,

`lim_{q→1⁻} ∑_{s≥0} (-1)^s q^{s+2m+1}/[s+2m+1]_q = log 2 - H̄_{2m}`,

which is the source's `∑_{r≥2m+1} (-1)^{r-1} q^r/[r]_q → log 2 - H̄_{2m}` after
the reindexing `r = s + 2m + 1`. -/
theorem tendsto_qLambertTail_log_two (m : ℕ) :
    Tendsto (fun q : ℝ => ∑' s : ℕ, (-1 : ℝ) ^ s * qLambertTerm q (s + (2 * m + 1)))
      (𝓝[<] (1 : ℝ)) (𝓝 (Real.log 2 - alternatingHarmonic (2 * m))) :=
  tendsto_qLambertTail (N := 2 * m + 1) (by omega) (tendsto_sum_range_alternating_tail m)

/-- The same limit written with the source's own sign `(-1)^{r-1}` at
`r = s + 2m + 1`, i.e. with the sign `(-1)^{s+2m}`. -/
theorem tendsto_qLambertTail_alternating (m : ℕ) :
    Tendsto
      (fun q : ℝ => ∑' s : ℕ, (-1 : ℝ) ^ (s + 2 * m) * qLambertTerm q (s + (2 * m + 1)))
      (𝓝[<] (1 : ℝ)) (𝓝 (Real.log 2 - alternatingHarmonic (2 * m))) := by
  have hsign : ∀ s : ℕ, (-1 : ℝ) ^ (s + 2 * m) = (-1 : ℝ) ^ s := by
    intro s
    rw [pow_add, pow_mul]
    norm_num
  simpa only [hsign] using tendsto_qLambertTail_log_two m

end

end Fabius
