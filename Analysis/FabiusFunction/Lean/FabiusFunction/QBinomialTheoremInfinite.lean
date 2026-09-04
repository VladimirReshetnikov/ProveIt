import FabiusFunction.QPochhammerInfinite
import FabiusFunction.QBinomialCauchy
import FabiusFunction.GaussianBinomialAtOne
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Euler's identities and the infinite q-binomial theorem

The classical `q`-series identities of Euler and Cauchy are proved here as
**stable limits of finite polynomial identities**, over an arbitrary
complete normed field `𝕜` and for every nome with `‖q‖ < 1`.

* The **finite `q`-binomial theorem** `(z;q)_N = ∑_k (-1)^k q^{C(k,2)} [N,k]_q z^k`
  becomes, as `N → ∞`, **Euler's product expansion**

  `(z;q)_∞ = ∑_k (-1)^k q^{C(k,2)} z^k / (q;q)_k`, valid for every `z`.

* The **finite `q`-Cauchy identity**
  `(az;q)_N = ∑_k [N,k]_q (a;q)_k z^k (z;q)_{N-k}`, divided by `(z;q)_N`,
  becomes the **infinite `q`-binomial theorem**

  `∑_k (a;q)_k / (q;q)_k · z^k = (az;q)_∞ / (z;q)_∞`, valid for `‖z‖ < 1`,

  whose specialization `a = 0` is **Euler's reciprocal expansion**
  `1/(z;q)_∞ = ∑_k z^k / (q;q)_k`.

The passage to the limit is Tannery's theorem (dominated convergence for
series), packaged once as `hasSum_of_tendsto_of_dominated`.  The only
analytic input is the **fixed-column limit** `[N,k]_q → 1/(q;q)_k` together
with a bound on Gaussian coefficients that is uniform in *both* indices,
`‖[N,k]_q‖ ≤ (−‖q‖;‖q‖)_∞ / (‖q‖;‖q‖)_∞²`.  That majorant comes from the real
comparison products `(±‖a‖;‖q‖)_n`, which sandwich the norms of all finite
symbols.

## Main declarations

* `hasSum_of_tendsto_of_dominated`: Tannery's theorem in `HasSum` form.
* `norm_finiteQPochhammerIn_le`, `qPochhammerInfIn_norm_le_norm_finiteQPochhammerIn`:
  the real sandwich for the norms of finite symbols.
* `gaussianMajorant`, `norm_gaussianBinomial_le`: the uniform bound.
* `tendsto_gaussianBinomial_atTop`, `tendsto_gaussianBinomial_add_const_atTop`:
  the fixed-column limit, unchanged by any fixed upper-index shift.
* `isBigO_gaussianBinomial_sub_inv`, `isBigO_gaussianBinomial_add_sub_inv`:
  the corresponding geometric error estimates.
* `summable_pow_choose_two_mul_pow`: summability of `r^{C(k,2)} s^k`.
* `hasSum_euler_product`: Euler's product expansion.
* `hasSum_qBinomial_theorem`: the infinite `q`-binomial theorem.
* `hasSum_euler_reciprocal`: Euler's reciprocal expansion.
-/

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace Fabius

noncomputable section

/-! ## Tannery's theorem in `HasSum` form -/

/-- **Tannery's theorem, `HasSum` form.**  If the `n`-th row `f n` of a
double family is dominated by one summable bound, converges termwise to `g`,
and sums to `S n` with `S n → L`, then `g` sums to `L`. -/
theorem hasSum_of_tendsto_of_dominated {ι E : Type*} [NormedAddCommGroup E]
    [CompleteSpace E] {f : ℕ → ι → E} {g : ι → E} {bound : ι → ℝ} {S : ℕ → E} {L : E}
    (hbound : Summable bound)
    (hlim : ∀ k, Tendsto (fun n => f n k) atTop (𝓝 (g k)))
    (hfb : ∀ n k, ‖f n k‖ ≤ bound k)
    (hS : ∀ n, HasSum (f n) (S n)) (hL : Tendsto S atTop (𝓝 L)) :
    HasSum g L := by
  have hgb : ∀ k, ‖g k‖ ≤ bound k := fun k =>
    le_of_tendsto' (hlim k).norm fun n => hfb n k
  have hg : Summable g := hbound.of_norm_bounded hgb
  have hT : Tendsto (fun n => ∑' k, f n k) atTop (𝓝 (∑' k, g k)) :=
    tendsto_tsum_of_dominated_convergence hbound hlim (Eventually.of_forall hfb)
  have hS' : (fun n => ∑' k, f n k) = S := funext fun n => (hS n).tsum_eq
  rw [hS'] at hT
  rw [← tendsto_nhds_unique hT hL]
  exact hg.hasSum

/-! ## Real comparison products -/

section RealComparison

/-- `1 ≤ (−x;r)_∞` for `x ≥ 0` and `0 ≤ r < 1`: every factor is at least one. -/
theorem one_le_qPochhammerInfIn_neg {x r : ℝ} (hx : 0 ≤ x) (hr0 : 0 ≤ r) (hr : r < 1) :
    1 ≤ qPochhammerInfIn (-x) r := by
  have hr' : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg hr0]
  refine le_hasProd_of_le_prod (hasProd_qPochhammerInfIn (-x) hr') fun s => ?_
  refine Finset.one_le_prod fun j _ => ?_
  have : 0 ≤ x * r ^ j := mul_nonneg hx (pow_nonneg hr0 j)
  simp only [neg_mul, sub_neg_eq_add]
  linarith

/-- The partial products `(−x;r)_n` increase to `(−x;r)_∞`. -/
theorem finiteQPochhammerIn_neg_le_qPochhammerInfIn {x r : ℝ} (hx : 0 ≤ x) (hr0 : 0 ≤ r)
    (hr : r < 1) (n : ℕ) :
    finiteQPochhammerIn (-x) r n ≤ qPochhammerInfIn (-x) r := by
  have hr' : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg hr0]
  rw [qPochhammerInfIn_eq_finite_mul_shift (-x) hr' n]
  have h1 : 1 ≤ qPochhammerInfIn (-x * r ^ n) r := by
    rw [neg_mul]
    exact one_le_qPochhammerInfIn_neg (mul_nonneg hx (pow_nonneg hr0 n)) hr0 hr
  have h0 : 0 ≤ finiteQPochhammerIn (-x) r n := by
    unfold finiteQPochhammerIn
    refine Finset.prod_nonneg fun j _ => ?_
    have : 0 ≤ x * r ^ j := mul_nonneg hx (pow_nonneg hr0 j)
    simp only [neg_mul, sub_neg_eq_add]
    linarith

  exact le_mul_of_one_le_right h0 h1

/-- `0 ≤ (x;r)_∞` for `x ≤ 1` and `0 ≤ r < 1`. -/
theorem qPochhammerInfIn_nonneg {x r : ℝ} (hx1 : x ≤ 1) (hr0 : 0 ≤ r) (hr : r < 1) :
    0 ≤ qPochhammerInfIn x r := by
  have hr' : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg hr0]
  refine le_hasProd_of_le_prod (hasProd_qPochhammerInfIn x hr') fun s => ?_
  refine Finset.prod_nonneg fun j _ => ?_
  have : x * r ^ j ≤ 1 := mul_le_one₀ hx1 (pow_nonneg hr0 j) (pow_le_one₀ hr0 hr.le)
  linarith

/-- The partial products `(x;r)_n` decrease to `(x;r)_∞` when `0 ≤ x ≤ 1`. -/
theorem qPochhammerInfIn_le_finiteQPochhammerIn {x r : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hr0 : 0 ≤ r) (hr : r < 1) (n : ℕ) :
    qPochhammerInfIn x r ≤ finiteQPochhammerIn x r n := by
  have hr' : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg hr0]
  rw [qPochhammerInfIn_eq_finite_mul_shift x hr' n]
  have hle : qPochhammerInfIn (x * r ^ n) r ≤ 1 := by
    refine hasProd_le_of_prod_le (hasProd_qPochhammerInfIn (x * r ^ n) hr') fun s => ?_
    refine Finset.prod_le_one (fun j _ => ?_) fun j _ => ?_
    · have h1 : r ^ n * r ^ j ≤ 1 := by
        rw [← pow_add]
        exact pow_le_one₀ hr0 hr.le
      have : x * r ^ n * r ^ j ≤ 1 := by
        calc x * r ^ n * r ^ j = x * (r ^ n * r ^ j) := by ring
          _ ≤ 1 * 1 :=
            mul_le_mul hx1 h1 (mul_nonneg (pow_nonneg hr0 n) (pow_nonneg hr0 j)) zero_le_one
          _ = 1 := one_mul 1
      linarith
    · have : 0 ≤ x * r ^ n * r ^ j :=
        mul_nonneg (mul_nonneg hx0 (pow_nonneg hr0 n)) (pow_nonneg hr0 j)
      linarith
  have h0 : 0 ≤ finiteQPochhammerIn x r n := by
    unfold finiteQPochhammerIn
    refine Finset.prod_nonneg fun j _ => ?_
    have : x * r ^ j ≤ 1 := mul_le_one₀ hx1 (pow_nonneg hr0 j) (pow_le_one₀ hr0 hr.le)
    linarith
  exact mul_le_of_le_one_right h0 hle

/-- `0 < (x;r)_∞` for `0 ≤ x < 1` and `0 ≤ r < 1`. -/
theorem qPochhammerInfIn_pos_of_lt_one {x r : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (hr0 : 0 ≤ r)
    (hr : r < 1) :
    0 < qPochhammerInfIn x r := by
  have hr' : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg hr0]
  refine lt_of_le_of_ne (qPochhammerInfIn_nonneg hx1.le hr0 hr) (Ne.symm ?_)
  refine qPochhammerInfIn_ne_zero x hr' fun j h => ?_
  have : x * r ^ j ≤ x := mul_le_of_le_one_right hx0 (pow_le_one₀ hr0 hr.le)
  linarith

end RealComparison

/-! ## Norm bounds for finite symbols and Gaussian coefficients -/

section NormBounds

variable {𝕜 : Type*} [NormedField 𝕜]

/-- `(0;q)_∞ = 1`. -/
@[simp] theorem qPochhammerInfIn_zero_left {R : Type*} [CommRing R] [TopologicalSpace R]
    (q : R) :
    qPochhammerInfIn 0 q = 1 := by
  simp [qPochhammerInfIn]

/-- Upper comparison: `‖(a;q)_n‖ ≤ (−‖a‖;‖q‖)_n`. -/
theorem norm_finiteQPochhammerIn_le_neg_norm (a q : 𝕜) (n : ℕ) :
    ‖finiteQPochhammerIn a q n‖ ≤ finiteQPochhammerIn (-‖a‖) ‖q‖ n := by
  unfold finiteQPochhammerIn
  rw [norm_prod]
  refine Finset.prod_le_prod (fun j _ => norm_nonneg _) fun j _ => ?_
  calc ‖1 - a * q ^ j‖ ≤ ‖(1 : 𝕜)‖ + ‖a * q ^ j‖ := norm_sub_le _ _
    _ = 1 - -‖a‖ * ‖q‖ ^ j := by rw [norm_one, norm_mul, norm_pow]; ring

/-- Lower comparison: `(‖a‖;‖q‖)_n ≤ ‖(a;q)_n‖` when `‖a‖ ≤ 1` and `‖q‖ ≤ 1`. -/
theorem finiteQPochhammerIn_norm_le_norm (a q : 𝕜) (ha : ‖a‖ ≤ 1) (hq : ‖q‖ ≤ 1) (n : ℕ) :
    finiteQPochhammerIn ‖a‖ ‖q‖ n ≤ ‖finiteQPochhammerIn a q n‖ := by
  unfold finiteQPochhammerIn
  rw [norm_prod]
  refine Finset.prod_le_prod (fun j _ => ?_) fun j _ => ?_
  · have : ‖a‖ * ‖q‖ ^ j ≤ 1 :=
      mul_le_one₀ ha (pow_nonneg (norm_nonneg q) j) (pow_le_one₀ (norm_nonneg q) hq)
    linarith
  · calc 1 - ‖a‖ * ‖q‖ ^ j = ‖(1 : 𝕜)‖ - ‖a * q ^ j‖ := by rw [norm_one, norm_mul, norm_pow]
      _ ≤ ‖1 - a * q ^ j‖ := norm_sub_norm_le _ _

/-- **Uniform upper bound**: `‖(a;q)_n‖ ≤ (−‖a‖;‖q‖)_∞` for every `n`. -/
theorem norm_finiteQPochhammerIn_le (a : 𝕜) {q : 𝕜} (hq : ‖q‖ < 1) (n : ℕ) :
    ‖finiteQPochhammerIn a q n‖ ≤ qPochhammerInfIn (-‖a‖) ‖q‖ :=
  (norm_finiteQPochhammerIn_le_neg_norm a q n).trans
    (finiteQPochhammerIn_neg_le_qPochhammerInfIn (norm_nonneg a) (norm_nonneg q) hq n)

/-- **Uniform lower bound**: `(‖a‖;‖q‖)_∞ ≤ ‖(a;q)_n‖` for every `n`, when
`‖a‖ ≤ 1`. -/
theorem qPochhammerInfIn_norm_le_norm_finiteQPochhammerIn (a : 𝕜) (ha : ‖a‖ ≤ 1) {q : 𝕜}
    (hq : ‖q‖ < 1) (n : ℕ) :
    qPochhammerInfIn ‖a‖ ‖q‖ ≤ ‖finiteQPochhammerIn a q n‖ :=
  (qPochhammerInfIn_le_finiteQPochhammerIn (norm_nonneg a) ha (norm_nonneg q) hq n).trans
    (finiteQPochhammerIn_norm_le_norm a q ha hq.le n)

/-- No factor of `(z;q)_n` vanishes when `‖z‖ < 1` and `‖q‖ < 1`. -/
theorem finiteQPochhammerIn_ne_zero_of_norm_lt_one {q z : 𝕜} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1)
    (n : ℕ) :
    finiteQPochhammerIn z q n ≠ 0 := by
  unfold finiteQPochhammerIn
  refine Finset.prod_ne_zero_iff.mpr fun j _ => one_sub_ne_zero_of_norm_lt_one ?_
  calc ‖z * q ^ j‖ = ‖z‖ * ‖q‖ ^ j := by rw [norm_mul, norm_pow]
    _ ≤ ‖z‖ * 1 :=
      mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg q) hq.le) (norm_nonneg z)
    _ < 1 := by simpa using hz

/-- Gaussian coefficients as quotients of `q`-factorials, for `‖q‖ < 1`. -/
theorem gaussianBinomial_eq_div {q : 𝕜} (hq : ‖q‖ < 1) {n k : ℕ} (hk : k ≤ n) :
    gaussianBinomial q n k =
      finiteQPochhammerIn q q n /
        (finiteQPochhammerIn q q k * finiteQPochhammerIn q q (n - k)) := by
  rw [eq_div_iff (mul_ne_zero (finiteQPochhammerIn_self_ne_zero hq k)
    (finiteQPochhammerIn_self_ne_zero hq (n - k))),
    finiteQPochhammerIn_self_eq_mul_mul_gaussianBinomial q hk]
  ring

/-- The **uniform majorant** `(−‖q‖;‖q‖)_∞ / (‖q‖;‖q‖)_∞²` of all Gaussian
coefficients with base `q`, in both indices. -/
def gaussianMajorant (q : 𝕜) : ℝ :=
  qPochhammerInfIn (-‖q‖) ‖q‖ / (qPochhammerInfIn ‖q‖ ‖q‖ * qPochhammerInfIn ‖q‖ ‖q‖)

/-- The Gaussian majorant is nonnegative. -/
theorem gaussianMajorant_nonneg {q : 𝕜} (hq : ‖q‖ < 1) : 0 ≤ gaussianMajorant q := by
  have hμ : 0 < qPochhammerInfIn ‖q‖ ‖q‖ :=
    qPochhammerInfIn_pos_of_lt_one (norm_nonneg q) hq (norm_nonneg q) hq
  have hM : 0 ≤ qPochhammerInfIn (-‖q‖) ‖q‖ :=
    zero_le_one.trans (one_le_qPochhammerInfIn_neg (norm_nonneg q) (norm_nonneg q) hq)
  exact div_nonneg hM (mul_pos hμ hμ).le

/-- **Gaussian coefficients are uniformly bounded** in both indices:
`‖[n,k]_q‖ ≤ (−‖q‖;‖q‖)_∞ / (‖q‖;‖q‖)_∞²`.  This uniformity is what licenses
dominated convergence in the finite-to-infinite limits below. -/
theorem norm_gaussianBinomial_le {q : 𝕜} (hq : ‖q‖ < 1) (n k : ℕ) :
    ‖gaussianBinomial q n k‖ ≤ gaussianMajorant q := by
  have hμ : 0 < qPochhammerInfIn ‖q‖ ‖q‖ :=
    qPochhammerInfIn_pos_of_lt_one (norm_nonneg q) hq (norm_nonneg q) hq
  have hM : 0 ≤ qPochhammerInfIn (-‖q‖) ‖q‖ :=
    zero_le_one.trans (one_le_qPochhammerInfIn_neg (norm_nonneg q) (norm_nonneg q) hq)
  unfold gaussianMajorant
  rcases le_or_gt k n with hk | hk
  · rw [gaussianBinomial_eq_div hq hk, norm_div, norm_mul]
    refine div_le_div₀ hM (norm_finiteQPochhammerIn_le q hq n) (mul_pos hμ hμ) ?_
    exact mul_le_mul (qPochhammerInfIn_norm_le_norm_finiteQPochhammerIn q hq.le hq k)
      (qPochhammerInfIn_norm_le_norm_finiteQPochhammerIn q hq.le hq (n - k))
      hμ.le (norm_nonneg _)
  · rw [gaussianBinomial_eq_zero_of_lt q hk, norm_zero]
    exact div_nonneg hM (mul_pos hμ hμ).le

/-- Shifted finite symbols `(q^m;q)_k` tend to `1` as `m → ∞`. -/
theorem tendsto_finiteQPochhammerIn_pow_atTop {q : 𝕜} (hq : ‖q‖ < 1) (k : ℕ) :
    Tendsto (fun m : ℕ => finiteQPochhammerIn (q ^ m) q k) atTop (𝓝 1) := by
  have h0 : Tendsto (fun m : ℕ => q ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq
  have h : Tendsto (fun m : ℕ => ∏ j ∈ Finset.range k, (1 - q ^ m * q ^ j)) atTop
      (𝓝 (∏ j ∈ Finset.range k, (1 - (0 : 𝕜) * q ^ j))) :=
    tendsto_finsetProd _ fun j _ => tendsto_const_nhds.sub (h0.mul_const _)
  simpa [finiteQPochhammerIn] using h

/-- **Effective finite-product convergence.**  When `‖q‖ ≤ 1`, the deviation
of `(q^m;q)_k` from one has the explicit bound

`‖(q^m;q)_k - 1‖ ≤ exp (k ‖q‖^m) - 1`.

This is the product estimate `‖∏(1+x_j)-1‖ ≤ exp(∑ ‖x_j‖)-1`, together with
`∑_{j<k} ‖q^(m+j)‖ ≤ k ‖q‖^m`. -/
theorem norm_finiteQPochhammerIn_pow_sub_one_le_exp_of_norm_le_one {q : 𝕜}
    (hq : ‖q‖ ≤ 1) (m k : ℕ) :
    ‖finiteQPochhammerIn (q ^ m) q k - 1‖ ≤
      Real.exp ((k : ℝ) * ‖q‖ ^ m) - 1 := by
  calc
    ‖finiteQPochhammerIn (q ^ m) q k - 1‖ ≤
        Real.exp (∑ j ∈ Finset.range k, ‖-(q ^ m * q ^ j)‖) - 1 := by
      simpa only [finiteQPochhammerIn, sub_eq_add_neg] using
        Finset.norm_prod_one_add_sub_one_le (Finset.range k)
          (fun j : ℕ => -(q ^ m * q ^ j))
    _ ≤ Real.exp ((k : ℝ) * ‖q‖ ^ m) - 1 := by
      gcongr
      calc
        (∑ j ∈ Finset.range k, ‖-(q ^ m * q ^ j)‖) ≤
            ∑ j ∈ Finset.range k, ‖q‖ ^ m := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_neg, norm_mul, norm_pow, norm_pow]
          exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg q) m)
            (pow_le_one₀ (norm_nonneg q) hq)
        _ = (k : ℝ) * ‖q‖ ^ m := by simp

/-- For a contracting nome, the effective finite-product error is
`O(q^m)` for every fixed column length `k`. -/
theorem isBigO_finiteQPochhammerIn_pow_sub_one {q : 𝕜}
    (hq : ‖q‖ < 1) (k : ℕ) :
    (fun m : ℕ => finiteQPochhammerIn (q ^ m) q k - 1) =O[atTop]
      (fun m : ℕ => q ^ m) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨2 * k, ?_⟩
  have hlim : Tendsto (fun m : ℕ => (k : ℝ) * ‖q‖ ^ m) atTop (𝓝 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq).const_mul (k : ℝ)
  filter_upwards [hlim.eventually_lt_const zero_lt_one] with m hm
  have hx0 : 0 ≤ (k : ℝ) * ‖q‖ ^ m :=
    mul_nonneg (Nat.cast_nonneg k) (pow_nonneg (norm_nonneg q) m)
  have hexp := Real.abs_exp_sub_one_le (show |(k : ℝ) * ‖q‖ ^ m| ≤ 1 by
    rw [abs_of_nonneg hx0]
    exact hm.le)
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp hx0)), abs_of_nonneg hx0] at hexp
  calc
    ‖finiteQPochhammerIn (q ^ m) q k - 1‖ ≤
        Real.exp ((k : ℝ) * ‖q‖ ^ m) - 1 :=
      norm_finiteQPochhammerIn_pow_sub_one_le_exp_of_norm_le_one hq.le m k
    _ ≤ 2 * ((k : ℝ) * ‖q‖ ^ m) := hexp
    _ = (2 * k) * ‖q ^ m‖ := by rw [norm_pow]; ring

/-- **The fixed-column limit** `[n,k]_q → 1/(q;q)_k` as `n → ∞`, because
`(q;q)_k [n,k]_q = (q^{n-k+1};q)_k → 1`. -/
theorem tendsto_gaussianBinomial_atTop {q : 𝕜} (hq : ‖q‖ < 1) (k : ℕ) :
    Tendsto (fun n : ℕ => gaussianBinomial q n k) atTop
      (𝓝 (finiteQPochhammerIn q q k)⁻¹) := by
  have hk0 : finiteQPochhammerIn q q k ≠ 0 := finiteQPochhammerIn_self_ne_zero hq k
  have hshift : Tendsto (fun n : ℕ => n - k + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp (tendsto_sub_atTop_nat k)
  have h1 : Tendsto
      (fun n : ℕ => finiteQPochhammerIn (q ^ (n - k + 1)) q k / finiteQPochhammerIn q q k)
      atTop (𝓝 (1 / finiteQPochhammerIn q q k)) :=
    ((tendsto_finiteQPochhammerIn_pow_atTop hq k).comp hshift).div_const _
  rw [one_div] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop k] with n hn
  rw [div_eq_iff hk0, ← finiteQPochhammerIn_self_mul_gaussianBinomial q hn, mul_comm]

/-- A fixed additive shift of the upper index does not change the
fixed-column limit.  In particular, taking `r = k` gives
`[n+k,k]_q → 1/(q;q)_k`. -/
theorem tendsto_gaussianBinomial_add_const_atTop {q : 𝕜}
    (hq : ‖q‖ < 1) (k r : ℕ) :
    Tendsto (fun n : ℕ => gaussianBinomial q (n + r) k) atTop
      (𝓝 (finiteQPochhammerIn q q k)⁻¹) := by
  simpa only [Function.comp_def] using
    (tendsto_gaussianBinomial_atTop hq k).comp (tendsto_add_atTop_nat r)

/-- **Effective fixed-column limit.**  For fixed `k`,

`[n,k]_q - 1/(q;q)_k = O(q^(n-k+1))`.

The denominator-free identity
`(q;q)_k [n,k]_q = (q^(n-k+1);q)_k` reduces the claim to the effective
finite-product estimate above. -/
theorem isBigO_gaussianBinomial_sub_inv {q : 𝕜}
    (hq : ‖q‖ < 1) (k : ℕ) :
    (fun n : ℕ => gaussianBinomial q n k - (finiteQPochhammerIn q q k)⁻¹) =O[atTop]
      (fun n : ℕ => q ^ (n - k + 1)) := by
  have hk0 : finiteQPochhammerIn q q k ≠ 0 := finiteQPochhammerIn_self_ne_zero hq k
  have hshift : Tendsto (fun n : ℕ => n - k + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp (tendsto_sub_atTop_nat k)
  have hnum :
      (fun n : ℕ => finiteQPochhammerIn (q ^ (n - k + 1)) q k - 1) =O[atTop]
        (fun n : ℕ => q ^ (n - k + 1)) := by
    simpa only [Function.comp_def] using
      (isBigO_finiteQPochhammerIn_pow_sub_one hq k).comp_tendsto hshift
  have hscaled := hnum.const_mul_left (finiteQPochhammerIn q q k)⁻¹
  refine hscaled.congr' ?_ (Filter.Eventually.of_forall fun _ => rfl)
  filter_upwards [eventually_ge_atTop k] with n hn
  have hG := finiteQPochhammerIn_self_mul_gaussianBinomial q hn
  rw [← hG, mul_sub, ← mul_assoc, inv_mul_cancel₀ hk0, one_mul, mul_one]

/-- The shifted effective limit has the cleaner rate
`[n+k,k]_q - 1/(q;q)_k = O(q^(n+1))`. -/
theorem isBigO_gaussianBinomial_add_sub_inv {q : 𝕜}
    (hq : ‖q‖ < 1) (k : ℕ) :
    (fun n : ℕ => gaussianBinomial q (n + k) k - (finiteQPochhammerIn q q k)⁻¹) =O[atTop]
      (fun n : ℕ => q ^ (n + 1)) := by
  simpa only [Function.comp_def, Nat.add_sub_cancel] using
    (isBigO_gaussianBinomial_sub_inv hq k).comp_tendsto
      (tendsto_add_atTop_nat k)

end NormBounds

/-! ## A superexponentially decaying majorant -/

/-- `∑_k r^{C(k,2)} s^k` converges for `0 ≤ r < 1` and `s ≥ 0`: beyond
`k ≥ 2m + 1` one has `C(k,2) ≥ mk`, so the terms are dominated by the
geometric sequence `(r^m s)^k`, where `m` is chosen with `r^m s < 1`. -/
theorem summable_pow_choose_two_mul_pow {r s : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (hs : 0 ≤ s) :
    Summable fun k : ℕ => r ^ k.choose 2 * s ^ k := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, r ^ m * s < 1 := by
    have h : Tendsto (fun m : ℕ => r ^ m * s) atTop (𝓝 (0 * s)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr).mul_const s
    rw [zero_mul] at h
    exact (h.eventually_lt_const zero_lt_one).exists
  have hgeom : Summable fun k : ℕ => (r ^ m * s) ^ k :=
    summable_geometric_of_lt_one (mul_nonneg (pow_nonneg hr0 m) hs) hm
  refine hgeom.of_norm_bounded_eventually ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop (2 * m + 1)] with k hk
  have hkm : m * k ≤ k.choose 2 := by
    have h2 := Fabius.two_mul_choose_two_add k
    rw [sq] at h2
    have h3 : 2 * (m * k) + k ≤ k * k := by
      calc 2 * (m * k) + k = k * (2 * m + 1) := by ring
        _ ≤ k * k := Nat.mul_le_mul_left k hk
    omega
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (pow_nonneg hr0 _) (pow_nonneg hs k)), mul_pow, ← pow_mul]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hr0 hr.le hkm) (pow_nonneg hs k)

/-! ## Euler's identities and the q-binomial theorem -/

section Identities

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-- **Euler's product expansion.**  For `‖q‖ < 1` and every `z`,
`(z;q)_∞ = ∑_k (-1)^k q^{C(k,2)} z^k / (q;q)_k`: the finite `q`-binomial
theorem, with `[N,k]_q → 1/(q;q)_k`, under dominated convergence. -/
theorem hasSum_euler_product {q : 𝕜} (hq : ‖q‖ < 1) (z : 𝕜) :
    HasSum (fun k : ℕ => (-1 : 𝕜) ^ k * q ^ k.choose 2 / finiteQPochhammerIn q q k * z ^ k)
      (qPochhammerInfIn z q) := by
  have hgm : 0 ≤ gaussianMajorant q := gaussianMajorant_nonneg hq
  refine hasSum_of_tendsto_of_dominated
    (f := fun n k => (-1 : 𝕜) ^ k * q ^ k.choose 2 * gaussianBinomial q n k * z ^ k)
    (bound := fun k => gaussianMajorant q * (‖q‖ ^ k.choose 2 * ‖z‖ ^ k))
    (S := fun n => finiteQPochhammerIn z q n)
    ?_ ?_ ?_ ?_ (tendsto_finiteQPochhammerIn_qPochhammerInfIn z hq)
  · exact (summable_pow_choose_two_mul_pow (norm_nonneg q) hq (norm_nonneg z)).mul_left _
  · intro k
    have h := ((tendsto_gaussianBinomial_atTop hq k).const_mul
      ((-1 : 𝕜) ^ k * q ^ k.choose 2)).mul_const (z ^ k)
    simpa only [div_eq_mul_inv] using h
  · intro n k
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have h := norm_gaussianBinomial_le hq n k
    calc ‖q‖ ^ k.choose 2 * ‖gaussianBinomial q n k‖ * ‖z‖ ^ k
        ≤ ‖q‖ ^ k.choose 2 * gaussianMajorant q * ‖z‖ ^ k := by gcongr
      _ = gaussianMajorant q * (‖q‖ ^ k.choose 2 * ‖z‖ ^ k) := by ring
  · intro n
    have hsupp : ∀ k ∉ Finset.range (n + 1),
        (-1 : 𝕜) ^ k * q ^ k.choose 2 * gaussianBinomial q n k * z ^ k = 0 := by
      intro k hk
      rw [Finset.mem_range, not_lt] at hk
      rw [gaussianBinomial_eq_zero_of_lt q hk]
      ring
    rw [← finite_qBinomial_theorem q z n]
    exact hasSum_sum_of_ne_finset_zero hsupp

/-- `(z;q)_∞ ≠ 0` when `‖z‖ < 1` and `‖q‖ < 1`. -/
theorem qPochhammerInfIn_ne_zero_of_norm_lt_one {q z : 𝕜} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    qPochhammerInfIn z q ≠ 0 := by
  refine qPochhammerInfIn_ne_zero z hq fun j h => ?_
  have h1 : ‖z * q ^ j‖ < 1 := by
    calc ‖z * q ^ j‖ = ‖z‖ * ‖q‖ ^ j := by rw [norm_mul, norm_pow]
      _ ≤ ‖z‖ * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg q) hq.le) (norm_nonneg z)
      _ < 1 := by simpa using hz
  rw [h, norm_one] at h1
  exact lt_irrefl _ h1

/-- **The infinite `q`-binomial theorem.**  For `‖q‖ < 1`, `‖z‖ < 1`, and
every `a`,
`∑_k (a;q)_k / (q;q)_k · z^k = (az;q)_∞ / (z;q)_∞`.
It is the finite `q`-Cauchy identity divided by `(z;q)_N`, in the limit
`N → ∞`, under dominated convergence. -/
theorem hasSum_qBinomial_theorem {q : 𝕜} (hq : ‖q‖ < 1) (a : 𝕜) {z : 𝕜} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => finiteQPochhammerIn a q k / finiteQPochhammerIn q q k * z ^ k)
      (qPochhammerInfIn (a * z) q / qPochhammerInfIn z q) := by
  have hz0 : qPochhammerInfIn z q ≠ 0 := qPochhammerInfIn_ne_zero_of_norm_lt_one hq hz
  have hgm : 0 ≤ gaussianMajorant q := gaussianMajorant_nonneg hq
  have hA : 0 ≤ qPochhammerInfIn (-‖a‖) ‖q‖ :=
    zero_le_one.trans (one_le_qPochhammerInfIn_neg (norm_nonneg a) (norm_nonneg q) hq)
  have hZ : 0 ≤ qPochhammerInfIn (-‖z‖) ‖q‖ :=
    zero_le_one.trans (one_le_qPochhammerInfIn_neg (norm_nonneg z) (norm_nonneg q) hq)
  have hB : 0 < qPochhammerInfIn ‖z‖ ‖q‖ :=
    qPochhammerInfIn_pos_of_lt_one (norm_nonneg z) hz (norm_nonneg q) hq
  refine hasSum_of_tendsto_of_dominated
    (f := fun n k => gaussianBinomial q n k * finiteQPochhammerIn a q k * z ^ k *
      finiteQPochhammerIn z q (n - k) / finiteQPochhammerIn z q n)
    (bound := fun k => gaussianMajorant q * qPochhammerInfIn (-‖a‖) ‖q‖ *
      qPochhammerInfIn (-‖z‖) ‖q‖ / qPochhammerInfIn ‖z‖ ‖q‖ * ‖z‖ ^ k)
    (S := fun n => finiteQPochhammerIn (a * z) q n / finiteQPochhammerIn z q n)
    ?_ ?_ ?_ ?_ ?_
  · exact (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left _
  · intro k
    have h1 := tendsto_gaussianBinomial_atTop hq k
    have h2 : Tendsto (fun n : ℕ => finiteQPochhammerIn z q (n - k)) atTop
        (𝓝 (qPochhammerInfIn z q)) :=
      (tendsto_finiteQPochhammerIn_qPochhammerInfIn z hq).comp (tendsto_sub_atTop_nat k)
    have h3 := tendsto_finiteQPochhammerIn_qPochhammerInfIn z hq
    have h := (((h1.mul_const (finiteQPochhammerIn a q k)).mul_const (z ^ k)).mul h2).div h3 hz0
    have hval : (finiteQPochhammerIn q q k)⁻¹ * finiteQPochhammerIn a q k * z ^ k *
        qPochhammerInfIn z q / qPochhammerInfIn z q =
        finiteQPochhammerIn a q k / finiteQPochhammerIn q q k * z ^ k := by
      rw [mul_div_assoc, div_self hz0, mul_one]
      ring
    rw [hval] at h
    exact h
  · intro n k
    rw [norm_div, norm_mul, norm_mul, norm_mul, norm_pow]
    have hG := norm_gaussianBinomial_le hq n k
    have ha := norm_finiteQPochhammerIn_le a hq k
    have hzk := norm_finiteQPochhammerIn_le z hq (n - k)
    have hzn := qPochhammerInfIn_norm_le_norm_finiteQPochhammerIn z hz.le hq n
    calc ‖gaussianBinomial q n k‖ * ‖finiteQPochhammerIn a q k‖ * ‖z‖ ^ k *
          ‖finiteQPochhammerIn z q (n - k)‖ / ‖finiteQPochhammerIn z q n‖
        ≤ gaussianMajorant q * qPochhammerInfIn (-‖a‖) ‖q‖ * ‖z‖ ^ k *
          qPochhammerInfIn (-‖z‖) ‖q‖ / qPochhammerInfIn ‖z‖ ‖q‖ := by gcongr
      _ = gaussianMajorant q * qPochhammerInfIn (-‖a‖) ‖q‖ *
          qPochhammerInfIn (-‖z‖) ‖q‖ / qPochhammerInfIn ‖z‖ ‖q‖ * ‖z‖ ^ k := by ring
  · intro n
    have hsupp : ∀ k ∉ Finset.range (n + 1),
        gaussianBinomial q n k * finiteQPochhammerIn a q k * z ^ k *
          finiteQPochhammerIn z q (n - k) / finiteQPochhammerIn z q n = 0 := by
      intro k hk
      rw [Finset.mem_range, not_lt] at hk
      rw [gaussianBinomial_eq_zero_of_lt q hk]
      ring
    have hfin : ∑ k ∈ Finset.range (n + 1),
        gaussianBinomial q n k * finiteQPochhammerIn a q k * z ^ k *
          finiteQPochhammerIn z q (n - k) / finiteQPochhammerIn z q n =
        finiteQPochhammerIn (a * z) q n / finiteQPochhammerIn z q n := by
      rw [finite_qCauchy_identity q a z n, Finset.sum_div]
    rw [← hfin]
    exact hasSum_sum_of_ne_finset_zero hsupp
  · exact (tendsto_finiteQPochhammerIn_qPochhammerInfIn (a * z) hq).div
      (tendsto_finiteQPochhammerIn_qPochhammerInfIn z hq) hz0

/-- **Euler's reciprocal expansion.**  For `‖q‖ < 1` and `‖z‖ < 1`,
`1/(z;q)_∞ = ∑_k z^k / (q;q)_k`: the `q`-binomial theorem at `a = 0`. -/
theorem hasSum_euler_reciprocal {q : 𝕜} (hq : ‖q‖ < 1) {z : 𝕜} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => z ^ k / finiteQPochhammerIn q q k) (qPochhammerInfIn z q)⁻¹ := by
  have h := hasSum_qBinomial_theorem hq 0 hz
  simpa only [finiteQPochhammerIn_zero_left, zero_mul, qPochhammerInfIn_zero_left, one_div,
    inv_mul_eq_div] using h

end Identities

end

end Fabius
