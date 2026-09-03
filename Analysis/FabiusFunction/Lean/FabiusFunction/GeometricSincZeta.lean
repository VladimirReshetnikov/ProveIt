import FabiusFunction.SincZetaDyadic
import FabiusFunction.RvachevPochhammerFactorization

/-!
# The all-orders zeta expansion of the geometric sinc product

`SincZetaDyadic` proves the atlas's `thm:all-orders-Q` for the dyadic sinc
product: `Φ(z) = ∏_h sinc(πz/2^h)` equals, on `‖z‖ < 1`,
`exp(-∑_r ζ(2r) 4^r z^{2r} / (r (4^r - 1)))`.  The only dyadic input is
the geometric collapse `∑_h 4^{-rh} = 4^r/(4^r - 1)`.  This file runs the
same Euler–zeta engine at an **arbitrary contracting ratio** `q`, for the
corpus's `geometricSincProduct q z = ∏' n, sinc(π q^n z)`:

`geometricSincProduct q z
  = exp (-∑_{r ≥ 1} ζ(2r) z^{2r} / (r (1 - q^{2r})))`   on `‖z‖ < 1`, `‖q‖ < 1`,

with the finite-prefix form on `‖q^m z‖ < 1`.  The dyadic theorem is the
case `q = 1/2`, and the atlas's **general geometric base** theorem
`p2:thm:base-b` — `Q_{∞,b}(t) = ∏_{k≥1} sinc(t/b^k)` and

`log (Q_{∞,b}/Q_{m,b})(t) = -∑_{r≥1} ζ(2r) t^{2r} q^{r(m+1)} / (r π^{2r} (1-q^r))`,
`q = b^{-2}`, on `|t| < π b^{m+1}` —

is the case `q = 1/b` read at `z = t/(π b)`, which is
`base_geometric_sinc_eq_prefix_mul_cexp` below, stated in exponential form
with the prefix cleared.

## Main declarations

* `tsum_pow_mul_even_pow` — the geometric collapse
  `∑'_h (q^h z)^{2k} = z^{2k}/(1 - q^{2k})`.
* `geometric_sinc_pair_powerSum` — power sums of the pair family
  `(q^h z)²/(n+1)²`, for every `z` (no smallness).
* `geometricSincProduct_eq_cexp` — **the master Euler–zeta form** at ratio `q`.
* `geometricSincProduct_pow_mul` — the prefix shift
  `S_q(z) = (∏_{j<m} sinc(π q^j z)) · S_q(q^m z)`.
* `geometricSincProduct_eq_prefix_mul_cexp` — **the all-orders prefix form**.
* `base_geometric_sinc_eq_prefix_mul_cexp` — **`p2:thm:base-b`**, for a real
  base `b > 1`, on `‖t‖ < π b^{m+1}`.
-/

set_option autoImplicit false

namespace Fabius

open Real Finset

/-! ## The geometric collapse -/

/-- `∑'_h (q^h z)^{2k} = z^{2k} / (1 - q^{2k})` for `‖q‖ < 1`, `k ≠ 0`. -/
theorem tsum_pow_mul_even_pow {q : ℂ} (hq : ‖q‖ < 1) (z : ℂ) {k : ℕ} (hk : k ≠ 0) :
    ∑' h : ℕ, (q ^ h * z) ^ (2 * k) = z ^ (2 * k) / (1 - q ^ (2 * k)) := by
  have hlt : ‖q ^ (2 * k)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
  calc ∑' h : ℕ, (q ^ h * z) ^ (2 * k)
      = ∑' h : ℕ, z ^ (2 * k) * (q ^ (2 * k)) ^ h := tsum_congr fun h => by ring
    _ = z ^ (2 * k) * (1 - q ^ (2 * k))⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hlt]
    _ = z ^ (2 * k) / (1 - q ^ (2 * k)) := (div_eq_mul_inv _ _).symm

/-- Norms of the geometric pair family: `‖(q^h z)²/(n+1)²‖ = ‖sineTerm‖`. -/
theorem norm_pair_eq_norm_sineTerm (q z : ℂ) (p : ℕ × ℕ) :
    ‖(q ^ p.1 * z) ^ 2 / ((p.2 : ℂ) + 1) ^ 2‖ = ‖sineTerm (q ^ p.1 * z) p.2‖ := by
  have h := one_add_sineTerm_eq_one_sub_sq_div (q ^ p.1 * z) p.2
  have h' : sineTerm (q ^ p.1 * z) p.2 = -((q ^ p.1 * z) ^ 2 / ((p.2 : ℂ) + 1) ^ 2) := by
    linear_combination h
  rw [h', norm_neg]

/-- **Power sums of the geometric pair family**, for every `z`:

`∑'_{(h,n)} ((q^h z)²/(n+1)²)^(r+1) = ζ(2(r+1)) z^(2(r+1)) / (1 - q^(2(r+1)))`. -/
theorem geometric_sinc_pair_powerSum {q : ℂ} (hq : ‖q‖ < 1) (z : ℂ) (r : ℕ) :
    ∑' p : ℕ × ℕ, ((q ^ p.1 * z) ^ 2 / ((p.2 : ℂ) + 1) ^ 2) ^ (r + 1) =
      (evenZeta (r + 1) : ℂ) * z ^ (2 * (r + 1)) / (1 - q ^ (2 * (r + 1))) := by
  have hterm : ∀ p : ℕ × ℕ,
      ((q ^ p.1 * z) ^ 2 / ((p.2 : ℂ) + 1) ^ 2) ^ (r + 1) =
        ((q ^ p.1 * z) ^ 2) ^ (r + 1) * (1 / ((p.2 : ℂ) + 1) ^ 2) ^ (r + 1) := by
    intro p
    rw [div_eq_mul_one_div, mul_pow]
  have hf : Summable fun h : ℕ => ‖((q ^ h * z) ^ 2) ^ (r + 1)‖ := by
    have hgeo : Summable fun h : ℕ => ‖z‖ ^ (2 * (r + 1)) * (‖q‖ ^ (2 * (r + 1))) ^ h := by
      refine (summable_geometric_of_lt_one (by positivity) ?_).mul_left _
      exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
    refine hgeo.congr fun h => Eq.symm ?_
    rw [← pow_mul, norm_pow, norm_mul, norm_pow]
    ring
  have hg : Summable fun n : ℕ => ‖(1 / ((n : ℂ) + 1) ^ 2) ^ (r + 1)‖ := by
    refine (summable_one_div_add_one_pow r.succ_ne_zero).congr fun n => Eq.symm ?_
    rw [one_div_pow, ← pow_mul, norm_div, norm_one, norm_pow, norm_natCast_add_one]
  have hFsum : Summable fun p : ℕ × ℕ =>
      ((q ^ p.1 * z) ^ 2 / ((p.2 : ℂ) + 1) ^ 2) ^ (r + 1) := by
    refine Summable.of_norm ?_
    refine (hf.mul_of_nonneg hg (fun h => norm_nonneg _)
      (fun n => norm_nonneg _)).congr fun p => Eq.symm ?_
    rw [hterm p, norm_mul]
  have hfiber : ∀ h : ℕ, Summable fun n : ℕ =>
      ((q ^ h * z) ^ 2 / ((n : ℂ) + 1) ^ 2) ^ (r + 1) := by
    intro h
    have hgc : Summable fun n : ℕ => (1 / ((n : ℂ) + 1) ^ 2) ^ (r + 1) :=
      Summable.of_norm hg
    refine (hgc.mul_left (((q ^ h * z) ^ 2) ^ (r + 1))).congr fun n => ?_
    exact (hterm (h, n)).symm
  rw [hFsum.tsum_prod' hfiber]
  calc ∑' h : ℕ, ∑' n : ℕ, ((q ^ h * z) ^ 2 / ((n : ℂ) + 1) ^ 2) ^ (r + 1)
      = ∑' h : ℕ, (evenZeta (r + 1) : ℂ) * (q ^ h * z) ^ (2 * (r + 1)) :=
        tsum_congr fun h => sinc_family_powerSum (q ^ h * z) r
    _ = (evenZeta (r + 1) : ℂ) * ∑' h : ℕ, (q ^ h * z) ^ (2 * (r + 1)) :=
        tsum_mul_left
    _ = (evenZeta (r + 1) : ℂ) * (z ^ (2 * (r + 1)) / (1 - q ^ (2 * (r + 1)))) := by
        rw [tsum_pow_mul_even_pow hq z r.succ_ne_zero]
    _ = (evenZeta (r + 1) : ℂ) * z ^ (2 * (r + 1)) / (1 - q ^ (2 * (r + 1))) := by
        rw [mul_div_assoc']

/-! ## The Euler–zeta form -/

/-- **The master Euler–zeta form of the geometric sinc product**: for
`‖q‖ < 1` and `‖z‖ < 1`,

`S_q(z) = exp (-∑'_r ζ(2(r+1)) z^(2(r+1)) / ((r+1) (1 - q^(2(r+1)))))`. -/
theorem geometricSincProduct_eq_cexp {q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    geometricSincProduct q z =
      Complex.exp (-∑' r : ℕ,
        (evenZeta (r + 1) : ℂ) * z ^ (2 * (r + 1)) /
          (((r : ℂ) + 1) * (1 - q ^ (2 * (r + 1))))) := by
  have hlt : ∀ p : ℕ × ℕ, ‖(q ^ p.1 * z) ^ 2 / ((p.2 : ℂ) + 1) ^ 2‖ < 1 := by
    intro p
    have hzp : ‖q ^ p.1 * z‖ < 1 := by
      rw [norm_mul, norm_pow]
      calc ‖q‖ ^ p.1 * ‖z‖ ≤ 1 * ‖z‖ := by
            gcongr
            exact pow_le_one₀ (norm_nonneg _) hq.le
        _ < 1 := by rw [one_mul]; exact hz
    exact sinc_family_norm_lt_one hzp p.2
  have hsum : Summable fun p : ℕ × ℕ => ‖(q ^ p.1 * z) ^ 2 / ((p.2 : ℂ) + 1) ^ 2‖ :=
    (summable_norm_sineTerm_qpow_pair hq z).congr fun p =>
      (norm_pair_eq_norm_sineTerm q z p).symm
  rw [geometricSincProduct_eq_tprod_pair hq,
    tprod_congr fun p : ℕ × ℕ => one_add_sineTerm_eq_one_sub_sq_div (q ^ p.1 * z) p.2,
    tprod_one_sub_eq_cexp_powerSum hlt hsum]
  congr 2
  refine tsum_congr fun r => ?_
  rw [geometric_sinc_pair_powerSum hq, div_div,
    mul_comm (1 - q ^ (2 * (r + 1))) ((r : ℂ) + 1)]

/-- The one-step peel: `S_q(z) = sinc(π z) · S_q(q z)`.  Same mechanism as the
corpus's `tprod_geom_scale`: peel the first factor with `tprod_eq_zero_mul'`
and re-index the tail. -/
theorem geometricSincProduct_mul_shift {q : ℂ} (hq : ‖q‖ < 1) (z : ℂ) :
    geometricSincProduct q z =
      complexSinc (π * z) * geometricSincProduct q (q * z) := by
  have harg : (fun n : ℕ => complexSinc (Real.pi * (q ^ (n + 1) * z))) =
      fun n : ℕ => complexSinc (Real.pi * (q ^ n * (q * z))) :=
    funext fun n => by
      congr 1
      rw [pow_succ]
      ring
  have hmult := geometricSincProductFactors_multipliable q (q * z) hq
  unfold geometricSincProduct
  rw [tprod_eq_zero_mul' (harg ▸ hmult), harg, pow_zero, one_mul]

/-- The prefix shift: `S_q(z) = (∏_{j<m} sinc(π q^j z)) · S_q(q^m z)`, by
iterating the one-step peel. -/
theorem geometricSincProduct_pow_mul {q : ℂ} (hq : ‖q‖ < 1) (z : ℂ) (m : ℕ) :
    geometricSincProduct q z =
      (∏ j ∈ range m, complexSinc (π * (q ^ j * z))) * geometricSincProduct q (q ^ m * z) := by
  induction m generalizing z with
  | zero => simp
  | succ m ih =>
      rw [geometricSincProduct_mul_shift hq z, ih (q * z), prod_range_succ']
      have h1 : ∀ j ∈ range m,
          complexSinc (π * (q ^ j * (q * z))) = complexSinc (π * (q ^ (j + 1) * z)) := by
        intro j _
        congr 1
        rw [pow_succ]
        ring
      have h2 : q ^ m * (q * z) = q ^ (m + 1) * z := by
        rw [pow_succ]
        ring
      rw [prod_congr rfl h1, h2, pow_zero, one_mul]
      ring

/-- **The all-orders prefix form** at ratio `q`: on `‖q^m z‖ < 1`,

`S_q(z) = (∏_{j<m} sinc(π q^j z)) ·
  exp (-∑'_r ζ(2(r+1)) (q^m z)^(2(r+1)) / ((r+1)(1 - q^(2(r+1)))))`. -/
theorem geometricSincProduct_eq_prefix_mul_cexp {q z : ℂ} (hq : ‖q‖ < 1) {m : ℕ}
    (hz : ‖q ^ m * z‖ < 1) :
    geometricSincProduct q z =
      (∏ j ∈ range m, complexSinc (π * (q ^ j * z))) *
        Complex.exp (-∑' r : ℕ,
          (evenZeta (r + 1) : ℂ) * (q ^ m * z) ^ (2 * (r + 1)) /
            (((r : ℂ) + 1) * (1 - q ^ (2 * (r + 1))))) := by
  rw [geometricSincProduct_pow_mul hq z m, geometricSincProduct_eq_cexp hq hz]

/-! ## The general geometric base -/

/-- The base-`b` product `∏_{k ≥ 1} sinc(t / b^k)` is the geometric sinc
product at ratio `1/b` and argument `t/(π b)`. -/
theorem tprod_complexSinc_div_pow_eq_geometricSincProduct {b : ℝ} (hb : 0 < b) (t : ℂ) :
    ∏' k : ℕ, complexSinc (t / (b : ℂ) ^ (k + 1)) =
      geometricSincProduct ((b : ℂ)⁻¹) (t / (π * b)) := by
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold geometricSincProduct
  refine tprod_congr fun k => ?_
  congr 1
  have hbk : ((b : ℂ) ^ k) ≠ 0 := pow_ne_zero _ hbC
  rw [pow_succ, inv_pow]
  field_simp
  try ring

/-- **`p2:thm:base-b`** (exponential form, prefix cleared).  For a real base
`b > 1` and `‖t‖ < π b^{m+1}`,

`∏_{k≥1} sinc(t/b^k) = (∏_{k=1}^{m} sinc(t/b^k)) ·
  exp (-∑'_r ζ(2(r+1)) (t/(π b^{m+1}))^(2(r+1)) / ((r+1) (1 - (b⁻¹)^(2(r+1)))))`,

which is the atlas's `log(Q_{∞,b}/Q_{m,b}) = -∑_{r≥1} ζ(2r) t^{2r} q^{r(m+1)} /
(r π^{2r} (1 - q^r))` with `q = b^{-2}`. -/
theorem base_geometric_sinc_eq_prefix_mul_cexp {b : ℝ} (hb : 1 < b) (t : ℂ) {m : ℕ}
    (ht : ‖t‖ < π * b ^ (m + 1)) :
    ∏' k : ℕ, complexSinc (t / (b : ℂ) ^ (k + 1)) =
      (∏ j ∈ range m, complexSinc (t / (b : ℂ) ^ (j + 1))) *
        Complex.exp (-∑' r : ℕ,
          (evenZeta (r + 1) : ℂ) * (t / (π * (b : ℂ) ^ (m + 1))) ^ (2 * (r + 1)) /
            (((r : ℂ) + 1) * (1 - ((b : ℂ)⁻¹) ^ (2 * (r + 1))))) := by
  have hb0 : 0 < b := by linarith
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb0.ne'
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hq : ‖(b : ℂ)⁻¹‖ < 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb0]
    exact inv_lt_one_of_one_lt₀ hb
  have hz : ‖((b : ℂ)⁻¹) ^ m * (t / (π * b))‖ < 1 := by
    have hval : ((b : ℂ)⁻¹) ^ m * (t / (π * b)) = t / (π * (b : ℂ) ^ (m + 1)) := by
      have hbm : ((b : ℂ) ^ m) ≠ 0 := pow_ne_zero _ hbC
      rw [pow_succ, inv_pow]
      field_simp
      try ring
    rw [hval, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb0,
      div_lt_one (by positivity)]
    exact ht
  rw [tprod_complexSinc_div_pow_eq_geometricSincProduct hb0 t,
    geometricSincProduct_eq_prefix_mul_cexp hq hz]
  congr 1
  · refine prod_congr rfl fun j _ => ?_
    congr 1
    have hbj : ((b : ℂ) ^ j) ≠ 0 := pow_ne_zero _ hbC
    rw [pow_succ, inv_pow]
    field_simp
    try ring
  · congr 2
    refine tsum_congr fun r => ?_
    congr 2
    have hbm : ((b : ℂ) ^ m) ≠ 0 := pow_ne_zero _ hbC
    rw [pow_succ, inv_pow]
    field_simp
    try ring

end Fabius
