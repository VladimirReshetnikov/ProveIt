import Mathlib.Analysis.MeanInequalities

/-!
# The boundary-layer maximum: `max_{[0,1]} tᵖ(1-t) = pᵖ/(p+1)^(p+1)`

The elementary optimization behind the two-adic valley law of the
Fourier-decay audit (Documents 2, 7, 8): the first lobe after a deep
zero of order `p` has height governed by
`max_{0 ≤ t ≤ 1} tᵖ(1-t) = pᵖ/(p+1)^(p+1)`, attained at
`t = p/(p+1)` — the source of the factor `∼ 1/(e·p)` and of the
maximizer location `1 - t ∼ 1/p` in the audited asymptotics
`E_{m2^k} ∼ H(1)|H(m)|/(e(k+1)) · (m2^k)^{-(k+1)}`.

* `pow_mul_one_sub_le` — the sharp bound
  `tᵖ(1-t) ≤ pᵖ/(p+1)^(p+1)` for `t ∈ [0,1]` (all `p : ℕ`, including
  `p = 0` with the convention `0⁰ = 1`), by the weighted AM–GM
  inequality with weights `p/(p+1)` and `1/(p+1)`.
* `pow_mul_one_sub_max` — attainment at `t = p/(p+1)`.
-/

set_option autoImplicit false

open Real

namespace Fabius

/-- **The boundary-layer bound**: for `t ∈ [0,1]`,
`tᵖ(1-t) ≤ pᵖ/(p+1)^(p+1)`. -/
theorem pow_mul_one_sub_le (p : ℕ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    t ^ p * (1 - t) ≤ (p : ℝ) ^ p / ((p : ℝ) + 1) ^ (p + 1) := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    simp only [pow_zero, one_mul, Nat.cast_zero, zero_add, pow_one]
    norm_num
    linarith
  have hnpos : (0:ℝ) < (p : ℝ) := by exact_mod_cast hp
  set n : ℝ := (p : ℝ) with hn_def
  have hn1 : (0:ℝ) < n + 1 := by linarith
  have hA : (0:ℝ) ≤ t * (n + 1) / n := by positivity
  have hB : (0:ℝ) ≤ (1 - t) * (n + 1) := by nlinarith
  have hw : n / (n + 1) + 1 / (n + 1) = 1 := by
    field_simp
  have hgm := Real.geom_mean_le_arith_mean2_weighted
    (by positivity : (0:ℝ) ≤ n / (n + 1))
    (by positivity : (0:ℝ) ≤ 1 / (n + 1)) hA hB hw
  have hrhs : n / (n + 1) * (t * (n + 1) / n) +
      1 / (n + 1) * ((1 - t) * (n + 1)) = 1 := by
    field_simp
    ring
  rw [hrhs] at hgm
  have hkey : (t * (n + 1) / n) ^ p * ((1 - t) * (n + 1)) ≤ 1 := by
    calc (t * (n + 1) / n) ^ p * ((1 - t) * (n + 1))
        = ((t * (n + 1) / n) ^ (n / (n + 1)) *
            ((1 - t) * (n + 1)) ^ (1 / (n + 1))) ^ (n + 1) := by
          rw [Real.mul_rpow (Real.rpow_nonneg hA _) (Real.rpow_nonneg hB _),
            ← Real.rpow_mul hA, ← Real.rpow_mul hB,
            div_mul_cancel₀ _ (ne_of_gt hn1), one_div,
            inv_mul_cancel₀ (ne_of_gt hn1), Real.rpow_one, hn_def,
            Real.rpow_natCast]
      _ ≤ 1 ^ (n + 1) :=
          Real.rpow_le_rpow (by positivity) hgm (by linarith)
      _ = 1 := Real.one_rpow _
  have hfinal : t ^ p * (1 - t) =
      ((t * (n + 1) / n) ^ p * ((1 - t) * (n + 1))) *
        (n ^ p / (n + 1) ^ (p + 1)) := by
    have hn0 : n ≠ 0 := ne_of_gt hnpos
    have hn10 : (n + 1) ≠ 0 := ne_of_gt hn1
    have hnp : n ^ p ≠ 0 := pow_ne_zero _ hn0
    have hn1p : (n + 1) ^ p ≠ 0 := pow_ne_zero _ hn10
    have hbase : (t * (n + 1) / n) ^ p = t ^ p * (n + 1) ^ p / n ^ p := by
      rw [div_pow, mul_pow]
    rw [hbase, pow_succ]
    field_simp
  calc t ^ p * (1 - t)
      = ((t * (n + 1) / n) ^ p * ((1 - t) * (n + 1))) *
          (n ^ p / (n + 1) ^ (p + 1)) := hfinal
    _ ≤ 1 * (n ^ p / (n + 1) ^ (p + 1)) :=
        mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = n ^ p / (n + 1) ^ (p + 1) := one_mul _

/-- **Attainment**: at `t = p/(p+1)` the boundary-layer bound is an
equality, `(p/(p+1))ᵖ·(1 - p/(p+1)) = pᵖ/(p+1)^(p+1)`. -/
theorem pow_mul_one_sub_max (p : ℕ) :
    ((p : ℝ) / ((p : ℝ) + 1)) ^ p * (1 - (p : ℝ) / ((p : ℝ) + 1)) =
      (p : ℝ) ^ p / ((p : ℝ) + 1) ^ (p + 1) := by
  have h1 : ((p : ℝ) + 1) ≠ 0 := by positivity
  have h2 : 1 - (p : ℝ) / ((p : ℝ) + 1) = 1 / ((p : ℝ) + 1) := by
    field_simp
    ring
  rw [h2, div_pow, pow_succ]
  field_simp

end Fabius
