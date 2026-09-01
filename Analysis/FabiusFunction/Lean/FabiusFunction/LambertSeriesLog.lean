import FabiusFunction.QPochhammerInfinite
import FabiusFunction.EulerLogTransform

/-!
# The Lambert-series logarithm of the infinite q-Pochhammer product

`EulerLogTransform` proves the Lambert-series identity for the logarithms of
the factors of the geometric Euler product,

`∑_j log(1 - a q^j) = -∑_{m≥0} a^{m+1} / ((m+1)(1 - q^{m+1}))`,

for `‖a‖ < 1` and `‖q‖ < 1` (`tsum_log_one_sub_geom`).  This module packages
its two consequences for the infinite `q`-Pochhammer symbol:

* the series form `∑_m a^{m+1}/((m+1)(1-q^{m+1})) = -∑_j log(1 - a q^j)` as a
  `HasSum`, and
* the branch-free exponential form `exp(-∑_m a^m/(m(1-q^m))) = (a;q)_∞`,
  obtained by exponentiating the sum of the principal logarithms of the
  nonvanishing factors.

## Main declarations

* `summable_lambert_series`: absolute convergence of the Lambert series.
* `hasSum_lambert_log_complex`: the series identity in `HasSum` form.
* `exp_neg_tsum_lambert_eq_qPochhammerInfIn`: the exponential form.
-/

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace Fabius

/-- `1 ≤ ‖(m + 1 : ℂ)‖`. -/
theorem one_le_norm_natCast_add_one (m : ℕ) : (1 : ℝ) ≤ ‖((m : ℂ) + 1)‖ := by
  rw [← Nat.cast_succ, Complex.norm_natCast]
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)

/-- The Lambert series `∑_m a^{m+1}/((m+1)(1 - q^{m+1}))` is absolutely
convergent for `‖a‖ < 1`, `‖q‖ < 1`: its terms are dominated by
`‖a‖^{m+1}/(1 - ‖q‖)`. -/
theorem summable_lambert_series {a q : ℂ} (ha : ‖a‖ < 1) (hq : ‖q‖ < 1) :
    Summable fun m : ℕ => a ^ (m + 1) / ((m + 1) * (1 - q ^ (m + 1))) := by
  have h1q : 0 < 1 - ‖q‖ := by linarith
  have hgeom : Summable fun m : ℕ => ‖a‖ ^ (m + 1) * (1 - ‖q‖)⁻¹ :=
    ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg a) ha)).mul_right _
  refine hgeom.of_norm_bounded fun m => ?_
  rw [norm_div, norm_pow, norm_mul]
  have hm := one_le_norm_natCast_add_one m
  have hden : 1 - ‖q‖ ≤ ‖(1 : ℂ) - q ^ (m + 1)‖ := by
    have hp : ‖q‖ ^ (m + 1) ≤ ‖q‖ := pow_le_of_le_one (norm_nonneg q) hq.le (Nat.succ_ne_zero m)
    calc 1 - ‖q‖ ≤ 1 - ‖q‖ ^ (m + 1) := by linarith
      _ = ‖(1 : ℂ)‖ - ‖q ^ (m + 1)‖ := by rw [norm_one, norm_pow]
      _ ≤ ‖(1 : ℂ) - q ^ (m + 1)‖ := norm_sub_norm_le _ _
  calc ‖a‖ ^ (m + 1) / (‖((m : ℂ) + 1)‖ * ‖(1 : ℂ) - q ^ (m + 1)‖)
      ≤ ‖a‖ ^ (m + 1) / (1 * (1 - ‖q‖)) :=
        div_le_div_of_nonneg_left (by positivity) (by simpa using h1q)
          (mul_le_mul hm hden h1q.le (norm_nonneg _))
    _ = ‖a‖ ^ (m + 1) * (1 - ‖q‖)⁻¹ := by rw [one_mul, div_eq_mul_inv]

/-- **The Lambert-series logarithm**, `HasSum` form: for `‖a‖ < 1` and
`‖q‖ < 1`, `∑_{m≥0} a^{m+1}/((m+1)(1 - q^{m+1})) = -∑_j log(1 - a q^j)`, with
the principal logarithm of each factor. -/
theorem hasSum_lambert_log_complex {a q : ℂ} (ha : ‖a‖ < 1) (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ => a ^ (m + 1) / ((m + 1) * (1 - q ^ (m + 1))))
      (-∑' j : ℕ, Complex.log (1 - a * q ^ j)) := by
  rw [tsum_log_one_sub_geom ha hq, neg_neg]
  exact (summable_lambert_series ha hq).hasSum

/-- **The exponential form**: `exp(-∑_{m≥1} a^m/(m(1 - q^m))) = (a;q)_∞` for
`‖a‖ < 1`, `‖q‖ < 1`. -/
theorem exp_neg_tsum_lambert_eq_qPochhammerInfIn {a q : ℂ} (ha : ‖a‖ < 1) (hq : ‖q‖ < 1) :
    Complex.exp (-∑' m : ℕ, a ^ (m + 1) / ((m + 1) * (1 - q ^ (m + 1)))) =
      qPochhammerInfIn a q := by
  rw [(hasSum_lambert_log_complex ha hq).tsum_eq, neg_neg]
  have hne : ∀ j : ℕ, 1 - a * q ^ j ≠ 0 := fun j => by
    refine one_sub_ne_zero_of_norm_lt_one ?_
    rw [norm_mul, norm_pow]
    calc ‖a‖ * ‖q‖ ^ j ≤ ‖a‖ * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg q) hq.le) (norm_nonneg a)
      _ < 1 := by simpa using ha
  have hlog : Summable fun j : ℕ => Complex.log (1 - a * q ^ j) := by
    have hs : Summable fun j : ℕ => -(a * q ^ j) :=
      ((summable_geometric_of_norm_lt_one hq).mul_left a).neg
    refine (Complex.summable_log_one_add_of_summable hs).congr fun j => ?_
    rw [← sub_eq_add_neg]
  exact Complex.cexp_tsum_eq_tprod hne hlog

end Fabius
