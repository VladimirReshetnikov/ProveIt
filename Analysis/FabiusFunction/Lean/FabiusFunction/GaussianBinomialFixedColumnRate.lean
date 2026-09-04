import FabiusFunction.QBinomialTheoremInfinite
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Effective fixed-column convergence of Gaussian coefficients

For a contracting nome, the numerator in the fixed-column quotient

`[n,k]_q = (q^(n-k+1);q)_k / (q;q)_k`

is a finite product whose factors approach one geometrically.  This module
turns that observation into explicit bounds.  The basic estimate works in a
normed commutative ring whose norm is multiplicative:

`||(q^m;q)_k - 1|| <= k * exp(k) * ||q||^m`.

Over a normed field, division by the nonzero fixed denominator `(q;q)_k`
then gives nonasymptotic error bounds for both `[n,k]_q` and `[n+k,k]_q`.
Their `IsBigO` corollaries are the two effective clauses of the manuscript's
fixed-column theorem.  All results include `q = 0`; in that case the errors
vanish once the displayed exponent is positive.

The upstream `QBinomialTheoremInfinite` module already supplies the general
exponential product-defect estimate and the shifted limit (for an arbitrary
fixed additive shift).  This leaf reuses those declarations and adds the
eight sharper nonasymptotic and relative/additive error results below.

## Main declarations

* `norm_finiteQPochhammerIn_pow_sub_one_le` gives the geometric bound with
  the simple fixed-column constant `k * exp k`.
* `norm_finiteQPochhammerIn_self_mul_gaussianBinomial_sub_one_le` is the
  denominator-free relative Gaussian error bound.
* `norm_gaussianBinomial_sub_inv_finiteQPochhammerIn_le` and
  `norm_gaussianBinomial_add_sub_inv_finiteQPochhammerIn_le` are the fixed
  and shifted nonasymptotic additive error bounds.
* `gaussianBinomial_fixedColumn_relativeError_isBigO` and
  `gaussianBinomial_shifted_fixedColumn_relativeError_isBigO` give the
  manuscript's multiplicative `1 + O(...)` statements.
* `gaussianBinomial_fixedColumn_error_isBigO` and
  `gaussianBinomial_shifted_fixedColumn_error_isBigO` are their additive
  counterparts.
-/

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace Fabius

noncomputable section

private theorem exp_sub_one_le_mul_exp_fixedColumn (t : ℝ) :
    Real.exp t - 1 ≤ t * Real.exp t := by
  have h := Real.add_one_le_exp (-t)
  have hpos : (0 : ℝ) < Real.exp t := Real.exp_pos t
  have hmul : (-t + 1) * Real.exp t ≤ Real.exp (-t) * Real.exp t :=
    mul_le_mul_of_nonneg_right h hpos.le
  have hcancel : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add]
    simp
  rw [hcancel] at hmul
  have hrearrange : (-t + 1) * Real.exp t =
      Real.exp t - t * Real.exp t := by ring
  rw [hrearrange] at hmul
  linarith

section FiniteProduct

variable {R : Type*} [NormedCommRing R] [NormOneClass R] [NormMulClass R]

/-- **Geometric finite-product defect bound.**  For `||q|| <= 1`,

`||(q^m;q)_k - 1|| <= (k * exp k) * ||q||^m`.

The constant is intentionally elementary rather than sharp.  Its useful
feature is that it depends only on the fixed column `k`, while the dependence
on the shift `m` is the single geometric factor `||q||^m`. -/
theorem norm_finiteQPochhammerIn_pow_sub_one_le
    (q : R) (hq : ‖q‖ ≤ 1) (m k : ℕ) :
    ‖finiteQPochhammerIn (q ^ m) q k - 1‖ ≤
      ((k : ℝ) * Real.exp (k : ℝ)) * ‖q‖ ^ m := by
  have hpow : ‖q‖ ^ m ≤ 1 :=
    pow_le_one₀ (norm_nonneg q) hq
  have ht_nonneg : 0 ≤ (k : ℝ) * ‖q‖ ^ m :=
    mul_nonneg (Nat.cast_nonneg k) (pow_nonneg (norm_nonneg q) m)
  have ht_le : (k : ℝ) * ‖q‖ ^ m ≤ (k : ℝ) := by
    calc
      (k : ℝ) * ‖q‖ ^ m ≤ (k : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg k)
      _ = (k : ℝ) := mul_one _
  calc
    ‖finiteQPochhammerIn (q ^ m) q k - 1‖ ≤
        Real.exp ((k : ℝ) * ‖q‖ ^ m) - 1 :=
      norm_finiteQPochhammerIn_pow_sub_one_le_exp hq m k
    _ ≤ ((k : ℝ) * ‖q‖ ^ m) *
        Real.exp ((k : ℝ) * ‖q‖ ^ m) :=
      exp_sub_one_le_mul_exp_fixedColumn _
    _ ≤ ((k : ℝ) * ‖q‖ ^ m) * Real.exp (k : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ht_le) ht_nonneg
    _ = ((k : ℝ) * Real.exp (k : ℝ)) * ‖q‖ ^ m := by ring

/-- **Denominator-free fixed-column Gaussian error.**  If `k <= n` and
`||q|| <= 1`, then

`||(q;q)_k [n,k]_q - 1|| <= (k * exp k) * ||q||^(n-k+1)`.

This relative form needs only a normed commutative ring with multiplicative
norm and remains meaningful at roots of unity; it is obtained before any
division by `(q;q)_k`. -/
theorem norm_finiteQPochhammerIn_self_mul_gaussianBinomial_sub_one_le
    (q : R) (hq : ‖q‖ ≤ 1) {n k : ℕ} (hk : k ≤ n) :
    ‖finiteQPochhammerIn q q k * gaussianBinomial q n k - 1‖ ≤
      ((k : ℝ) * Real.exp (k : ℝ)) * ‖q‖ ^ (n - k + 1) := by
  rw [finiteQPochhammerIn_self_mul_gaussianBinomial q hk]
  exact norm_finiteQPochhammerIn_pow_sub_one_le q hq (n - k + 1) k

end FiniteProduct

section Field

variable {K : Type*} [NormedField K]

/-- **Nonasymptotic fixed-column error.**  For `||q|| < 1` and `k <= n`,

`||[n,k]_q - (q;q)_k⁻¹||`
` <= ||(q;q)_k⁻¹|| * k * exp(k) * ||q||^(n-k+1)`.

No nonzero hypothesis on `q` is needed. -/
theorem norm_gaussianBinomial_sub_inv_finiteQPochhammerIn_le
    (q : K) (hq : ‖q‖ < 1) {n k : ℕ} (hk : k ≤ n) :
    ‖gaussianBinomial q n k - (finiteQPochhammerIn q q k)⁻¹‖ ≤
      (‖(finiteQPochhammerIn q q k)⁻¹‖ *
        ((k : ℝ) * Real.exp (k : ℝ))) * ‖q‖ ^ (n - k + 1) := by
  have hden : finiteQPochhammerIn q q k ≠ 0 :=
    finiteQPochhammerIn_self_ne_zero hq k
  have halgebra :
      gaussianBinomial q n k - (finiteQPochhammerIn q q k)⁻¹ =
        (finiteQPochhammerIn q q k)⁻¹ *
          (finiteQPochhammerIn q q k * gaussianBinomial q n k - 1) := by
    rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hden, one_mul, mul_one]
  rw [halgebra, norm_mul]
  calc
    ‖(finiteQPochhammerIn q q k)⁻¹‖ *
        ‖finiteQPochhammerIn q q k * gaussianBinomial q n k - 1‖ ≤
        ‖(finiteQPochhammerIn q q k)⁻¹‖ *
          (((k : ℝ) * Real.exp (k : ℝ)) *
            ‖q‖ ^ (n - k + 1)) :=
      mul_le_mul_of_nonneg_left
        (norm_finiteQPochhammerIn_self_mul_gaussianBinomial_sub_one_le
          q hq.le hk)
        (norm_nonneg _)
    _ = (‖(finiteQPochhammerIn q q k)⁻¹‖ *
          ((k : ℝ) * Real.exp (k : ℝ))) *
            ‖q‖ ^ (n - k + 1) := by ring

/-- **Nonasymptotic shifted fixed-column error.**  For `||q|| < 1`,

`||[n+k,k]_q - (q;q)_k⁻¹||`
` <= ||(q;q)_k⁻¹|| * k * exp(k) * ||q||^(n+1)`.

This is the second effective estimate in the fixed-column theorem, including
the `q = 0` edge case. -/
theorem norm_gaussianBinomial_add_sub_inv_finiteQPochhammerIn_le
    (q : K) (hq : ‖q‖ < 1) (n k : ℕ) :
    ‖gaussianBinomial q (n + k) k - (finiteQPochhammerIn q q k)⁻¹‖ ≤
      (‖(finiteQPochhammerIn q q k)⁻¹‖ *
        ((k : ℝ) * Real.exp (k : ℝ))) * ‖q‖ ^ (n + 1) := by
  simpa only [Nat.add_sub_cancel_right] using
    (norm_gaussianBinomial_sub_inv_finiteQPochhammerIn_le
      q hq (n := n + k) (k := k) (by omega))

/-- The relative fixed-column error is
`O(q^(n-k+1))` at infinity.  Equivalently,
`[n,k]_q = (q;q)_k⁻¹ * (1 + O(q^(n-k+1)))` after the fixed nonzero
denominator is divided out. -/
theorem gaussianBinomial_fixedColumn_relativeError_isBigO
    (q : K) (hq : ‖q‖ < 1) (k : ℕ) :
    (fun n : ℕ ↦
      finiteQPochhammerIn q q k * gaussianBinomial q n k - 1) =O[atTop]
        (fun n : ℕ ↦ q ^ (n - k + 1)) := by
  apply Asymptotics.IsBigO.of_bound ((k : ℝ) * Real.exp (k : ℝ))
  filter_upwards [eventually_ge_atTop k] with n hn
  rw [norm_pow]
  exact norm_finiteQPochhammerIn_self_mul_gaussianBinomial_sub_one_le
    q hq.le hn

/-- The shifted relative fixed-column error is `O(q^(n+1))` at infinity,
the multiplicative error clause for `[n+k,k]_q`. -/
theorem gaussianBinomial_shifted_fixedColumn_relativeError_isBigO
    (q : K) (hq : ‖q‖ < 1) (k : ℕ) :
    (fun n : ℕ ↦
      finiteQPochhammerIn q q k * gaussianBinomial q (n + k) k - 1) =O[atTop]
        (fun n : ℕ ↦ q ^ (n + 1)) := by
  apply Asymptotics.IsBigO.of_bound ((k : ℝ) * Real.exp (k : ℝ))
  filter_upwards with n
  rw [norm_pow]
  simpa only [Nat.add_sub_cancel_right] using
    (norm_finiteQPochhammerIn_self_mul_gaussianBinomial_sub_one_le
      q hq.le (n := n + k) (k := k) (by omega))

/-- The additive fixed-column error is `O(q^(n-k+1))` at infinity. -/
theorem gaussianBinomial_fixedColumn_error_isBigO
    (q : K) (hq : ‖q‖ < 1) (k : ℕ) :
    (fun n : ℕ ↦
      gaussianBinomial q n k - (finiteQPochhammerIn q q k)⁻¹) =O[atTop]
        (fun n : ℕ ↦ q ^ (n - k + 1)) := by
  apply Asymptotics.IsBigO.of_bound
    (‖(finiteQPochhammerIn q q k)⁻¹‖ *
      ((k : ℝ) * Real.exp (k : ℝ)))
  filter_upwards [eventually_ge_atTop k] with n hn
  rw [norm_pow]
  exact norm_gaussianBinomial_sub_inv_finiteQPochhammerIn_le q hq hn

/-- The additive shifted fixed-column error is `O(q^(n+1))` at infinity. -/
theorem gaussianBinomial_shifted_fixedColumn_error_isBigO
    (q : K) (hq : ‖q‖ < 1) (k : ℕ) :
    (fun n : ℕ ↦
      gaussianBinomial q (n + k) k - (finiteQPochhammerIn q q k)⁻¹) =O[atTop]
        (fun n : ℕ ↦ q ^ (n + 1)) := by
  apply Asymptotics.IsBigO.of_bound
    (‖(finiteQPochhammerIn q q k)⁻¹‖ *
      ((k : ℝ) * Real.exp (k : ℝ)))
  filter_upwards with n
  rw [norm_pow]
  exact norm_gaussianBinomial_add_sub_inv_finiteQPochhammerIn_le q hq n k

end Field

end

end Fabius
