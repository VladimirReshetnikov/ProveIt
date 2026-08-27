import FabiusFunction.ThueMorseEulerTransform
import FabiusFunction.ThueMorseGenerating
import FabiusFunction.ThueMorseAutocorrelation
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Mahler equations for the Thue–Morse series

The Thue–Morse generating series satisfies exact functional equations
under the substitution `z ↦ z²` (`PowerSeries.expand 2`).  This module
proves the formal (coefficientwise) layer of the atlas's Mahler section:

* `thueMorseSeries_mahler` — the **Mahler equation**
  `E(z) = (1-z)·E(z²)`: the two-scale sign recursion in one identity.
* `thueMorseSeries_dissection` — the iterated form
  `E(z) = P_m(z)·E(z^(2^m))` for every level `m`, the substitution
  realized as the `m`-th iterate of `z ↦ z²` and the block polynomial
  appearing through `coe_thueMorseBlockPolynomial_series`.
* `one_sub_X_mul_geometricSeriesZ` and
  `two_mul_bitZSeries_add_thueMorseSeries` — the cleared bridge between
  the zero–one and signed series: `2T + E` is the geometric series, so
  `(1-z)(2T(z) + E(z)) = 1` (`one_sub_X_mul_bridge`), the
  denominator-free form of `T = 1/(2(1-z)) - E/2`.
* `thueMorsePrefixSeries_eq` — the prefix generating function
  `∑_N S(N)·z^N = z·E(z²)`, from the exact prefix collapse.
* `autocorrelationSeries_mahler` — a **finite Mahler equation for the
  autocorrelation**, sharper than the limiting statement of the atlas:
  with `C_m(z) = ∑_k A_m(k)·z^k` the unnormalized dyadic autocorrelation
  series, `z·C_{m+1}(z) = 2^m - (1-z)²·C_m(z²)` holds exactly at every
  level.  Dividing by `2^(m+1)` and letting `m → ∞` recovers the atlas's
  `2zC(z) = 1 - (1-z)²C(z²)` for the spectral measure's Fourier data.

The substitution bookkeeping — `two_ne_zero'` (the side condition of
`PowerSeries.expand 2`), `iterate_expand_mul` and
`iterate_expand_one_sub_X` — is public so that every module iterating
the same substitution (`ThueMorseLacunaryQuotient`) reuses it instead
of re-proving it.

Everything is coefficient arithmetic; no convergence enters anywhere.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- The side condition of the Mahler substitution `PowerSeries.expand 2`. -/
theorem two_ne_zero' : (2 : ℕ) ≠ 0 := by omega

/-- **Mahler equation** for the signed series: `E(z) = (1-z)·E(z²)`. -/
theorem thueMorseSeries_mahler :
    thueMorseSeries =
      (1 - PowerSeries.X) *
        PowerSeries.expand 2 two_ne_zero' thueMorseSeries := by
  have hexp : (1 - PowerSeries.X) *
      PowerSeries.expand 2 two_ne_zero' thueMorseSeries =
      PowerSeries.expand 2 two_ne_zero' thueMorseSeries -
        PowerSeries.X * PowerSeries.expand 2 two_ne_zero' thueMorseSeries := by
    ring
  rw [hexp]
  ext n
  rw [map_sub]
  rcases n with _ | k
  · rw [PowerSeries.coeff_zero_X_mul, sub_zero, PowerSeries.coeff_expand,
      if_pos (by omega : 2 ∣ 0)]
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_expand,
      PowerSeries.coeff_expand, coeff_thueMorseSeries, coeff_thueMorseSeries,
      coeff_thueMorseSeries]
    rcases Nat.even_or_odd' k with ⟨r, hk | hk⟩ <;> subst hk
    · rw [if_neg (by omega : ¬ 2 ∣ 2 * r + 1), if_pos (by omega : 2 ∣ 2 * r),
        show 2 * r / 2 = r by omega, zero_sub, thueMorseSign_two_mul_add_one]
    · rw [if_pos (by omega : 2 ∣ 2 * r + 1 + 1),
        if_neg (by omega : ¬ 2 ∣ 2 * r + 1),
        show (2 * r + 1 + 1) / 2 = r + 1 by omega, sub_zero,
        show 2 * r + 1 + 1 = 2 * (r + 1) by ring, thueMorseSign_two_mul]

/-- The coerced block polynomial is the finite series-level product. -/
theorem coe_thueMorseBlockPolynomial_series (m : ℕ) :
    ((thueMorseBlockPolynomial m : Polynomial ℤ) : PowerSeries ℤ) =
      ∏ j ∈ range m, (1 - PowerSeries.X ^ 2 ^ j) := by
  rw [thueMorseBlockPolynomial_eq_product,
    ← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [map_sub, map_one, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_X]

/-- Iterates of the Mahler substitution are multiplicative. -/
theorem iterate_expand_mul (m : ℕ) (a b : PowerSeries ℤ) :
    (⇑(PowerSeries.expand 2 two_ne_zero' (R := ℤ)))^[m] (a * b) =
      (⇑(PowerSeries.expand 2 two_ne_zero' (R := ℤ)))^[m] a *
        (⇑(PowerSeries.expand 2 two_ne_zero' (R := ℤ)))^[m] b := by
  induction m generalizing a b with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply, map_mul, ih]

/-- The `m`-th Mahler iterate of `1 - z` is `1 - z^(2^m)`. -/
theorem iterate_expand_one_sub_X (m : ℕ) :
    (⇑(PowerSeries.expand 2 two_ne_zero' (R := ℤ)))^[m] (1 - PowerSeries.X) =
      1 - PowerSeries.X ^ 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih, map_sub, map_one, map_pow,
        PowerSeries.expand_X, ← pow_mul,
        show 2 * 2 ^ m = 2 ^ (m + 1) by rw [pow_succ]; ring]

/-- **Dyadic dissection.**  For every level `m`,
`E(z) = P_m(z)·E(z^(2^m))`, with the substitution `z ↦ z^(2^m)` as the
`m`-th iterate of the Mahler substitution. -/
theorem thueMorseSeries_dissection (m : ℕ) :
    thueMorseSeries =
      (∏ j ∈ range m, (1 - PowerSeries.X ^ 2 ^ j)) *
        (⇑(PowerSeries.expand 2 two_ne_zero' (R := ℤ)))^[m] thueMorseSeries := by
  induction m with
  | zero => simp
  | succ m ih =>
      calc thueMorseSeries
          = (∏ j ∈ range m, (1 - PowerSeries.X ^ 2 ^ j)) *
              (⇑(PowerSeries.expand 2 two_ne_zero' (R := ℤ)))^[m]
                thueMorseSeries := ih
        _ = (∏ j ∈ range m, (1 - PowerSeries.X ^ 2 ^ j)) *
              (⇑(PowerSeries.expand 2 two_ne_zero' (R := ℤ)))^[m]
                ((1 - PowerSeries.X) *
                  PowerSeries.expand 2 two_ne_zero' thueMorseSeries) := by
            rw [← thueMorseSeries_mahler]
        _ = (∏ j ∈ range m, (1 - PowerSeries.X ^ 2 ^ j)) *
              ((1 - PowerSeries.X ^ 2 ^ m) *
                (⇑(PowerSeries.expand 2 two_ne_zero' (R := ℤ)))^[m + 1]
                  thueMorseSeries) := by
            rw [iterate_expand_mul, iterate_expand_one_sub_X,
              ← Function.iterate_succ_apply]
        _ = (∏ j ∈ range (m + 1), (1 - PowerSeries.X ^ 2 ^ j)) *
              (⇑(PowerSeries.expand 2 two_ne_zero' (R := ℤ)))^[m + 1]
                thueMorseSeries := by
            rw [Finset.prod_range_succ]
            ring

/-! ### The bridge between the zero–one and signed series -/

/-- The zero–one Thue–Morse series over `ℤ`. -/
def thueMorseBitZSeries : PowerSeries ℤ :=
  PowerSeries.mk fun n => (thueMorseBit n : ℤ)

/-- The geometric series is the inverse of `1 - z` over `ℤ`. -/
theorem one_sub_X_mul_geometricSeriesZ :
    (1 - PowerSeries.X) * (PowerSeries.mk fun _ => (1 : ℤ)) = 1 := by
  have h : (PowerSeries.mk fun _ => (1 : ℤ)) * (1 - PowerSeries.X) = 1 :=
    PowerSeries.mk_one_mul_one_sub_eq_one ℤ
  rw [mul_comm]
  exact h

/-- The combination `2T + E` is the geometric series: coefficientwise
`2τ(n) + ε(n) = 1`. -/
theorem two_mul_bitZSeries_add_thueMorseSeries :
    2 * thueMorseBitZSeries + thueMorseSeries =
      PowerSeries.mk fun _ => (1 : ℤ) := by
  have h2 : (2 : PowerSeries ℤ) = PowerSeries.C (2 : ℤ) := by
    rw [← map_ofNat (PowerSeries.C (R := ℤ)) 2]
  rw [h2]
  ext n
  rw [map_add, PowerSeries.coeff_C_mul, coeff_thueMorseSeries,
    PowerSeries.coeff_mk, thueMorseBitZSeries, PowerSeries.coeff_mk]
  have h := thueMorseSign_eq_one_sub_two_mul_bit n
  omega

/-- **Cleared form of `T = 1/(2(1-z)) - E/2`**:
`(1-z)·(2T(z) + E(z)) = 1`. -/
theorem one_sub_X_mul_bridge :
    (1 - PowerSeries.X) * (2 * thueMorseBitZSeries + thueMorseSeries) = 1 := by
  rw [two_mul_bitZSeries_add_thueMorseSeries, one_sub_X_mul_geometricSeriesZ]

/-! ### The prefix generating function -/

/-- The generating series of the exclusive signed prefix sums `S(N)`. -/
def thueMorsePrefixSeries : PowerSeries ℤ :=
  PowerSeries.mk fun N => ∑ t ∈ range N, thueMorseSign t

/-- **Prefix generating function**: `∑_N S(N)·z^N = z·E(z²)`, so the
prefix series is `z·∏_{j≥1} (1-z^(2^j))` under the Mahler equation. -/
theorem thueMorsePrefixSeries_eq :
    thueMorsePrefixSeries =
      PowerSeries.X * PowerSeries.expand 2 two_ne_zero' thueMorseSeries := by
  ext n
  rcases n with _ | k
  · rw [PowerSeries.coeff_zero_X_mul, thueMorsePrefixSeries,
      PowerSeries.coeff_mk]
    simp
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_expand,
      coeff_thueMorseSeries, thueMorsePrefixSeries, PowerSeries.coeff_mk,
      sum_thueMorseSign_range]
    rcases Nat.even_or_odd' k with ⟨r, hk | hk⟩ <;> subst hk
    · rw [if_neg (by omega : ¬ 2 ∣ 2 * r + 1), if_pos (by omega : 2 ∣ 2 * r),
        show (2 * r + 1) / 2 = r by omega, show 2 * r / 2 = r by omega]
    · rw [if_pos (by omega : 2 ∣ 2 * r + 1 + 1),
        if_neg (by omega : ¬ 2 ∣ 2 * r + 1)]

/-! ### The finite autocorrelation Mahler equation -/

/-- **Finite Mahler equation for the autocorrelation.**  With
`C_m(z) = ∑_k A_m(k)·z^k`,
`z·C_{m+1}(z) = 2^m - (1-z)²·C_m(z²)` — exactly, at every finite level.
After dividing by `2^(m+1)` this is the atlas's renormalization law
`2zC(z) = 1 - (1-z)²C(z²)` for the limiting spectral measure. -/
theorem autocorrelationSeries_mahler (m : ℕ) :
    PowerSeries.X *
        PowerSeries.mk (fun k => thueMorseAutocorrelation (m + 1) k) =
      PowerSeries.C ((2 : ℤ) ^ m) -
        (1 - PowerSeries.X) ^ 2 *
          PowerSeries.expand 2 two_ne_zero'
            (PowerSeries.mk fun k => thueMorseAutocorrelation m k) := by
  have hexp : (1 - PowerSeries.X) ^ 2 *
      PowerSeries.expand 2 two_ne_zero'
        (PowerSeries.mk fun k => thueMorseAutocorrelation m k) =
      PowerSeries.expand 2 two_ne_zero'
          (PowerSeries.mk fun k => thueMorseAutocorrelation m k) -
        (PowerSeries.X * PowerSeries.expand 2 two_ne_zero'
            (PowerSeries.mk fun k => thueMorseAutocorrelation m k) +
          PowerSeries.X * PowerSeries.expand 2 two_ne_zero'
            (PowerSeries.mk fun k => thueMorseAutocorrelation m k)) +
        PowerSeries.X * (PowerSeries.X *
          PowerSeries.expand 2 two_ne_zero'
            (PowerSeries.mk fun k => thueMorseAutocorrelation m k)) := by
    ring
  rw [hexp]
  ext n
  simp only [map_sub, map_add]
  rcases n with _ | k
  · rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_X_mul,
      PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_expand,
      if_pos (by omega : 2 ∣ 0), Nat.zero_div, PowerSeries.coeff_mk,
      thueMorseAutocorrelation_zero_shift, PowerSeries.coeff_C, if_pos rfl]
    ring
  · simp only [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk,
      PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero k)]
    rcases k with _ | j
    · -- n = 1: A_{m+1}(0) = 2^{m+1}
      simp only [PowerSeries.coeff_zero_X_mul,
        PowerSeries.coeff_expand, if_neg (by omega : ¬ 2 ∣ 1),
        if_pos (by omega : 2 ∣ 0), Nat.zero_div, PowerSeries.coeff_mk,
        thueMorseAutocorrelation_zero_shift]
      rw [pow_succ]
      ring
    · -- n = j + 2
      simp only [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_expand,
        PowerSeries.coeff_mk]
      rcases Nat.even_or_odd' j with ⟨r, hj | hj⟩ <;> subst hj
      · -- k = 2r + 1 odd: A_{m+1}(2r+1) = -(A_m r + A_m (r+1))
        rw [if_pos (by omega : 2 ∣ 2 * r + 1 + 1),
          if_neg (by omega : ¬ 2 ∣ 2 * r + 1),
          if_pos (by omega : 2 ∣ 2 * r),
          show (2 * r + 1 + 1) / 2 = r + 1 by omega,
          show 2 * r / 2 = r by omega,
          thueMorseAutocorrelation_succ_odd]
        ring
      · -- k = 2r + 2 = 2(r+1) even: A_{m+1}(2(r+1)) = 2·A_m(r+1)
        rw [if_neg (by omega : ¬ 2 ∣ 2 * r + 1 + 1 + 1),
          if_pos (by omega : 2 ∣ 2 * r + 1 + 1),
          if_neg (by omega : ¬ 2 ∣ 2 * r + 1),
          show (2 * r + 1 + 1) / 2 = r + 1 by omega,
          show 2 * r + 1 + 1 = 2 * (r + 1) by ring,
          thueMorseAutocorrelation_succ_even]
        ring

end Fabius
