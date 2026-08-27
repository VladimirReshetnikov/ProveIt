import FabiusFunction.ThueMorseMahler

/-!
# The lacunary quotient expansion of the bit series

Iterating the inhomogeneous Mahler equation of the zero–one series
`T(z) = ∑ τ(n)zⁿ` produces the atlas's lacunary quotient expansion.
We prove the exact finite-level identity in `ℤ⟦z⟧`, with each
"quotient" `z^(2^j)/(1-z^(2^(j+1)))` realized as an honest power
series — the dyadic geometric series — so no denominators ever occur:

`T = ∑_{j<M} P_j·z^(2^j)·G_(j+1) + P_M·T(z^(2^M))`.

* `dyadicGeometricSeries j` — `G_j = ∑_k z^(k·2^j)`, the inverse of
  `1 - z^(2^j)` (`one_sub_X_pow_mul_dyadicGeometric`).
* `thueMorseBitZSeries_mahler` — the inhomogeneous Mahler equation
  `T = (1-z)·T(z²) + z·G_1` (`eq:T-Mahler`).
* `thueMorseBitZSeries_lacunary_quotient` — the level-`M` expansion
  (`thm:lacunary-quotient`, exact finite form).
-/

set_option autoImplicit false

open Finset

namespace Fabius

private theorem two_ne : (2 : ℕ) ≠ 0 := by omega

/-- The dyadic geometric series `G_j = ∑_k z^(k·2^j)`. -/
def dyadicGeometricSeries (j : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => if 2 ^ j ∣ n then 1 else 0

/-- `G_j` inverts `1 - z^(2^j)`. -/
theorem one_sub_X_pow_mul_dyadicGeometric (j : ℕ) :
    (1 - PowerSeries.X ^ 2 ^ j) * dyadicGeometricSeries j = 1 := by
  have hexp : (1 - PowerSeries.X ^ 2 ^ j) * dyadicGeometricSeries j =
      dyadicGeometricSeries j -
        PowerSeries.X ^ 2 ^ j * dyadicGeometricSeries j := by
    ring
  rw [hexp]
  ext n
  rw [map_sub, PowerSeries.coeff_X_pow_mul', dyadicGeometricSeries,
    PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  have hpow : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [if_pos (dvd_zero _), if_neg (by omega), if_pos rfl]
    ring
  · rw [if_neg (show ¬ n = 0 by omega)]
    by_cases hdvd : 2 ^ j ∣ n
    · have hge : 2 ^ j ≤ n := Nat.le_of_dvd hn hdvd
      rw [if_pos hdvd, if_pos hge,
        if_pos (Nat.dvd_sub hdvd dvd_rfl)]
      ring
    · rw [if_neg hdvd]
      split_ifs with h1 h2
      · exfalso
        have := Nat.dvd_add h2 (dvd_refl (2 ^ j))
        rw [Nat.sub_add_cancel h1] at this
        exact hdvd this
      · ring
      · ring

/-- The Mahler substitution shifts the dyadic geometric series. -/
theorem expand_dyadicGeometric (j : ℕ) :
    PowerSeries.expand 2 two_ne (dyadicGeometricSeries j) =
      dyadicGeometricSeries (j + 1) := by
  ext n
  simp only [dyadicGeometricSeries, PowerSeries.coeff_expand,
    PowerSeries.coeff_mk]
  by_cases h2 : 2 ∣ n
  · rw [if_pos h2]
    by_cases hj : 2 ^ j ∣ n / 2
    · obtain ⟨k, hk⟩ := hj
      have hnk : n = 2 ^ (j + 1) * k := by
        have h1 : n = 2 * (n / 2) := by omega
        rw [h1, hk, pow_succ]
        ring
      rw [if_pos ⟨k, hk⟩, if_pos ⟨k, hnk⟩]
    · rw [if_neg hj, if_neg ?_]
      rintro ⟨k, hk⟩
      apply hj
      refine ⟨k, ?_⟩
      have : n = 2 * (2 ^ j * k) := by rw [hk, pow_succ]; ring
      omega
  · rw [if_neg h2, if_neg ?_]
    rintro ⟨k, hk⟩
    apply h2
    refine ⟨2 ^ j * k, ?_⟩
    rw [hk, pow_succ]
    ring

/-- The inhomogeneous Mahler equation of the bit series
(`eq:T-Mahler`): `T = (1-z)·T(z²) + z·G_1`. -/
theorem thueMorseBitZSeries_mahler :
    thueMorseBitZSeries =
      (1 - PowerSeries.X) *
          PowerSeries.expand 2 two_ne thueMorseBitZSeries +
        PowerSeries.X * dyadicGeometricSeries 1 := by
  have hexp : (1 - PowerSeries.X) *
      PowerSeries.expand 2 two_ne thueMorseBitZSeries +
      PowerSeries.X * dyadicGeometricSeries 1 =
      PowerSeries.expand 2 two_ne thueMorseBitZSeries -
        PowerSeries.X * PowerSeries.expand 2 two_ne thueMorseBitZSeries +
        PowerSeries.X * dyadicGeometricSeries 1 := by
    ring
  rw [hexp]
  ext n
  rw [map_add, map_sub]
  rcases n with _ | k
  · rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_X_mul]
    simp only [PowerSeries.coeff_expand, if_pos (show (2:ℕ) ∣ 0 by omega),
      thueMorseBitZSeries, PowerSeries.coeff_mk]
    norm_num
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul]
    simp only [PowerSeries.coeff_expand, thueMorseBitZSeries,
      dyadicGeometricSeries, PowerSeries.coeff_mk]
    rcases Nat.even_or_odd k with ⟨t, ht⟩ | ⟨t, ht⟩
    · -- `k = 2t`, so `k + 1` is odd
      subst ht
      rw [if_neg (by omega : ¬ 2 ∣ t + t + 1),
        if_pos (by omega : 2 ∣ t + t),
        if_pos (by omega : 2 ^ 1 ∣ t + t),
        show (t + t) / 2 = t by omega]
      have h1 : thueMorseBit (t + t + 1) = 1 - thueMorseBit t := by
        rw [thueMorseBit, thueMorseBit,
          show t + t + 1 = 2 * t + 1 by ring,
          binaryWeight_two_mul_add_one]
        omega
      have h2 := thueMorseBit_le_one t
      rw [h1]
      push_cast [Nat.cast_sub h2]
      ring
    · -- `k = 2t + 1`, so `k + 1 = 2(t+1)` is even
      subst ht
      rw [if_pos (by omega : 2 ∣ 2 * t + 1 + 1),
        if_neg (by omega : ¬ 2 ∣ 2 * t + 1),
        if_neg (by omega : ¬ 2 ^ 1 ∣ 2 * t + 1),
        show (2 * t + 1 + 1) / 2 = t + 1 by omega]
      have h1 : thueMorseBit (2 * t + 1 + 1) = thueMorseBit (t + 1) := by
        rw [thueMorseBit, thueMorseBit,
          show 2 * t + 1 + 1 = 2 * (t + 1) by ring,
          binaryWeight_two_mul]
      rw [h1]
      ring

private theorem iterate_expand_mul' (m : ℕ) (a b : PowerSeries ℤ) :
    (⇑(PowerSeries.expand 2 two_ne (R := ℤ)))^[m] (a * b) =
      (⇑(PowerSeries.expand 2 two_ne (R := ℤ)))^[m] a *
        (⇑(PowerSeries.expand 2 two_ne (R := ℤ)))^[m] b := by
  induction m generalizing a b with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply, map_mul, ih]

private theorem iterate_expand_add' (m : ℕ) (a b : PowerSeries ℤ) :
    (⇑(PowerSeries.expand 2 two_ne (R := ℤ)))^[m] (a + b) =
      (⇑(PowerSeries.expand 2 two_ne (R := ℤ)))^[m] a +
        (⇑(PowerSeries.expand 2 two_ne (R := ℤ)))^[m] b := by
  induction m generalizing a b with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply, map_add, ih]

private theorem iterate_expand_one_sub_X' (m : ℕ) :
    (⇑(PowerSeries.expand 2 two_ne (R := ℤ)))^[m] (1 - PowerSeries.X) =
      1 - PowerSeries.X ^ 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih, map_sub, map_one, map_pow,
        PowerSeries.expand_X, ← pow_mul,
        show 2 * 2 ^ m = 2 ^ (m + 1) by rw [pow_succ]; ring]

private theorem iterate_expand_X' (m : ℕ) :
    (⇑(PowerSeries.expand 2 two_ne (R := ℤ)))^[m] PowerSeries.X =
      PowerSeries.X ^ 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih, map_pow,
        PowerSeries.expand_X, ← pow_mul,
        show 2 * 2 ^ m = 2 ^ (m + 1) by rw [pow_succ]; ring]

private theorem iterate_expand_dyadic (m j : ℕ) :
    (⇑(PowerSeries.expand 2 two_ne (R := ℤ)))^[m]
        (dyadicGeometricSeries j) =
      dyadicGeometricSeries (j + m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih, expand_dyadicGeometric,
        show j + m + 1 = j + (m + 1) by ring]

/-- **The lacunary quotient expansion** (`thm:lacunary-quotient`),
exact finite form: for every level `M`,
`T = ∑_{j<M} P_j·z^(2^j)·G_(j+1) + P_M·T(z^(2^M))`. -/
theorem thueMorseBitZSeries_lacunary_quotient (M : ℕ) :
    thueMorseBitZSeries =
      (∑ j ∈ range M,
        (∏ h ∈ range j, (1 - PowerSeries.X ^ 2 ^ h)) *
          (PowerSeries.X ^ 2 ^ j * dyadicGeometricSeries (j + 1))) +
      (∏ h ∈ range M, (1 - PowerSeries.X ^ 2 ^ h)) *
        (⇑(PowerSeries.expand 2 two_ne (R := ℤ)))^[M]
          thueMorseBitZSeries := by
  induction M with
  | zero => simp
  | succ M ih =>
      -- expand the tail one more level
      have hstep : (⇑(PowerSeries.expand 2 two_ne (R := ℤ)))^[M]
          thueMorseBitZSeries =
          (1 - PowerSeries.X ^ 2 ^ M) *
            (⇑(PowerSeries.expand 2 two_ne (R := ℤ)))^[M + 1]
              thueMorseBitZSeries +
          PowerSeries.X ^ 2 ^ M * dyadicGeometricSeries (M + 1) := by
        conv_lhs => rw [show thueMorseBitZSeries =
          (1 - PowerSeries.X) *
              PowerSeries.expand 2 two_ne thueMorseBitZSeries +
            PowerSeries.X * dyadicGeometricSeries 1 from
          thueMorseBitZSeries_mahler]
        rw [iterate_expand_add', iterate_expand_mul', iterate_expand_mul',
          iterate_expand_one_sub_X', iterate_expand_X',
          iterate_expand_dyadic, show (1 : ℕ) + M = M + 1 by ring,
          ← Function.iterate_succ_apply]
      conv_lhs => rw [ih, hstep]
      rw [Finset.sum_range_succ, Finset.prod_range_succ]
      ring

end Fabius
