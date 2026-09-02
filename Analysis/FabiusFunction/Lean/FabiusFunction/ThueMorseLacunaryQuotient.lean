import FabiusFunction.ThueMorseMahler
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# The lacunary quotient expansion of the bit series

Iterating the inhomogeneous Mahler equation of the zero–one series
`T(z) = ∑ τ(n)zⁿ` produces the atlas's lacunary quotient expansion.
We prove the exact finite-level identity in `ℤ⟦z⟧`, with each
"quotient" `z^(2^j)/(1-z^(2^(j+1)))` realized as an honest power
series — the dyadic geometric series — so no denominators ever occur:

`T = ∑_{j<M} P_j·z^(2^j)·G_(j+1) + P_M·T(z^(2^M))`.

* `dyadicGeometricSeries j` — `G_j = ∑_k z^(k·2^j)`, the period-`2^j`
  case of `geometricSeriesOfPeriod` from `ThueMorseMahler`, hence the
  inverse of `1 - z^(2^j)` (`one_sub_X_pow_mul_dyadicGeometric`).
* `dyadicGeometricSeries_eq_expand` — `G_j` is the substitution
  `z ↦ z^(2^j)` applied to the plain geometric series `∑_k z^k`.  The
  shift `G_j ↦ G_(j+1)` (`expand_dyadicGeometric`) is read off from
  this together with Mathlib's `PowerSeries.expand_mul`.
* `thueMorseBitZSeries_mahler` — the inhomogeneous Mahler equation
  `T = (1-z)·T(z²) + z·G_1` (`eq:T-Mahler`).
* `thueMorseBitZSeries_lacunary_quotient` — the level-`M` expansion
  (`thm:lacunary-quotient`, exact finite form).

The substitution bookkeeping — `two_ne_zero_nat`, `iterate_expand_mul`,
`iterate_expand_X` and `iterate_expand_one_sub_X` — is imported from
`ThueMorseMahler` rather than duplicated here; additivity of the
iterates is Mathlib's `iterate_map_add`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- The dyadic geometric series `G_j = ∑_k z^(k·2^j)`: the geometric
series of period `2^j` over `ℤ`. -/
noncomputable def dyadicGeometricSeries (j : ℕ) : PowerSeries ℤ :=
  geometricSeriesOfPeriod ℤ (2 ^ j)

/-- The coefficient description of `G_j`: the coefficient at `n` is `1`
exactly when `2^j ∣ n`. -/
theorem dyadicGeometricSeries_eq (j : ℕ) :
    dyadicGeometricSeries j =
      PowerSeries.mk fun n => if 2 ^ j ∣ n then 1 else 0 :=
  rfl

/-- The side condition of the substitution `z ↦ z^(2^j)`. -/
private theorem two_pow_ne_zero' (j : ℕ) : (2 : ℕ) ^ j ≠ 0 := by
  have h : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  omega

/-- Two substitutions `PowerSeries.expand` whose exponents are equal —
but not syntactically identical — agree. -/
private theorem expand_exp_congr {p q : ℕ} (hpq : p = q) (hp : p ≠ 0)
    (hq : q ≠ 0) (φ : PowerSeries ℤ) :
    PowerSeries.expand p hp φ = PowerSeries.expand q hq φ := by
  subst hpq
  rfl

/-- `G_j` is the substitution `z ↦ z^(2^j)` applied to the plain
geometric series `∑_k z^k`. -/
theorem dyadicGeometricSeries_eq_expand (j : ℕ) (hj : (2 : ℕ) ^ j ≠ 0) :
    dyadicGeometricSeries j =
      PowerSeries.expand (2 ^ j) hj (PowerSeries.mk fun _ => (1 : ℤ)) :=
  geometricSeriesOfPeriod_eq_expand (2 ^ j) hj

/-- `G_j` inverts `1 - z^(2^j)`. -/
theorem one_sub_X_pow_mul_dyadicGeometric (j : ℕ) :
    (1 - PowerSeries.X ^ 2 ^ j) * dyadicGeometricSeries j = 1 :=
  one_sub_X_pow_mul_geometricSeriesOfPeriod (R := ℤ) (2 ^ j)
    (two_pow_ne_zero' j)

/-- The Mahler substitution shifts the dyadic geometric series. -/
theorem expand_dyadicGeometric (j : ℕ) :
    PowerSeries.expand 2 two_ne_zero_nat (dyadicGeometricSeries j) =
      dyadicGeometricSeries (j + 1) := by
  have hpow : (2 : ℕ) * 2 ^ j = 2 ^ (j + 1) := by rw [pow_succ]; ring
  rw [dyadicGeometricSeries_eq_expand j (two_pow_ne_zero' j),
    dyadicGeometricSeries_eq_expand (j + 1) (two_pow_ne_zero' (j + 1)),
    ← PowerSeries.expand_mul 2 two_ne_zero_nat (2 ^ j)
      (two_pow_ne_zero' j) (PowerSeries.mk fun _ => (1 : ℤ))]
  exact expand_exp_congr hpow _ _ _

/-- The inhomogeneous Mahler equation of the bit series
(`eq:T-Mahler`): `T = (1-z)·T(z²) + z·G_1`. -/
theorem thueMorseBitZSeries_mahler :
    thueMorseBitZSeries =
      (1 - PowerSeries.X) *
          PowerSeries.expand 2 two_ne_zero_nat thueMorseBitZSeries +
        PowerSeries.X * dyadicGeometricSeries 1 := by
  have hexp : (1 - PowerSeries.X) *
      PowerSeries.expand 2 two_ne_zero_nat thueMorseBitZSeries +
      PowerSeries.X * dyadicGeometricSeries 1 =
      PowerSeries.expand 2 two_ne_zero_nat thueMorseBitZSeries -
        PowerSeries.X *
          PowerSeries.expand 2 two_ne_zero_nat thueMorseBitZSeries +
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
      dyadicGeometricSeries_eq, PowerSeries.coeff_mk]
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

private theorem iterate_expand_dyadic (m j : ℕ) :
    (⇑(PowerSeries.expand 2 two_ne_zero_nat (R := ℤ)))^[m]
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
        (⇑(PowerSeries.expand 2 two_ne_zero_nat (R := ℤ)))^[M]
          thueMorseBitZSeries := by
  induction M with
  | zero => simp
  | succ M ih =>
      -- expand the tail one more level
      have hstep :
          (⇑(PowerSeries.expand 2 two_ne_zero_nat (R := ℤ)))^[M]
            thueMorseBitZSeries =
          (1 - PowerSeries.X ^ 2 ^ M) *
            (⇑(PowerSeries.expand 2 two_ne_zero_nat (R := ℤ)))^[M + 1]
              thueMorseBitZSeries +
          PowerSeries.X ^ 2 ^ M * dyadicGeometricSeries (M + 1) := by
        conv_lhs => rw [show thueMorseBitZSeries =
          (1 - PowerSeries.X) *
              PowerSeries.expand 2 two_ne_zero_nat thueMorseBitZSeries +
            PowerSeries.X * dyadicGeometricSeries 1 from
          thueMorseBitZSeries_mahler]
        rw [iterate_map_add
            (PowerSeries.expand 2 two_ne_zero_nat (R := ℤ)),
          iterate_expand_mul, iterate_expand_mul,
          iterate_expand_one_sub_X, iterate_expand_X,
          iterate_expand_dyadic, show (1 : ℕ) + M = M + 1 by ring,
          ← Function.iterate_succ_apply]
      conv_lhs => rw [ih, hstep]
      rw [Finset.sum_range_succ, Finset.prod_range_succ]
      ring

end Fabius
