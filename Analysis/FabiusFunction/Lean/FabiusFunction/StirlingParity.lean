import FabiusFunction.StirlingOrdinaryGF
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Data.ZMod.Basic

/-!
# Parity of the Stirling numbers of the second kind

Reducing the column generating function `∑_r S(k+r,k) t^r = ∏_{j=1}^{k} (1 - j t)^{-1}` modulo `2`
kills the even factors and leaves `(1 - t)^{-⌈k/2⌉}`, whose coefficients are binomial
coefficients.  Hence, for `1 ≤ k ≤ n`,

`S(n,k) ≡ C(n - ⌈(k+1)/2⌉, ⌊(k-1)/2⌋)  (mod 2)`.

## Main results

* `prod_one_sub_mul_X_zmod_two`, `stirlingColumnOGF_zmod_two`.
* `stirlingSecond_add_zmod_two`, `stirlingSecond_modEq_choose_two`.
-/

set_option autoImplicit false

open PowerSeries Finset

namespace Fabius

/-- Over `𝔽₂`, `∏_{j<k} (1 - (j+1) t) = (1 - t)^{(k+1)/2}`: only the odd factors survive. -/
theorem prod_one_sub_mul_X_zmod_two (k : ℕ) :
    (∏ j ∈ range k, (1 - ((j + 1 : ℕ) : (ZMod 2)⟦X⟧) * X)) = (1 - X) ^ ((k + 1) / 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, ih]
    rcases Nat.even_or_odd (k + 1) with he | ho
    · have h0 : ((k + 1 : ℕ) : (ZMod 2)⟦X⟧) = 0 := by
        rw [← map_natCast (PowerSeries.C : ZMod 2 →+* (ZMod 2)⟦X⟧) (k + 1),
          ZMod.natCast_eq_zero_iff_even.mpr he, map_zero]
      rw [h0, zero_mul, sub_zero, mul_one]
      obtain ⟨r, hr⟩ := he
      congr 1
      omega
    · have h1 : ((k + 1 : ℕ) : (ZMod 2)⟦X⟧) = 1 := by
        rw [← map_natCast (PowerSeries.C : ZMod 2 →+* (ZMod 2)⟦X⟧) (k + 1),
          ZMod.natCast_eq_one_iff_odd.mpr ho, map_one]
      rw [h1, one_mul, ← pow_succ]
      obtain ⟨r, hr⟩ := ho
      congr 1
      omega

/-- Over `𝔽₂` the column series is `(1 - t)^{-(k+1)/2}`. -/
theorem stirlingColumnOGF_zmod_two (k : ℕ) :
    stirlingColumnOGF (ZMod 2) k = (PowerSeries.mk 1) ^ ((k + 1) / 2) := by
  have h1 := prod_one_sub_mul_X_mul_stirlingColumnOGF (ZMod 2) k
  rw [prod_one_sub_mul_X_zmod_two] at h1
  have h2 : (PowerSeries.mk 1 : (ZMod 2)⟦X⟧) ^ ((k + 1) / 2) * (1 - X) ^ ((k + 1) / 2) = 1 := by
    rw [← mul_pow, mk_one_mul_one_sub_eq_one, one_pow]
  calc stirlingColumnOGF (ZMod 2) k
      = (PowerSeries.mk 1 ^ ((k + 1) / 2) * (1 - X) ^ ((k + 1) / 2)) *
          stirlingColumnOGF (ZMod 2) k := by rw [h2, one_mul]
    _ = PowerSeries.mk 1 ^ ((k + 1) / 2) *
          ((1 - X) ^ ((k + 1) / 2) * stirlingColumnOGF (ZMod 2) k) := by rw [mul_assoc]
    _ = PowerSeries.mk 1 ^ ((k + 1) / 2) := by rw [h1, mul_one]

/-- **Parity of `S(n,k)`, column form:** for `k ≥ 1`,
`S(k + r, k) ≡ C((k-1)/2 + r, (k-1)/2) (mod 2)`. -/
theorem stirlingSecond_add_zmod_two (k r : ℕ) (hk : 1 ≤ k) :
    ((Nat.stirlingSecond (k + r) k : ℕ) : ZMod 2) =
      (((k - 1) / 2 + r).choose ((k - 1) / 2) : ZMod 2) := by
  have h := congrArg (PowerSeries.coeff r) (stirlingColumnOGF_zmod_two k)
  rw [coeff_stirlingColumnOGF, show (k + 1) / 2 = (k - 1) / 2 + 1 by omega,
    mk_one_pow_eq_mk_choose_add, coeff_mk] at h
  exact h

/-- **Parity criterion:** for `1 ≤ k ≤ n`,
`S(n,k) ≡ C(n - ⌈(k+1)/2⌉, ⌊(k-1)/2⌋) (mod 2)`, with `⌈(k+1)/2⌉ = (k+2)/2`. -/
theorem stirlingSecond_modEq_choose_two {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    Nat.stirlingSecond n k ≡ (n - (k + 2) / 2).choose ((k - 1) / 2) [MOD 2] := by
  obtain ⟨r, rfl⟩ : ∃ r, n = k + r := ⟨n - k, by omega⟩
  rw [← ZMod.natCast_eq_natCast_iff, stirlingSecond_add_zmod_two k r hk,
    show k + r - (k + 2) / 2 = (k - 1) / 2 + r by omega]

end Fabius
