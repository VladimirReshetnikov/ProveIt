import Mathlib.RingTheory.PowerSeries.WellKnown
import FabiusFunction.EulerianNumbers

/-!
# Eulerian numbers: symmetry, the rational generating function, and the explicit formula

Three classical facts about the Eulerian numbers `A(n,k)` (defined in
`FabiusFunction.EulerianNumbers` by the insertion recurrence):

* **symmetry** `A(n,k) = A(n, n-1-k)` for `k < n`;
* the **rational generating function**
  `∑_{m ≥ 0} (m+1)^n t^m = A_n(t) / (1-t)^{n+1}`, stated in `R⟦X⟧` as
  `(1 - X)^{n+1} · ∑_m (m+1)^n X^m = ∑_k A(n,k) X^k`;
* the **explicit formula**
  `A(n,k) = ∑_{j ≤ k} (-1)^j C(n+1, j) (k+1-j)^n`.

The generating function is Worpitzky's identity `(m+1)^n = ∑_k A(n,k) C(m+1+k, n)`
read column by column with `∑_m C(m + d, d) X^m = (1 - X)^{-(d+1)}`
(Mathlib's `PowerSeries.mk_one_pow_eq_mk_choose_add`); the explicit formula is
its `k`-th coefficient, and symmetry is what turns the Worpitzky exponent
`n-1-k` into `k`.

## Main results

* `eulerianNumber_succ_self_left`, `eulerianNumber_symm`.
* `succPowSeries`, `coeff_one_sub_X_pow`, `succPowSeries_succ_eq`.
* `one_sub_X_pow_mul_succPowSeries`: the rational generating function.
* `eulerianNumber_eq_sum_int`: the explicit formula; `eulerianNumber_one_right`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

/-! ### Symmetry -/

/-- The last nonzero entry of every row is one: `A(n+1, n) = 1`. -/
theorem eulerianNumber_succ_self_left (n : ℕ) : eulerianNumber (n + 1) n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [eulerianNumber_succ_succ, eulerianNumber_eq_zero_of_le (by omega) le_rfl, mul_zero,
      zero_add, Nat.add_sub_cancel_left, one_mul, ih]

/-- **Symmetry of the Eulerian numbers:** `A(n,k) = A(n, n-1-k)` for `k < n`
(complementation of permutations exchanges descents and ascents). -/
theorem eulerianNumber_symm (n k : ℕ) (hk : k + 1 ≤ n) :
    eulerianNumber n k = eulerianNumber n (n - 1 - k) := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
    rw [Nat.add_sub_cancel]
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · rw [Nat.sub_zero, eulerianNumber_zero_right, eulerianNumber_succ_self_left]
    rcases Nat.lt_or_ge k n with hkn | hkn
    · -- `0 < k < n`: write `k = j + 1` and `n = j + i + 2`
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      obtain ⟨i, rfl⟩ : ∃ i, n = j + i + 2 := ⟨n - j - 2, by omega⟩
      have h1 := ih (j + 1) (by omega)
      have h2 := ih j (by omega)
      rw [show j + i + 2 - 1 - (j + 1) = i by omega] at h1
      rw [show j + i + 2 - 1 - j = i + 1 by omega] at h2
      rw [show j + i + 2 - (j + 1) = i + 1 by omega, eulerianNumber_succ_succ (j + i + 2) j,
        eulerianNumber_succ_succ (j + i + 2) i, h1, h2, show j + i + 2 - j = i + 2 by omega,
        show j + i + 2 - i = j + 2 by omega]
      ring
    · -- `k = n`: both sides are one
      have hkn' : k = n := by omega
      subst hkn'
      rw [Nat.sub_self, eulerianNumber_zero_right, eulerianNumber_succ_self_left]

/-! ### The rational generating function -/

variable (R : Type*) [CommRing R]

/-- The series `∑_{m ≥ 0} (m+1)^n X^m`. -/
noncomputable def succPowSeries (n : ℕ) : R⟦X⟧ :=
  PowerSeries.mk fun m => ((m : R) + 1) ^ n

/-- The coefficients of `(1 - X)^N` are the signed binomial coefficients. -/
theorem coeff_one_sub_X_pow (N i : ℕ) :
    PowerSeries.coeff i ((1 - X : R⟦X⟧) ^ N) = (-1) ^ i * (N.choose i : R) := by
  have h : (1 - X : R⟦X⟧) ^ N = ∑ m ∈ Finset.range (N + 1),
      PowerSeries.C ((-1) ^ m * (N.choose m : R)) * X ^ m := by
    rw [sub_eq_add_neg, add_comm, add_pow]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [neg_pow, one_pow, mul_one, map_mul, map_pow, map_neg, map_one,
      map_natCast (PowerSeries.C : R →+* R⟦X⟧)]
    ring
  rw [h, map_sum]
  simp only [PowerSeries.coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range]
  split_ifs with hi
  · rfl
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]

/-- Worpitzky's identity read column by column:
`∑_m (m+1)^{n+1} X^m = ∑_{k ≤ n} A(n+1,k) X^{n-k} (1 - X)^{-(n+2)}`. -/
theorem succPowSeries_succ_eq (n : ℕ) :
    succPowSeries R (n + 1) = ∑ k ∈ Finset.range (n + 1),
      PowerSeries.C (eulerianNumber (n + 1) k : R) *
        (X ^ (n - k) * PowerSeries.mk 1 ^ (n + 1 + 1)) := by
  ext m
  rw [succPowSeries, coeff_mk, map_sum]
  have hw := worpitzky_nat (n + 1) (m + 1)
  rw [Finset.sum_range_succ, eulerianNumber_eq_zero_of_le (by omega) le_rfl, zero_mul,
    add_zero] at hw
  have hw' : ((m : R) + 1) ^ (n + 1) = ∑ k ∈ Finset.range (n + 1),
      (eulerianNumber (n + 1) k : R) * ((m + 1 + k).choose (n + 1) : R) := by
    have hc := congrArg (Nat.cast : ℕ → R) hw
    push_cast at hc
    exact hc
  rw [hw']
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [coeff_C_mul, coeff_X_pow_mul', mk_one_pow_eq_mk_choose_add, coeff_mk]
  split_ifs with h
  · have hidx : m + 1 + k = n + 1 + (m - (n - k)) := by omega
    rw [hidx]
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]

/-- **The rational generating function of the Eulerian polynomials:**
`(1 - X)^{n+1} · ∑_{m ≥ 0} (m+1)^n X^m = ∑_{k ≤ n} A(n,k) X^k`, i.e.
`∑_m (m+1)^n t^m = A_n(t)/(1-t)^{n+1}`. -/
theorem one_sub_X_pow_mul_succPowSeries (n : ℕ) :
    (1 - X) ^ (n + 1) * succPowSeries R n =
      ∑ k ∈ Finset.range (n + 1), (eulerianNumber n k : R⟦X⟧) * X ^ k := by
  cases n with
  | zero =>
    have h : succPowSeries R 0 = PowerSeries.mk 1 := by
      ext m
      simp [succPowSeries]
    rw [h, pow_one, mul_comm, mk_one_mul_one_sub_eq_one]
    simp
  | succ n =>
    rw [succPowSeries_succ_eq, Finset.mul_sum]
    have hunit : ((1 : R⟦X⟧) - X) ^ (n + 1 + 1) * PowerSeries.mk 1 ^ (n + 1 + 1) = 1 := by
      rw [← mul_pow, mul_comm, mk_one_mul_one_sub_eq_one, one_pow]
    have hterm : ∀ k ∈ Finset.range (n + 1),
        (1 - X) ^ (n + 1 + 1) * (PowerSeries.C (eulerianNumber (n + 1) k : R) *
            (X ^ (n - k) * PowerSeries.mk 1 ^ (n + 1 + 1)))
          = (eulerianNumber (n + 1) (n - k) : R⟦X⟧) * X ^ (n - k) := by
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [eulerianNumber_symm (n + 1) k (by omega), show n + 1 - 1 - k = n - k by omega,
        ← map_natCast (PowerSeries.C : R →+* R⟦X⟧)]
      calc (1 - X) ^ (n + 1 + 1) * (PowerSeries.C (eulerianNumber (n + 1) (n - k) : R) *
            (X ^ (n - k) * PowerSeries.mk 1 ^ (n + 1 + 1)))
          = PowerSeries.C (eulerianNumber (n + 1) (n - k) : R) * X ^ (n - k) *
            ((1 - X) ^ (n + 1 + 1) * PowerSeries.mk 1 ^ (n + 1 + 1)) := by ring
        _ = _ := by rw [hunit, mul_one]
    rw [Finset.sum_congr rfl hterm]
    have hr := Finset.sum_range_reflect (fun k => (eulerianNumber (n + 1) k : R⟦X⟧) * X ^ k) (n + 1)
    simp only [Nat.add_sub_cancel] at hr
    rw [Finset.sum_range_succ (fun k => (eulerianNumber (n + 1) k : R⟦X⟧) * X ^ k) (n + 1),
      eulerianNumber_eq_zero_of_le (by omega) le_rfl, Nat.cast_zero, zero_mul, add_zero]
    exact hr

/-! ### The explicit formula -/

/-- **The explicit formula for the Eulerian numbers:**
`A(n,k) = ∑_{j ≤ k} (-1)^j C(n+1, j) (k+1-j)^n`. -/
theorem eulerianNumber_eq_sum_int (n k : ℕ) :
    (eulerianNumber n k : ℤ) = ∑ j ∈ Finset.range (k + 1),
      (-1 : ℤ) ^ j * (n + 1).choose j * ((k + 1 - j : ℕ) : ℤ) ^ n := by
  have h := congrArg (PowerSeries.coeff k) (one_sub_X_pow_mul_succPowSeries ℤ n)
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, map_sum] at h
  have hR : ∑ i ∈ Finset.range (n + 1),
      PowerSeries.coeff k ((eulerianNumber n i : ℤ⟦X⟧) * X ^ i) = (eulerianNumber n k : ℤ) := by
    have hc : ∀ i, PowerSeries.coeff k ((eulerianNumber n i : ℤ⟦X⟧) * X ^ i)
        = if k = i then (eulerianNumber n i : ℤ) else 0 := by
      intro i
      rw [← map_natCast (PowerSeries.C : ℤ →+* ℤ⟦X⟧), PowerSeries.coeff_C_mul_X_pow]
    simp only [hc, Finset.sum_ite_eq, Finset.mem_range]
    split_ifs with hk
    · rfl
    · symm
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        simp
      · exact_mod_cast eulerianNumber_eq_zero_of_le hn (by omega)
  rw [hR] at h
  simp only [coeff_one_sub_X_pow, succPowSeries, coeff_mk] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [show k + 1 - j = (k - j) + 1 by omega]
  push_cast
  ring

/-- `A(n,1) = 2^n - (n+1)`. -/
theorem eulerianNumber_one_right (n : ℕ) : (eulerianNumber n 1 : ℤ) = 2 ^ n - (n + 1) := by
  rw [eulerianNumber_eq_sum_int]
  simp [Finset.sum_range_succ]
  ring

end Fabius
