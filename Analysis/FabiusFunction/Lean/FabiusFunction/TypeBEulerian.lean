import FabiusFunction.EulerianGeneratingFunctions

/-!
# Type-B Eulerian numbers

The type-B Eulerian numbers `B(n,k)` are defined by the insertion recurrence

`B(n+1,k+1) = (2k+3) B(n,k+1) + (2n-2k+1) B(n,k)`, `B(n+1,0) = B(n,0)`, `B(0,0) = 1`.

We prove the type-B Worpitzky identity `(2m+1)^n = ∑_k B(n,k) C(m+n-k, n)`, the
rational generating function `∑_m (2m+1)^n t^m = B_n(t)/(1-t)^{n+1}` with
`B_n(t) = ∑_k B(n,k) t^k`, and the explicit formula
`B(n,k) = ∑_{j ≤ k} (-1)^j C(n+1,j) (2(k-j)+1)^n`.

## Main results

* `typeBEulerian`, `typeBEulerian_succ_succ`, `typeBEulerian_zero_right`,
  `typeBEulerian_eq_zero_of_lt`.
* `two_mul_add_one_mul_choose`, `typeB_worpitzky`.
* `oddPowSeries`, `one_sub_X_pow_mul_oddPowSeries`, `typeBEulerian_eq_sum_int`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

/-- The type-B Eulerian numbers, by the insertion recurrence. -/
def typeBEulerian : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, 0 => typeBEulerian n 0
  | n + 1, k + 1 => (2 * k + 3) * typeBEulerian n (k + 1) + (2 * n - 2 * k + 1) * typeBEulerian n k

@[simp] theorem typeBEulerian_zero_zero : typeBEulerian 0 0 = 1 := rfl

@[simp] theorem typeBEulerian_zero_succ (k : ℕ) : typeBEulerian 0 (k + 1) = 0 := rfl

theorem typeBEulerian_succ_zero (n : ℕ) : typeBEulerian (n + 1) 0 = typeBEulerian n 0 := rfl

/-- The recurrence `B(n+1,k+1) = (2k+3) B(n,k+1) + (2n-2k+1) B(n,k)`. -/
theorem typeBEulerian_succ_succ (n k : ℕ) :
    typeBEulerian (n + 1) (k + 1) =
      (2 * k + 3) * typeBEulerian n (k + 1) + (2 * n - 2 * k + 1) * typeBEulerian n k := rfl

/-- `B(n,0) = 1`. -/
@[simp] theorem typeBEulerian_zero_right (n : ℕ) : typeBEulerian n 0 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [typeBEulerian_succ_zero, ih]

/-- `B(n,k) = 0` for `n < k`. -/
theorem typeBEulerian_eq_zero_of_lt : ∀ {n k : ℕ}, n < k → typeBEulerian n k = 0
  | 0, 0, h => absurd h (by omega)
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => absurd h (by omega)
  | n + 1, k + 1, h => by
    rw [typeBEulerian_succ_succ, typeBEulerian_eq_zero_of_lt (by omega : n < k + 1),
      typeBEulerian_eq_zero_of_lt (by omega : n < k), mul_zero, mul_zero, add_zero]

/-- The one-step relation behind the type-B Worpitzky identity:
`(2m+1) C(m+n-k, n) = (2k+1) C(m+n+1-k, n+1) + (2n-2k+1) C(m+n-k, n+1)` for `k ≤ n`. -/
theorem two_mul_add_one_mul_choose (m n k : ℕ) (hk : k ≤ n) :
    (2 * m + 1) * (m + n - k).choose n =
      (2 * k + 1) * (m + n + 1 - k).choose (n + 1) + (2 * n - 2 * k + 1) * (m + n - k).choose (n + 1) := by
  rcases Nat.lt_or_ge m k with hmk | hmk
  · rw [Nat.choose_eq_zero_of_lt (show m + n - k < n by omega),
      Nat.choose_eq_zero_of_lt (show m + n + 1 - k < n + 1 by omega),
      Nat.choose_eq_zero_of_lt (show m + n - k < n + 1 by omega)]
    simp
  · have hc1 := Nat.choose_succ_right_eq (m + n - k) n
    have hc2 := Nat.choose_succ_succ' (m + n - k) n
    rw [show m + n + 1 - k = m + n - k + 1 by omega, hc2]
    rw [show m + n - k - n = m - k by omega] at hc1
    have h2k : 2 * k ≤ 2 * n := by omega
    zify [hk, hmk, h2k] at hc1 ⊢
    linear_combination (-2 : ℤ) * hc1

/-- **The type-B Worpitzky identity:** `(2m+1)^n = ∑_{k ≤ n} B(n,k) C(m+n-k, n)`. -/
theorem typeB_worpitzky (n m : ℕ) :
    (2 * m + 1) ^ n = ∑ k ∈ Finset.range (n + 1), typeBEulerian n k * (m + n - k).choose n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : (2 * m + 1) ^ (n + 1) = ∑ k ∈ Finset.range (n + 1), typeBEulerian n k *
        ((2 * k + 1) * (m + n + 1 - k).choose (n + 1) +
          (2 * n - 2 * k + 1) * (m + n - k).choose (n + 1)) := by
      rw [pow_succ, ih, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [mul_assoc, mul_comm ((m + n - k).choose n), two_mul_add_one_mul_choose m n k hkn]
    have e1 : ∀ k, m + (n + 1) - (k + 1) = m + n - k := fun k => by omega
    have e2 : ∀ k, m + n + 1 - (k + 1) = m + n - k := fun k => by omega
    have e3 : m + (n + 1) - 0 = m + n + 1 := by omega
    have e4 : m + n + 1 - 0 = m + n + 1 := by omega
    have key : ∑ k ∈ Finset.range (n + 1),
        (2 * k + 1) * typeBEulerian n k * (m + n + 1 - k).choose (n + 1)
        = ∑ k ∈ Finset.range (n + 1),
            (2 * k + 3) * typeBEulerian n (k + 1) * (m + n - k).choose (n + 1)
          + (m + n + 1).choose (n + 1) := by
      rw [Finset.sum_range_succ'
          (fun k => (2 * k + 1) * typeBEulerian n k * (m + n + 1 - k).choose (n + 1)) n,
        Finset.sum_range_succ
          (fun k => (2 * k + 3) * typeBEulerian n (k + 1) * (m + n - k).choose (n + 1)) n,
        typeBEulerian_eq_zero_of_lt (Nat.lt_succ_self n)]
      simp only [mul_zero, zero_mul, add_zero, Nat.zero_add, Nat.mul_one, Nat.one_mul,
        typeBEulerian_zero_right, e2, e4]
      simp only [show ∀ x : ℕ, 2 * (x + 1) + 1 = 2 * x + 3 from fun x => by ring]
    rw [hstep, Finset.sum_range_succ'
      (fun k => typeBEulerian (n + 1) k * (m + (n + 1) - k).choose (n + 1)) (n + 1)]
    simp only [typeBEulerian_succ_succ, typeBEulerian_succ_zero, typeBEulerian_zero_right, e1, e3,
      Nat.one_mul]
    calc ∑ k ∈ Finset.range (n + 1), typeBEulerian n k *
          ((2 * k + 1) * (m + n + 1 - k).choose (n + 1) +
            (2 * n - 2 * k + 1) * (m + n - k).choose (n + 1))
        = ∑ k ∈ Finset.range (n + 1), (2 * k + 1) * typeBEulerian n k * (m + n + 1 - k).choose (n + 1)
          + ∑ k ∈ Finset.range (n + 1),
              (2 * n - 2 * k + 1) * typeBEulerian n k * (m + n - k).choose (n + 1) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ = (∑ k ∈ Finset.range (n + 1),
              (2 * k + 3) * typeBEulerian n (k + 1) * (m + n - k).choose (n + 1)
            + (m + n + 1).choose (n + 1))
          + ∑ k ∈ Finset.range (n + 1),
              (2 * n - 2 * k + 1) * typeBEulerian n k * (m + n - k).choose (n + 1) := by rw [key]
      _ = ∑ k ∈ Finset.range (n + 1),
            ((2 * k + 3) * typeBEulerian n (k + 1) + (2 * n - 2 * k + 1) * typeBEulerian n k) *
              (m + n - k).choose (n + 1) + (m + n + 1).choose (n + 1) := by
          rw [Finset.sum_congr rfl (fun k _ => add_mul ((2 * k + 3) * typeBEulerian n (k + 1))
            ((2 * n - 2 * k + 1) * typeBEulerian n k) ((m + n - k).choose (n + 1))),
            Finset.sum_add_distrib]
          ring

/-- The series `∑_m (2m+1)^n X^m`. -/
noncomputable def oddPowSeries (R : Type*) [CommRing R] (n : ℕ) : R⟦X⟧ :=
  PowerSeries.mk fun m => (2 * (m : R) + 1) ^ n

section

variable (R : Type*) [CommRing R]

/-- The type-B Worpitzky identity read column by column. -/
theorem oddPowSeries_eq (n : ℕ) :
    oddPowSeries R n = ∑ k ∈ Finset.range (n + 1),
      PowerSeries.C (typeBEulerian n k : R) * (X ^ k * PowerSeries.mk 1 ^ (n + 1)) := by
  ext m
  rw [oddPowSeries, coeff_mk, map_sum]
  have hw : (2 * (m : R) + 1) ^ n = ∑ k ∈ Finset.range (n + 1),
      (typeBEulerian n k : R) * ((m + n - k).choose n : R) := by
    have h := congrArg (Nat.cast : ℕ → R) (typeB_worpitzky n m)
    push_cast at h
    exact h
  rw [hw]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [coeff_C_mul, coeff_X_pow_mul', mk_one_pow_eq_mk_choose_add, coeff_mk]
  split_ifs with h
  · have hidx : m + n - k = n + (m - k) := by omega
    rw [hidx]
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]

/-- **The rational generating function of the type-B Eulerian polynomials:**
`(1 - X)^{n+1} · ∑_m (2m+1)^n X^m = ∑_{k ≤ n} B(n,k) X^k`. -/
theorem one_sub_X_pow_mul_oddPowSeries (n : ℕ) :
    (1 - X) ^ (n + 1) * oddPowSeries R n =
      ∑ k ∈ Finset.range (n + 1), (typeBEulerian n k : R⟦X⟧) * X ^ k := by
  rw [oddPowSeries_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hunit : ((1 : R⟦X⟧) - X) ^ (n + 1) * PowerSeries.mk 1 ^ (n + 1) = 1 := by
    rw [← mul_pow, mul_comm, mk_one_mul_one_sub_eq_one, one_pow]
  rw [← map_natCast (PowerSeries.C : R →+* R⟦X⟧)]
  calc (1 - X) ^ (n + 1) * (PowerSeries.C (typeBEulerian n k : R) * (X ^ k * PowerSeries.mk 1 ^ (n + 1)))
      = PowerSeries.C (typeBEulerian n k : R) * X ^ k *
          ((1 - X) ^ (n + 1) * PowerSeries.mk 1 ^ (n + 1)) := by ring
    _ = _ := by rw [hunit, mul_one]

end

/-- **The explicit formula for the type-B Eulerian numbers:**
`B(n,k) = ∑_{j ≤ k} (-1)^j C(n+1, j) (2(k-j)+1)^n`. -/
theorem typeBEulerian_eq_sum_int (n k : ℕ) :
    (typeBEulerian n k : ℤ) = ∑ j ∈ Finset.range (k + 1),
      (-1 : ℤ) ^ j * (n + 1).choose j * (2 * ((k - j : ℕ) : ℤ) + 1) ^ n := by
  have h := congrArg (PowerSeries.coeff k) (one_sub_X_pow_mul_oddPowSeries ℤ n)
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, map_sum] at h
  have hR : ∑ i ∈ Finset.range (n + 1),
      PowerSeries.coeff k ((typeBEulerian n i : ℤ⟦X⟧) * X ^ i) = (typeBEulerian n k : ℤ) := by
    have hc : ∀ i, PowerSeries.coeff k ((typeBEulerian n i : ℤ⟦X⟧) * X ^ i)
        = if k = i then (typeBEulerian n i : ℤ) else 0 := by
      intro i
      rw [← map_natCast (PowerSeries.C : ℤ →+* ℤ⟦X⟧), PowerSeries.coeff_C_mul_X_pow]
    simp only [hc, Finset.sum_ite_eq, Finset.mem_range]
    split_ifs with hk
    · rfl
    · rw [typeBEulerian_eq_zero_of_lt (by omega), Nat.cast_zero]
  rw [hR] at h
  simp only [coeff_one_sub_X_pow, oddPowSeries, coeff_mk] at h
  rw [← h]

end Fabius
