import FabiusFunction.StirlingOrdinaryGF
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Second-order Eulerian numbers

The second-order Eulerian numbers `⟪n,k⟫` are defined by the insertion recurrence

`⟪n+1,k+1⟫ = (2n-k) ⟪n,k⟫ + (k+2) ⟪n,k+1⟫`, `⟪n+1,0⟫ = ⟪n,0⟫ = 1`,

(the manuscript's `⟪n,k⟫ = (2n-k-1) ⟪n-1,k-1⟫ + (k+1) ⟪n-1,k⟫`).  We prove the row
sums `∑_k ⟪n,k⟫ = (2n-1)!!`, the polynomial recurrence
`E_{n+1}(t) = (2nt+1) E_n(t) + t(1-t) E_n'(t)`, and the diagonal Stirling generating
function `∑_m S(n+m,m) t^m = t E_n(t)/(1-t)^{2n+1}` for `n ≥ 1`.

## Main results

* `secondEulerian`, `secondEulerian_succ_succ`, `secondEulerian_zero_right`,
  `secondEulerian_eq_zero_of_le`, `secondEulerian_succ_self`.
* `sum_secondEulerian_eq_doubleFactorial`.
* `diagStirlingSeries`, `secondEulerianSeries`, `one_sub_X_mul_diagStirlingSeries_succ`,
  `secondEulerianSeries_succ`, `one_sub_X_pow_mul_diagStirlingSeries`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

/-- The second-order Eulerian numbers, by the insertion recurrence. -/
def secondEulerian : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, 0 => secondEulerian n 0
  | n + 1, k + 1 => (2 * n - k) * secondEulerian n k + (k + 2) * secondEulerian n (k + 1)

/-- The second-order Eulerian triangle starts at `1`. -/
@[simp] theorem secondEulerian_zero_zero : secondEulerian 0 0 = 1 := rfl

/-- Row `0` of the second-order Eulerian triangle vanishes beyond its first entry. -/
@[simp] theorem secondEulerian_zero_succ (k : ℕ) : secondEulerian 0 (k + 1) = 0 := rfl

/-- Column `0` of the second-order Eulerian triangle is constant down the rows. -/
theorem secondEulerian_succ_zero (n : ℕ) : secondEulerian (n + 1) 0 = secondEulerian n 0 := rfl

/-- The recurrence `⟪n+1,k+1⟫ = (2n-k) ⟪n,k⟫ + (k+2) ⟪n,k+1⟫`. -/
theorem secondEulerian_succ_succ (n k : ℕ) :
    secondEulerian (n + 1) (k + 1) =
      (2 * n - k) * secondEulerian n k + (k + 2) * secondEulerian n (k + 1) := rfl

/-- `⟪n,0⟫ = 1`. -/
@[simp] theorem secondEulerian_zero_right (n : ℕ) : secondEulerian n 0 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [secondEulerian_succ_zero, ih]

/-- `⟪n,k⟫ = 0` for `1 ≤ n ≤ k`. -/
theorem secondEulerian_eq_zero_of_le : ∀ {n k : ℕ}, 1 ≤ n → n ≤ k → secondEulerian n k = 0
  | 0, _, h, _ => absurd h (by omega)
  | _ + 1, 0, _, h => absurd h (by omega)
  | n + 1, k + 1, _, h => by
    rw [secondEulerian_succ_succ]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        simp
    · rw [secondEulerian_eq_zero_of_le hn (by omega), secondEulerian_eq_zero_of_le hn (by omega),
        mul_zero, mul_zero, add_zero]

/-- `⟪n,n+1⟫ = 0`. -/
theorem secondEulerian_succ_self (n : ℕ) : secondEulerian n (n + 1) = 0 := by
  cases n with
  | zero => rfl
  | succ n => exact secondEulerian_eq_zero_of_le (by omega) (by omega)

/-- `⟪n,k⟫ = 0` for `2n < k`. -/
theorem secondEulerian_eq_zero_of_two_mul_lt {n k : ℕ} (h : 2 * n < k) : secondEulerian n k = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rfl
  · exact secondEulerian_eq_zero_of_le hn (by omega)

/-- `(2(n+1)-1)!! = (2n+1) · (2n-1)!!`. -/
theorem doubleFactorial_two_mul_succ_sub_one (n : ℕ) :
    (2 * (n + 1) - 1).doubleFactorial = (2 * n + 1) * (2 * n - 1).doubleFactorial := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [show 2 * (n + 1 + 1) - 1 = 2 * n + 1 + 2 by omega, Nat.doubleFactorial_add_two,
      show 2 * (n + 1) - 1 = 2 * n + 1 by omega]
    ring

/-- **Row sums:** `∑_{k ≤ n} ⟪n,k⟫ = (2n-1)!!`. -/
theorem sum_secondEulerian_eq_doubleFactorial (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), secondEulerian n k = (2 * n - 1).doubleFactorial := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [doubleFactorial_two_mul_succ_sub_one, ← ih, Finset.mul_sum,
      Finset.sum_range_succ' (fun k => secondEulerian (n + 1) k) (n + 1),
      secondEulerian_zero_right]
    simp only [secondEulerian_succ_succ]
    rw [Finset.sum_add_distrib]
    -- `∑_{k ≤ n} (k+2) ⟪n,k+1⟫ + 1 = ∑_{k ≤ n} (k+1) ⟪n,k⟫`
    have hshift : ∑ k ∈ Finset.range (n + 1), (k + 2) * secondEulerian n (k + 1) + 1
        = ∑ k ∈ Finset.range (n + 1), (k + 1) * secondEulerian n k := by
      rw [Finset.sum_range_succ (fun k => (k + 2) * secondEulerian n (k + 1)) n,
        secondEulerian_succ_self, mul_zero, add_zero,
        Finset.sum_range_succ' (fun k => (k + 1) * secondEulerian n k) n,
        secondEulerian_zero_right]
    calc ∑ k ∈ Finset.range (n + 1), (2 * n - k) * secondEulerian n k +
          ∑ k ∈ Finset.range (n + 1), (k + 2) * secondEulerian n (k + 1) + 1
        = ∑ k ∈ Finset.range (n + 1), (2 * n - k) * secondEulerian n k +
            (∑ k ∈ Finset.range (n + 1), (k + 2) * secondEulerian n (k + 1) + 1) := by ring
      _ = ∑ k ∈ Finset.range (n + 1), (2 * n - k) * secondEulerian n k +
            ∑ k ∈ Finset.range (n + 1), (k + 1) * secondEulerian n k := by rw [hshift]
      _ = ∑ k ∈ Finset.range (n + 1), (2 * n + 1) * secondEulerian n k := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k hk => ?_
          have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          rw [← add_mul, show 2 * n - k + (k + 1) = 2 * n + 1 by omega]

/-! ### The diagonal Stirling generating function -/

section

variable (R : Type*) [CommRing R]

/-- `F_n(t) = ∑_m S(n+m, m) t^m`. -/
noncomputable def diagStirlingSeries (n : ℕ) : R⟦X⟧ :=
  PowerSeries.mk fun m => (Nat.stirlingSecond (n + m) m : R)

/-- `E_n(t) = ∑_k ⟪n,k⟫ t^k` as a power series. -/
noncomputable def secondEulerianSeries (n : ℕ) : R⟦X⟧ :=
  PowerSeries.mk fun k => (secondEulerian n k : R)

/-- `(1 - t)' = -1`. -/
theorem derivative_one_sub_X : d⁄dX R (1 - X) = -1 := by
  ext n
  rw [coeff_derivative, map_sub, map_neg, PowerSeries.coeff_one, PowerSeries.coeff_one,
    PowerSeries.coeff_X]
  cases n with
  | zero => simp
  | succ n => simp

/-- `(1 - t) F_{n+1} = t F_n'`. -/
theorem one_sub_X_mul_diagStirlingSeries_succ (n : ℕ) :
    (1 - X) * diagStirlingSeries R (n + 1) = X * d⁄dX R (diagStirlingSeries R n) := by
  ext m
  rw [sub_mul, one_mul, map_sub]
  cases m with
  | zero =>
    rw [coeff_zero_X_mul, coeff_zero_X_mul, diagStirlingSeries, coeff_mk, Nat.add_zero,
      Nat.stirlingSecond_succ_zero, Nat.cast_zero, sub_zero]
  | succ m =>
    rw [coeff_succ_X_mul, coeff_succ_X_mul, coeff_derivative, diagStirlingSeries,
      diagStirlingSeries, coeff_mk, coeff_mk, coeff_mk,
      show n + 1 + (m + 1) = n + m + 1 + 1 by omega, show n + 1 + m = n + m + 1 by omega,
      show n + (m + 1) = n + m + 1 by omega, Nat.stirlingSecond_succ_succ]
    push_cast
    ring

/-- The polynomial recurrence `E_{n+1} = (2nt + 1) E_n + t(1-t) E_n'`. -/
theorem secondEulerianSeries_succ (n : ℕ) :
    secondEulerianSeries R (n + 1) =
      (((2 * n : ℕ) : R⟦X⟧) * X + 1) * secondEulerianSeries R n +
        X * (1 - X) * d⁄dX R (secondEulerianSeries R n) := by
  ext k
  have hE : ∀ j, coeff j (secondEulerianSeries R n) = (secondEulerian n j : R) := fun j => by
    rw [secondEulerianSeries, coeff_mk]
  rw [secondEulerianSeries, coeff_mk, ← map_natCast (PowerSeries.C : R →+* R⟦X⟧) (2 * n),
    add_mul, one_mul, map_add, map_add, mul_assoc, coeff_C_mul,
    show X * (1 - X) * d⁄dX R (secondEulerianSeries R n)
      = X * d⁄dX R (secondEulerianSeries R n) - X * (X * d⁄dX R (secondEulerianSeries R n)) by ring,
    map_sub]
  cases k with
  | zero =>
    simp only [coeff_zero_X_mul, mul_zero, zero_add, sub_zero, hE, secondEulerian_zero_right]
    exact (add_zero _).symm
  | succ k =>
    cases k with
    | zero =>
      simp only [coeff_succ_X_mul, coeff_zero_X_mul, coeff_derivative, hE,
        secondEulerian_succ_succ, secondEulerian_zero_right, Nat.sub_zero]
      push_cast
      ring
    | succ j =>
      simp only [coeff_succ_X_mul, coeff_derivative, hE, secondEulerian_succ_succ]
      rcases Nat.lt_or_ge (2 * n) (j + 1) with hlt | hge
      · have hz : secondEulerian n (j + 1) = 0 := secondEulerian_eq_zero_of_two_mul_lt hlt
        rw [Nat.sub_eq_zero_of_le hlt.le, hz]
        push_cast
        ring
      · push_cast [Nat.cast_sub hge]
        ring

/-- `F_1 = t/(1-t)^3`. -/
theorem diagStirlingSeries_one :
    diagStirlingSeries R 1 = X * PowerSeries.mk 1 ^ (2 + 1) := by
  ext m
  rw [mk_one_pow_eq_mk_choose_add, diagStirlingSeries, coeff_mk]
  cases m with
  | zero => simp
  | succ m =>
    rw [coeff_succ_X_mul, coeff_mk, show 1 + (m + 1) = m + 1 + 1 by omega,
      Nat.stirlingSecond_succ_self_left, show 2 + m = m + 1 + 1 by omega]

/-- `E_1 = 1`. -/
theorem secondEulerianSeries_one : secondEulerianSeries R 1 = 1 := by
  ext k
  rw [secondEulerianSeries, coeff_mk, PowerSeries.coeff_one]
  cases k with
  | zero => simp
  | succ k => simp [secondEulerian_eq_zero_of_le (by omega : 1 ≤ 1) (by omega : 1 ≤ k + 1)]

/-- **The diagonal Stirling generating function:**
`(1-t)^{2n+1} ∑_m S(n+m,m) t^m = t E_n(t)` for `n ≥ 1`, i.e.
`∑_m S(n+m,m) t^m = t E_n(t)/(1-t)^{2n+1}`. -/
theorem one_sub_X_pow_mul_diagStirlingSeries (n : ℕ) (hn : 1 ≤ n) :
    (1 - X) ^ (2 * n + 1) * diagStirlingSeries R n = X * secondEulerianSeries R n := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [diagStirlingSeries_one, secondEulerianSeries_one]
    have hunit : ((1 : R⟦X⟧) - X) ^ (2 * 1 + 1) * PowerSeries.mk 1 ^ (2 + 1) = 1 := by
      rw [show 2 * 1 + 1 = 2 + 1 by norm_num, ← mul_pow, mul_comm, mk_one_mul_one_sub_eq_one,
        one_pow]
    calc ((1 : R⟦X⟧) - X) ^ (2 * 1 + 1) * (X * PowerSeries.mk 1 ^ (2 + 1))
        = X * (((1 : R⟦X⟧) - X) ^ (2 * 1 + 1) * PowerSeries.mk 1 ^ (2 + 1)) := by ring
      _ = X * 1 := by rw [hunit]
  | succ n hn ih =>
    have hA := one_sub_X_mul_diagStirlingSeries_succ R n
    have hB := secondEulerianSeries_succ R n
    have hD := congrArg (d⁄dX R) ih
    rw [Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz, derivative_one_sub_X,
      derivative_X] at hD
    simp only [smul_eq_mul, nsmul_eq_mul] at hD
    push_cast at hD hB ⊢
    have hpow : ((1 : R⟦X⟧) - X) ^ (2 * (n + 1) + 1) = (1 - X) ^ (2 * n + 1) * (1 - X) ^ 2 := by
      rw [← pow_add, show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by ring]
    try simp only [Nat.add_sub_cancel] at hD
    rw [hpow]
    linear_combination (1 - X) ^ (2 * n) * (1 - X) ^ 2 * hA + X * (1 - X) * hD +
      (2 * (n : R⟦X⟧) + 1) * X * ih - X * hB

end

end Fabius
