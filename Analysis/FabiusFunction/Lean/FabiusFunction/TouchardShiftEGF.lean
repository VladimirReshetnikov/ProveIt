import FabiusFunction.BellShiftEGF
import FabiusFunction.BellHomogeneity

/-!
# Shifted Touchard polynomials and Spivey's identity for Touchard polynomials

With `T_n(x) = ∑_k S(n,k) x^k` (the complete Bell polynomial at constant weights `x`),

`∑_n T_{n+m}(x) t^n/n! = (∑_{j ≤ m} S(m,j) x^j e^{jt}) · ∑_n T_n(x) t^n/n!`,

the `m`-th derivative of `exp(x(e^t - 1))`.  Comparing coefficients gives Spivey's
identity for Touchard polynomials,

`T_{m+n}(x) = ∑_{j ≤ m} ∑_{k ≤ n} S(m,j) x^j C(n,k) T_k(x) j^{n-k}`,

over any commutative `ℚ`-algebra; the Bell-number case is `x = 1`.

## Main results

* `egfA_touchard_succ`: `∑_n T_{n+1}(x) t^n/n! = x e^t ∑_n T_n(x) t^n/n!`.
* `touchardExpX`, `derivative_touchardExpX`, `egfA_touchard_add`.
* `spivey_touchard`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

section

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- The Touchard recurrence `T_{n+1}(x) = x ∑_k C(n,k) T_k(x)` as a generating-function
identity. -/
theorem egfA_touchard_succ (x : A) :
    egfA A (fun n => Bell.complete (fun _ => x) (n + 1)) =
      PowerSeries.C x * (exp A * egfA A (fun n => Bell.complete (fun _ => x) n)) := by
  have hexp : exp A = egfA A (fun _ => (1 : A)) := by
    ext n
    rw [coeff_exp, coeff_egfA, mul_one]
  rw [hexp, egfA_mul, Bell.binomialConv_comm]
  ext n
  rw [coeff_C_mul, coeff_egfA, coeff_egfA, Bell.complete_succ, Bell.binomialConv_eq_sum_range,
    Bell.binomialConv_eq_sum_range, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Bell.shift_apply]
  ring

/-- `∑_{j ≤ m} S(m,j) x^j e^{jt}`, the Touchard polynomial `T_m` at `x e^t` written in the
weights `x^j`. -/
noncomputable def touchardExpX (x : A) (m : ℕ) : A⟦X⟧ :=
  ∑ j ∈ Finset.range (m + 1),
    PowerSeries.C ((Nat.stirlingSecond m j : A) * x ^ j) * expSeries A (j : A)

/-- `T_0` is `1`. -/
theorem touchardExpX_zero (x : A) : touchardExpX A x 0 = 1 := by
  rw [touchardExpX, Finset.sum_range_one, Nat.stirlingSecond_zero, Nat.cast_one, pow_zero, mul_one,
    map_one, one_mul, Nat.cast_zero, expSeries_zero]

/-- The Touchard recurrence for the series: `(T_m)' + x T_m e^t = T_{m+1}`. -/
theorem derivative_touchardExpX (x : A) (m : ℕ) :
    d⁄dX A (touchardExpX A x m) + PowerSeries.C x * (touchardExpX A x m * exp A) =
      touchardExpX A x (m + 1) := by
  have hder : d⁄dX A (touchardExpX A x m) = ∑ j ∈ Finset.range (m + 1),
      PowerSeries.C ((Nat.stirlingSecond m j : A) * x ^ j * j) * expSeries A (j : A) := by
    rw [touchardExpX, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Derivation.leibniz, derivative_C, smul_zero, add_zero, smul_eq_mul, derivative_expSeries]
    simp only [map_mul]
    ring
  have hmul : PowerSeries.C x * (touchardExpX A x m * exp A) = ∑ j ∈ Finset.range (m + 1),
      PowerSeries.C ((Nat.stirlingSecond m j : A) * x ^ (j + 1)) * expSeries A ((j + 1 : ℕ) : A) := by
    rw [touchardExpX, Finset.sum_mul, Finset.mul_sum, exp_eq_expSeries_one]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc, expSeries_mul, Nat.cast_succ, pow_succ]
    simp only [map_mul, map_pow]
    ring
  have hrhs : touchardExpX A x (m + 1) = ∑ j ∈ Finset.range (m + 1),
      PowerSeries.C ((Nat.stirlingSecond (m + 1) (j + 1) : A) * x ^ (j + 1)) *
        expSeries A ((j + 1 : ℕ) : A) := by
    rw [touchardExpX, Finset.sum_range_succ'
      (fun j => PowerSeries.C ((Nat.stirlingSecond (m + 1) j : A) * x ^ j) * expSeries A (j : A))
      (m + 1), Nat.stirlingSecond_succ_zero, Nat.cast_zero, zero_mul, map_zero, zero_mul, add_zero]
  have hsplit : ∑ j ∈ Finset.range (m + 1),
      PowerSeries.C ((Nat.stirlingSecond (m + 1) (j + 1) : A) * x ^ (j + 1)) *
        expSeries A ((j + 1 : ℕ) : A)
      = ∑ j ∈ Finset.range (m + 1),
          PowerSeries.C (((j + 1 : ℕ) : A) * Nat.stirlingSecond m (j + 1) * x ^ (j + 1)) *
            expSeries A ((j + 1 : ℕ) : A)
        + ∑ j ∈ Finset.range (m + 1),
          PowerSeries.C ((Nat.stirlingSecond m j : A) * x ^ (j + 1)) * expSeries A ((j + 1 : ℕ) : A) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Nat.stirlingSecond_succ_succ]
    push_cast
    rw [add_mul, map_add]
    ring
  have hshift : ∑ j ∈ Finset.range (m + 1),
      PowerSeries.C (((j + 1 : ℕ) : A) * Nat.stirlingSecond m (j + 1) * x ^ (j + 1)) *
        expSeries A ((j + 1 : ℕ) : A)
      = ∑ j ∈ Finset.range (m + 1),
          PowerSeries.C ((Nat.stirlingSecond m j : A) * x ^ j * j) * expSeries A (j : A) := by
    rw [Finset.sum_range_succ, Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self m),
      Nat.cast_zero, mul_zero, zero_mul, map_zero, zero_mul, add_zero,
      Finset.sum_range_succ'
        (fun j => PowerSeries.C ((Nat.stirlingSecond m j : A) * x ^ j * j) * expSeries A (j : A)) m,
      Nat.cast_zero, mul_zero, map_zero, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring_nf
  rw [hder, hmul, hrhs, hsplit, hshift]

/-- **The shifted Touchard generating function:**
`∑_n T_{n+m}(x) t^n/n! = T_m(x e^t) · ∑_n T_n(x) t^n/n!` (with `T_m(x e^t)` meaning
`∑_j S(m,j) x^j e^{jt}`). -/
theorem egfA_touchard_add (x : A) (m : ℕ) :
    egfA A (fun n => Bell.complete (fun _ => x) (n + m)) =
      touchardExpX A x m * egfA A (fun n => Bell.complete (fun _ => x) n) := by
  induction m with
  | zero => simp [touchardExpX_zero]
  | succ m ih =>
    have hD : d⁄dX A (egfA A fun n => Bell.complete (fun _ => x) (n + m)) =
        egfA A fun n => Bell.complete (fun _ => x) (n + (m + 1)) := by
      rw [derivative_egfA]
      congr 1
      funext n
      rw [Bell.shift_apply, show n + 1 + m = n + (m + 1) by omega]
    rw [← hD, ih, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    have hB : d⁄dX A (egfA A fun n => Bell.complete (fun _ => x) n) =
        PowerSeries.C x * (exp A * egfA A fun n => Bell.complete (fun _ => x) n) := by
      rw [derivative_egfA, ← egfA_touchard_succ]
      rfl
    rw [hB, ← derivative_touchardExpX]
    ring

end

/-- **Spivey's identity for Touchard polynomials:**
`T_{m+n}(x) = ∑_{j ≤ m} ∑_{k ≤ n} S(m,j) x^j · C(n,k) · T_k(x) · j^{n-k}`, over any commutative
`ℚ`-algebra. -/
theorem spivey_touchard (A : Type*) [CommRing A] [Algebra ℚ A] (x : A) (m n : ℕ) :
    Bell.complete (fun _ => x) (m + n) =
      ∑ j ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (n + 1),
        (Nat.stirlingSecond m j : A) * x ^ j *
          ((n.choose k : A) * (Bell.complete (fun _ => x) k * (j : A) ^ (n - k))) := by
  have h := congrArg (coeff n) (egfA_touchard_add A x m)
  rw [coeff_egfA, touchardExpX, Finset.sum_mul, map_sum] at h
  have hterm : ∀ j ∈ Finset.range (m + 1),
      coeff n (PowerSeries.C ((Nat.stirlingSecond m j : A) * x ^ j) * expSeries A (j : A) *
        egfA A (fun n => Bell.complete (fun _ => x) n))
      = (Nat.stirlingSecond m j : A) * x ^ j * (algebraMap ℚ A (1 / n.factorial) *
          ∑ k ∈ Finset.range (n + 1),
            (n.choose k : A) * (Bell.complete (fun _ => x) k * (j : A) ^ (n - k))) := by
    intro j _
    rw [mul_assoc, coeff_C_mul, expSeries, egfA_mul, coeff_egfA, Bell.binomialConv_comm,
      Bell.binomialConv_eq_sum_range]
  rw [Finset.sum_congr rfl hterm] at h
  have hfactor : ∑ j ∈ Finset.range (m + 1), (Nat.stirlingSecond m j : A) * x ^ j *
      (algebraMap ℚ A (1 / n.factorial) * ∑ k ∈ Finset.range (n + 1),
        (n.choose k : A) * (Bell.complete (fun _ => x) k * (j : A) ^ (n - k)))
      = algebraMap ℚ A (1 / n.factorial) * ∑ j ∈ Finset.range (m + 1),
        (Nat.stirlingSecond m j : A) * x ^ j * ∑ k ∈ Finset.range (n + 1),
          (n.choose k : A) * (Bell.complete (fun _ => x) k * (j : A) ^ (n - k)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hfactor] at h
  have hinv : algebraMap ℚ A (n.factorial : ℚ) * algebraMap ℚ A (1 / n.factorial) = 1 := by
    rw [← map_mul, mul_one_div_cancel (by positivity), map_one]
  have h' := congrArg (fun t => algebraMap ℚ A (n.factorial : ℚ) * t) h
  simp only [← mul_assoc, hinv, one_mul] at h'
  rw [Nat.add_comm, h']
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end Fabius
