import FabiusFunction.BellGeneratingFunctions
import FabiusFunction.BinomialInversion

/-!
# Shifted Bell numbers: Spivey's identity and Bell inversion

The exponential generating function of the shifted Bell numbers `n ↦ B(n+m)` is
the `m`-th derivative of `exp(e^t - 1)`, which equals `T_m(e^t) · exp(e^t - 1)`
with `T_m(x) = ∑_j S(m,j) x^j` the Touchard polynomial:

`∑_n B(n+m) t^n/n! = (∑_{j ≤ m} S(m,j) e^{jt}) · ∑_n B(n) t^n/n!`.

Reading off the coefficient of `t^n/n!` gives **Spivey's identity**

`B(m+n) = ∑_{j ≤ m} ∑_{k ≤ n} S(m,j) C(n,k) j^{n-k} B(k)`,

and binomial inversion of `B(n+1) = ∑_k C(n,k) B(k)` gives
`B(n) = ∑_j (-1)^{n-j} C(n,j) B(j+1)`.

## Main results

* `expSeries`, `expSeries_mul`, `derivative_expSeries`: `e^{at}` as an EGF.
* `bell_succ_eq_sum_choose`, `egfA_bell_succ`.
* `touchardExp`, `derivative_touchardExp`: `T_{m+1}(e^t) = (T_m(e^t))' + T_m(e^t) e^t`.
* `egfA_bell_add`: the shifted Bell generating function.
* `spivey`: Spivey's identity.
* `bell_eq_sum_neg_one_pow_choose_bell_succ`: the Bell inversion identity.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

/-- `B(n+1) = ∑_{k ≤ n} C(n,k) B(k)` (Mathlib's recurrence, reflected). -/
theorem bell_succ_eq_sum_choose (n : ℕ) :
    Nat.bell (n + 1) = ∑ k ∈ Finset.range (n + 1), n.choose k * Nat.bell k := by
  rw [Nat.bell_succ, ← Nat.range_succ_eq_Iic,
    ← Finset.sum_range_reflect (fun k => n.choose k * Nat.bell k) (n + 1)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [Nat.add_sub_cancel, Nat.choose_symm hin]

section

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- The exponential series `e^{at} = ∑_n a^n t^n/n!`. -/
noncomputable def expSeries (a : A) : A⟦X⟧ := egfA A fun n => a ^ n

/-- `e^{0 t} = 1`. -/
theorem expSeries_zero : expSeries A 0 = 1 := by
  ext n
  rw [expSeries, coeff_egfA, PowerSeries.coeff_one]
  cases n with
  | zero => simp
  | succ n => simp

/-- `e^{at} e^{bt} = e^{(a+b)t}`. -/
theorem expSeries_mul (a b : A) : expSeries A a * expSeries A b = expSeries A (a + b) := by
  rw [expSeries, expSeries, expSeries, egfA_mul]
  congr 1
  funext n
  rw [Bell.binomialConv_eq_sum_range, add_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- `(e^{at})' = a e^{at}`. -/
theorem derivative_expSeries (a : A) :
    d⁄dX A (expSeries A a) = PowerSeries.C a * expSeries A a := by
  rw [expSeries, derivative_egfA]
  ext n
  rw [coeff_egfA, coeff_C_mul, coeff_egfA, Bell.shift_apply, pow_succ]
  ring

/-- `e^t` as the exponential series at `1`. -/
theorem exp_eq_expSeries_one : exp A = expSeries A 1 := by
  ext n
  rw [coeff_exp, expSeries, coeff_egfA, one_pow, mul_one]

/-- The shifted Bell generating function: `∑_n B(n+1) t^n/n! = e^t ∑_n B(n) t^n/n!`. -/
theorem egfA_bell_succ :
    egfA A (fun n => (Nat.bell (n + 1) : A)) = exp A * egfA A (fun n => (Nat.bell n : A)) := by
  have hexp : exp A = egfA A (fun _ => (1 : A)) := by
    ext n
    rw [coeff_exp, coeff_egfA, mul_one]
  rw [hexp, egfA_mul, Bell.binomialConv_comm]
  congr 1
  funext n
  rw [Bell.binomialConv_eq_sum_range, bell_succ_eq_sum_choose, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

/-- The derivative of the shifted Bell generating function shifts once more. -/
theorem derivative_egfA_bell_add (m : ℕ) :
    d⁄dX A (egfA A fun n => (Nat.bell (n + m) : A)) =
      egfA A fun n => (Nat.bell (n + (m + 1)) : A) := by
  rw [derivative_egfA]
  congr 1
  funext n
  rw [Bell.shift_apply, show n + 1 + m = n + (m + 1) by omega]

/-- `T_m(e^t) = ∑_{j ≤ m} S(m,j) e^{jt}`, the Touchard polynomial at `e^t`. -/
noncomputable def touchardExp (m : ℕ) : A⟦X⟧ :=
  ∑ j ∈ Finset.range (m + 1), PowerSeries.C (Nat.stirlingSecond m j : A) * expSeries A (j : A)

/-- `T_0(e^t) = 1`. -/
theorem touchardExp_zero : touchardExp A 0 = 1 := by
  rw [touchardExp, Finset.sum_range_one, Nat.stirlingSecond_zero, Nat.cast_one, map_one, one_mul,
    Nat.cast_zero, expSeries_zero]

/-- The Touchard recurrence at `e^t`: `T_m(e^t)' + T_m(e^t) e^t = T_{m+1}(e^t)`. -/
theorem derivative_touchardExp (m : ℕ) :
    d⁄dX A (touchardExp A m) + touchardExp A m * exp A = touchardExp A (m + 1) := by
  have hder : d⁄dX A (touchardExp A m) = ∑ j ∈ Finset.range (m + 1),
      PowerSeries.C ((Nat.stirlingSecond m j : A) * j) * expSeries A (j : A) := by
    rw [touchardExp, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Derivation.leibniz, derivative_C, smul_zero, add_zero, smul_eq_mul, derivative_expSeries,
      map_mul]
    ring
  have hmul : touchardExp A m * exp A = ∑ j ∈ Finset.range (m + 1),
      PowerSeries.C (Nat.stirlingSecond m j : A) * expSeries A ((j + 1 : ℕ) : A) := by
    rw [touchardExp, Finset.sum_mul, exp_eq_expSeries_one]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc, expSeries_mul, Nat.cast_succ]
  have hrhs : touchardExp A (m + 1) = ∑ j ∈ Finset.range (m + 1),
      PowerSeries.C (Nat.stirlingSecond (m + 1) (j + 1) : A) * expSeries A ((j + 1 : ℕ) : A) := by
    rw [touchardExp, Finset.sum_range_succ'
      (fun j => PowerSeries.C (Nat.stirlingSecond (m + 1) j : A) * expSeries A (j : A)) (m + 1),
      Nat.stirlingSecond_succ_zero, Nat.cast_zero, map_zero, zero_mul, add_zero]
  have hsplit : ∑ j ∈ Finset.range (m + 1),
      PowerSeries.C (Nat.stirlingSecond (m + 1) (j + 1) : A) * expSeries A ((j + 1 : ℕ) : A)
      = ∑ j ∈ Finset.range (m + 1),
          PowerSeries.C (((j + 1 : ℕ) : A) * Nat.stirlingSecond m (j + 1)) *
            expSeries A ((j + 1 : ℕ) : A)
        + ∑ j ∈ Finset.range (m + 1),
          PowerSeries.C (Nat.stirlingSecond m j : A) * expSeries A ((j + 1 : ℕ) : A) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Nat.stirlingSecond_succ_succ, Nat.cast_add, Nat.cast_mul, map_add, map_mul]
    push_cast
    ring
  have hshift : ∑ j ∈ Finset.range (m + 1),
      PowerSeries.C (((j + 1 : ℕ) : A) * Nat.stirlingSecond m (j + 1)) * expSeries A ((j + 1 : ℕ) : A)
      = ∑ j ∈ Finset.range (m + 1),
          PowerSeries.C ((Nat.stirlingSecond m j : A) * j) * expSeries A (j : A) := by
    rw [Finset.sum_range_succ, Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self m),
      Nat.cast_zero, mul_zero, map_zero, zero_mul, add_zero,
      Finset.sum_range_succ'
        (fun j => PowerSeries.C ((Nat.stirlingSecond m j : A) * j) * expSeries A (j : A)) m,
      Nat.cast_zero, mul_zero, map_zero, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm ((j + 1 : ℕ) : A)]
  rw [hder, hmul, hrhs, hsplit, hshift]

/-- **The shifted Bell generating function:**
`∑_n B(n+m) t^n/n! = T_m(e^t) · ∑_n B(n) t^n/n!`, i.e. the `m`-th derivative of
`exp(e^t - 1)` is `T_m(e^t) exp(e^t - 1)`. -/
theorem egfA_bell_add (m : ℕ) :
    egfA A (fun n => (Nat.bell (n + m) : A)) =
      touchardExp A m * egfA A (fun n => (Nat.bell n : A)) := by
  induction m with
  | zero => simp [touchardExp_zero]
  | succ m ih =>
    have hB : d⁄dX A (egfA A fun n => (Nat.bell n : A)) = exp A * egfA A (fun n => (Nat.bell n : A)) := by
      rw [derivative_egfA, ← egfA_bell_succ]
      rfl
    rw [← derivative_egfA_bell_add, ih, Derivation.leibniz, smul_eq_mul, smul_eq_mul, hB,
      ← derivative_touchardExp]
    ring

end

/-- **Spivey's identity:**
`B(m+n) = ∑_{j ≤ m} ∑_{k ≤ n} S(m,j) · C(n,k) · B(k) · j^{n-k}`. -/
theorem spivey (m n : ℕ) :
    Nat.bell (m + n) = ∑ j ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (n + 1),
      Nat.stirlingSecond m j * (n.choose k * (Nat.bell k * j ^ (n - k))) := by
  have h := congrArg (coeff n) (egfA_bell_add ℚ m)
  rw [coeff_egfA, touchardExp, Finset.sum_mul, map_sum] at h
  have hterm : ∀ j ∈ Finset.range (m + 1),
      coeff n (PowerSeries.C (Nat.stirlingSecond m j : ℚ) * expSeries ℚ (j : ℚ) *
        egfA ℚ (fun n => (Nat.bell n : ℚ)))
      = (Nat.stirlingSecond m j : ℚ) * (algebraMap ℚ ℚ (1 / n.factorial) *
          ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * ((Nat.bell k : ℚ) * (j : ℚ) ^ (n - k))) := by
    intro j _
    rw [mul_assoc, coeff_C_mul, expSeries, egfA_mul, coeff_egfA, Bell.binomialConv_comm,
      Bell.binomialConv_eq_sum_range]
  rw [Finset.sum_congr rfl hterm] at h
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at h
  have hfactor : ∑ j ∈ Finset.range (m + 1), (Nat.stirlingSecond m j : ℚ) *
      ((1 / (n.factorial : ℚ)) *
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * ((Nat.bell k : ℚ) * (j : ℚ) ^ (n - k)))
      = (1 / (n.factorial : ℚ)) * ∑ j ∈ Finset.range (m + 1), (Nat.stirlingSecond m j : ℚ) *
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * ((Nat.bell k : ℚ) * (j : ℚ) ^ (n - k)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hfactor] at h
  have hn : (1 / (n.factorial : ℚ)) ≠ 0 := one_div_ne_zero (by positivity)
  have h' := mul_left_cancel₀ hn h
  simp only [Finset.mul_sum] at h'
  rw [Nat.add_comm]
  exact_mod_cast h'

/-- **Bell inversion:** `B(n) = ∑_{j ≤ n} (-1)^{n-j} C(n,j) B(j+1)`. -/
theorem bell_eq_sum_neg_one_pow_choose_bell_succ (n : ℕ) :
    (Nat.bell n : ℤ) = ∑ j ∈ Finset.range (n + 1),
      (-1 : ℤ) ^ (n - j) * n.choose j * Nat.bell (j + 1) := by
  refine binomial_inversion_ring (fun j => (Nat.bell j : ℤ)) (fun n => (Nat.bell (n + 1) : ℤ)) ?_ n
  intro n
  rw [bell_succ_eq_sum_choose, Nat.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

end Fabius
