import FabiusFunction.EulerianGeneratingFunctions
import FabiusFunction.BellShiftEGF

/-!
# The binomial recurrence and the exponential generating function of the Eulerian polynomials

The Eulerian polynomials `A_n(t) = ∑_k A(n,k) t^k` satisfy, for `n ≥ 1`,

`A_n(t) = ∑_{k < n} C(n,k) A_k(t) (t - 1)^{n-1-k}`,

and consequently their exponential generating function `F(x,t) = ∑_n A_n(t) x^n/n!`
satisfies `F(x,t) (t - e^{(t-1)x}) = t - 1`, i.e. `F = (t-1)/(t - e^{(t-1)x})`.

The recurrence is proved from the rational generating function
`∑_m (m+1)^n t^m = A_n(t)/(1-t)^{n+1}`: the binomial theorem
`∑_k C(n,k) (-1)^{n-k} (m+1)^k = m^n` turns the right side of the recurrence into
`(1-t)^n ∑_m ((m+1)^n - m^n) t^m = (1-t)^{n+1} ∑_m (m+1)^n t^m`.
The generating function is then the recurrence read coefficientwise in
`(ℚ[t])⟦x⟧`.

## Main results

* `X_mul_succPowSeries`, `sum_choose_neg_one_pow_succPowSeries`.
* `eulerian_binomial_recurrence_series` (in `R⟦X⟧`), `coe_eulerianPolynomial`,
  `eulerianPolynomial_binomial_recurrence` (in `R[X]`).
* `egfA_eulerianPolynomial_mul`: the exponential generating function.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

section

variable (R : Type*) [CommRing R]

/-- `∑_m m^n X^m = X · ∑_m (m+1)^n X^m` for `n ≥ 1`. -/
theorem X_mul_succPowSeries (n : ℕ) (hn : 1 ≤ n) :
    X * succPowSeries R n = PowerSeries.mk fun m => (m : R) ^ n := by
  ext m
  cases m with
  | zero => rw [coeff_zero_X_mul, coeff_mk, Nat.cast_zero, zero_pow (by omega)]
  | succ m =>
    rw [coeff_succ_X_mul, succPowSeries, coeff_mk, coeff_mk]
    push_cast
    ring

/-- The binomial theorem `∑_k C(n,k) (-1)^{n-k} (m+1)^k = m^n`, series by series. -/
theorem sum_choose_neg_one_pow_succPowSeries (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        PowerSeries.C ((n.choose k : R) * (-1) ^ (n - k)) * succPowSeries R k
      = PowerSeries.mk fun m => (m : R) ^ n := by
  ext m
  rw [map_sum, coeff_mk]
  have h : ((m : R) + 1 + (-1)) ^ n =
      ∑ k ∈ Finset.range (n + 1), ((m : R) + 1) ^ k * (-1) ^ (n - k) * n.choose k :=
    add_pow _ _ _
  rw [show (m : R) + 1 + (-1) = (m : R) by ring] at h
  rw [h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_C_mul, succPowSeries, coeff_mk]
  ring

/-- **The binomial recurrence of the Eulerian polynomials** in `R⟦X⟧`:
`A_n(X) = ∑_{k < n} C(n,k) A_k(X) (X - 1)^{n-1-k}` for `n ≥ 1`, with
`A_n(X) = ∑_k A(n,k) X^k`. -/
theorem eulerian_binomial_recurrence_series (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ Finset.range (n + 1), (eulerianNumber n k : R⟦X⟧) * X ^ k) =
      ∑ k ∈ Finset.range n, PowerSeries.C (n.choose k : R) *
        ((∑ j ∈ Finset.range (k + 1), (eulerianNumber k j : R⟦X⟧) * X ^ j) *
          (X - 1) ^ (n - 1 - k)) := by
  have hP : ∀ k, (∑ j ∈ Finset.range (k + 1), (eulerianNumber k j : R⟦X⟧) * X ^ j)
      = (1 - X) ^ (k + 1) * succPowSeries R k :=
    fun k => (one_sub_X_pow_mul_succPowSeries R k).symm
  rw [hP n]
  have hterm : ∀ k ∈ Finset.range n, PowerSeries.C (n.choose k : R) *
      ((∑ j ∈ Finset.range (k + 1), (eulerianNumber k j : R⟦X⟧) * X ^ j) * (X - 1) ^ (n - 1 - k))
      = (1 - X) ^ n *
          (-(PowerSeries.C ((n.choose k : R) * (-1) ^ (n - k)) * succPowSeries R k)) := by
    intro k hk
    have hkn : k < n := Finset.mem_range.mp hk
    have hsign : ((X : R⟦X⟧) - 1) ^ (n - 1 - k) = (-1) ^ (n - 1 - k) * (1 - X) ^ (n - 1 - k) := by
      rw [← neg_sub, neg_pow]
    have hpow : ((1 : R⟦X⟧) - X) ^ (k + 1) * (1 - X) ^ (n - 1 - k) = (1 - X) ^ n := by
      rw [← pow_add]
      congr 1
      omega
    have hsgn2 : ((-1 : R⟦X⟧)) ^ (n - k) = -((-1) ^ (n - 1 - k)) := by
      rw [show n - k = n - 1 - k + 1 by omega, pow_succ]
      ring
    rw [hP k, hsign, map_mul, map_pow, map_neg, map_one, hsgn2]
    calc PowerSeries.C (n.choose k : R) *
          ((1 - X) ^ (k + 1) * succPowSeries R k * ((-1) ^ (n - 1 - k) * (1 - X) ^ (n - 1 - k)))
        = ((1 - X) ^ (k + 1) * (1 - X) ^ (n - 1 - k)) *
            (PowerSeries.C (n.choose k : R) * (-1) ^ (n - 1 - k) * succPowSeries R k) := by ring
      _ = _ := by rw [hpow]; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_neg_distrib]
  have hsum : ∑ k ∈ Finset.range n,
      PowerSeries.C ((n.choose k : R) * (-1) ^ (n - k)) * succPowSeries R k
      = X * succPowSeries R n - succPowSeries R n := by
    have h := sum_choose_neg_one_pow_succPowSeries R n
    rw [Finset.sum_range_succ, Nat.choose_self, Nat.sub_self, pow_zero, Nat.cast_one, mul_one,
      map_one, one_mul, ← X_mul_succPowSeries R n hn] at h
    exact eq_sub_of_add_eq h
  rw [hsum]
  ring

/-- The Eulerian polynomial as a power series. -/
theorem coe_eulerianPolynomial (n : ℕ) :
    ((eulerianPolynomial R n : Polynomial R) : R⟦X⟧) =
      ∑ k ∈ Finset.range (n + 1), (eulerianNumber n k : R⟦X⟧) * X ^ k := by
  rw [eulerianPolynomial, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_natCast, map_pow, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]

/-- **The binomial recurrence of the Eulerian polynomials:**
`A_n(t) = ∑_{k < n} C(n,k) A_k(t) (t - 1)^{n-1-k}` for `n ≥ 1`, in `R[t]`. -/
theorem eulerianPolynomial_binomial_recurrence (n : ℕ) (hn : 1 ≤ n) :
    eulerianPolynomial R n = ∑ k ∈ Finset.range n,
      (n.choose k : Polynomial R) * (eulerianPolynomial R k * (Polynomial.X - 1) ^ (n - 1 - k)) := by
  apply Polynomial.coe_inj.mp
  rw [coe_eulerianPolynomial, eulerian_binomial_recurrence_series R n hn,
    ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_natCast Polynomial.coeToPowerSeries.ringHom, map_mul, map_pow, map_sub,
    map_one, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_X, coe_eulerianPolynomial, map_natCast (PowerSeries.C : R →+* R⟦X⟧)]

end

/-- **The exponential generating function of the Eulerian polynomials:**
`(∑_n A_n(t) x^n/n!) · (t - e^{(t-1)x}) = t - 1` in `(ℚ[t])⟦x⟧`, i.e.
`∑_n A_n(t) x^n/n! = (t-1)/(t - e^{(t-1)x})`. -/
theorem egfA_eulerianPolynomial_mul :
    egfA (Polynomial ℚ) (fun n => eulerianPolynomial ℚ n) *
      (PowerSeries.C (Polynomial.X : Polynomial ℚ) - expSeries (Polynomial ℚ) (Polynomial.X - 1)) =
      PowerSeries.C (Polynomial.X - 1 : Polynomial ℚ) := by
  have h1 : PowerSeries.C (Polynomial.X : Polynomial ℚ) *
      egfA (Polynomial ℚ) (fun n => eulerianPolynomial ℚ n)
      = egfA (Polynomial ℚ) (fun n => Polynomial.X * eulerianPolynomial ℚ n) := by
    ext n
    rw [coeff_C_mul, coeff_egfA, coeff_egfA]
    ring
  rw [mul_sub, mul_comm _ (PowerSeries.C _), h1, expSeries, egfA_mul]
  ext n
  rw [map_sub, coeff_egfA, coeff_egfA, PowerSeries.coeff_C, Bell.binomialConv_eq_sum_range]
  cases n with
  | zero => simp [eulerianPolynomial]
  | succ n =>
    rw [if_neg (Nat.succ_ne_zero n), Finset.sum_range_succ, Nat.choose_self, Nat.sub_self, pow_zero,
      mul_one, Nat.cast_one, one_mul]
    have hrec := eulerianPolynomial_binomial_recurrence ℚ (n + 1) (by omega)
    have hfac : ∑ k ∈ Finset.range (n + 1),
        ((n + 1).choose k : Polynomial ℚ) *
          (eulerianPolynomial ℚ k * (Polynomial.X - 1) ^ (n + 1 - k))
        = (Polynomial.X - 1) * ∑ k ∈ Finset.range (n + 1),
            ((n + 1).choose k : Polynomial ℚ) *
              (eulerianPolynomial ℚ k * (Polynomial.X - 1) ^ (n + 1 - 1 - k)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [show n + 1 - k = (n + 1 - 1 - k) + 1 by omega, pow_succ]
      ring
    rw [hfac, ← hrec]
    ring

end Fabius
