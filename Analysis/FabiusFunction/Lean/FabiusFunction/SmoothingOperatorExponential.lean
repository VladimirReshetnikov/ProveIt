import FabiusFunction.SmoothingOperatorInversion
import FabiusFunction.MomentCumulantAlgebra

/-!
# The operator exponential of the smoothing calculus

The TM volume's cumulant-operator display asserts, "formally, and
exactly at the level of the local Fourier logarithm",

`Up = exp(∑_{r≥1} κ_{2r}/(2r)!·4^{-rm}·D^{2r})·u_m`,

the exponential of the cumulant operator turning into the moment
operator.  This module proves that identity *at the formal level*, in
full generality: for any zero-constant exponent series `K` over a
rational algebra, the smoothing operator of its generated exponential
`exp(K)` acts on every polynomial as the (finite, degreewise
nilpotent) exponential of the operator of `K`,

`seriesDerivOp (expSeries E) a q
  = ∑_{d ≤ deg q} (1/d!)·(seriesDerivOp K a)^[d] q`.

Expanding the exponential thus changes cumulants into moments exactly
as the display claims — with the Fabius instance available through
the moment–cumulant dictionary of `MomentCumulantAlgebra`.

* `coeff_pow_eq_zero_of_lt` — low coefficients of powers of a
  zero-constant series vanish;
* `expCoeff_eq_sum_coeff_pow` — each coefficient of the generated
  exponential is the truncated exponential of the exponent;
* `seriesDerivOp_expSeries` — **the operator exponential**.
-/

set_option autoImplicit false

open Finset Polynomial
open Fabius.SaddleExpansion

namespace Fabius

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- Low coefficients of powers of a zero-constant series vanish. -/
theorem coeff_pow_eq_zero_of_lt {φ : PowerSeries R}
    (h0 : PowerSeries.constantCoeff φ = 0) {m d : ℕ} (hmd : m < d) :
    PowerSeries.coeff m (φ ^ d) = 0 := by
  induction d generalizing m with
  | zero => omega
  | succ d ih =>
    rw [pow_succ, PowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    have hsum := Finset.mem_antidiagonal.mp hp
    by_cases h2 : p.2 = 0
    · rw [h2, PowerSeries.coeff_zero_eq_constantCoeff_apply, h0,
        mul_zero]
    · rw [ih (by omega), zero_mul]

/-- Each coefficient of the generated exponential is the truncated
exponential of the exponent series. -/
theorem expCoeff_eq_sum_coeff_pow (E : ℕ → R) (hE0 : E 0 = 0)
    (m : ℕ) :
    expCoeff E m = ∑ d ∈ range (m + 1),
      algebraMap ℚ R (1 / d.factorial) *
        PowerSeries.coeff m ((exponentSeries E) ^ d) := by
  have hconst : PowerSeries.constantCoeff (exponentSeries E) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simpa using hE0
  have h1 : expCoeff E m = PowerSeries.coeff m (expSeries E) :=
    (coeff_expSeries E m).symm
  rw [h1, expSeries_eq_exp_subst E hE0,
    PowerSeries.coeff_subst'
      (PowerSeries.HasSubst.of_constantCoeff_zero' hconst)]
  rw [finsum_eq_finsetSum_of_support_subset _ (s := range (m + 1)) ?_]
  · refine Finset.sum_congr rfl fun d _ => ?_
    rw [PowerSeries.coeff_exp, smul_eq_mul]
  · intro d hd
    simp only [Function.mem_support] at hd
    by_contra hdm
    rw [Finset.mem_coe, Finset.mem_range, not_lt] at hdm
    exact hd (by
      rw [coeff_pow_eq_zero_of_lt hconst (by omega), smul_zero])

/-- **The operator exponential**: on every polynomial the smoothing
operator of the generated exponential series is the finite
exponential of the exponent's operator — the formal face of the
cumulant-operator display. -/
theorem seriesDerivOp_expSeries (E : ℕ → R) (hE0 : E 0 = 0) (a : R)
    (q : R[X]) :
    seriesDerivOp (expSeries E) a q =
      ∑ d ∈ range (q.natDegree + 1),
        algebraMap ℚ R (1 / d.factorial) •
          (fun r => seriesDerivOp (exponentSeries E) a r)^[d] q := by
  have hconst : PowerSeries.constantCoeff (exponentSeries E) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simpa using hE0
  have hiter : ∀ (d : ℕ) (r : R[X]),
      (fun r => seriesDerivOp (exponentSeries E) a r)^[d] r =
        seriesDerivOp ((exponentSeries E) ^ d) a r := by
    intro d
    induction d with
    | zero =>
        intro r
        rw [Function.iterate_zero_apply, pow_zero, seriesDerivOp_one]
    | succ d ih =>
        intro r
        rw [Function.iterate_succ_apply', ih r, ← seriesDerivOp_mul,
          ← pow_succ']
  simp_rw [hiter]
  calc seriesDerivOp (expSeries E) a q
      = ∑ m ∈ range (q.natDegree + 1),
          ((∑ d ∈ range (q.natDegree + 1),
            algebraMap ℚ R (1 / d.factorial) *
              PowerSeries.coeff m ((exponentSeries E) ^ d)) *
            a ^ m) • derivative^[m] q := by
        rw [seriesDerivOp]
        refine Finset.sum_congr rfl fun m hm => ?_
        congr 2
        rw [coeff_expSeries, expCoeff_eq_sum_coeff_pow E hE0 m]
        refine Finset.sum_subset ?_ ?_
        · intro d hd
          rw [Finset.mem_range] at hd ⊢
          rw [Finset.mem_range] at hm
          omega
        · intro d _hd hdm
          rw [Finset.mem_range, not_lt] at hdm
          rw [coeff_pow_eq_zero_of_lt hconst (by omega), mul_zero]
    _ = ∑ d ∈ range (q.natDegree + 1),
          algebraMap ℚ R (1 / d.factorial) •
            seriesDerivOp ((exponentSeries E) ^ d) a q := by
        simp_rw [Finset.sum_mul, Finset.sum_smul, seriesDerivOp,
          Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d _ =>
          Finset.sum_congr rfl fun m _ => ?_
        rw [mul_assoc]

end Fabius
