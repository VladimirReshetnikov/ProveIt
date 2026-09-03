import FabiusFunction.CoefficientRules
import FabiusFunction.BellHomogeneity
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# Elementary symmetric functions through the complete Bell polynomials

For a finite family `u : ι → A` indexed by `s : Finset ι`, with power sums
`p_r = ∑_{i ∈ s} u_i^r`, the source's identity

`e_n = (1/n!) B_n(p_1, -1! p_2, 2! p_3, …, (-1)^{n-1}(n-1)! p_n)`
(`esymm_eq_bell_complete`)

expresses the elementary symmetric functions through the complete Bell polynomials, and its
sign variant `e_n = ((-1)^n/n!) B_n(-p_1, -1! p_2, …, -(n-1)! p_n)`
(`esymm_eq_neg_bell_complete`) follows from the weighted homogeneity of `B_n`.

The source proves it by taking logarithms of `E(t) = ∏_i (1 + u_i t)`.  Mathlib's formal
logarithm has no `exp ∘ log = id`, and supplying one is a larger undertaking than the
identity, so the formal proof instead compares the two sides through the differential
equation they share.  Both `E` and `∑_n B_n t^n/n!` satisfy

`F' = F · W`,  `W = ∑_{i ∈ s} u_i/(1 + u_i t)`,  `F(0) = 1`,

and a series with `F(0) = 0` satisfying that equation is zero
(`Fabius.eq_zero_of_derivative_eq_mul`), so the two agree.  Nothing here needs a logarithm,
an exponential, or an inverse: `u_i/(1 + u_i t)` is written as `u_i` times the geometric
series of `-u_i` (`logDerivSeries`), which is what makes the induction over `s` go through
with only Leibniz and `Fabius.one_sub_C_mul_X_mul_geomSeries`.

`E`'s coefficients are the elementary symmetric functions by `Finset.prod_add`
(`coeff_elemSeries`), stated as a sum over `s.powersetCard n` and also in terms of Mathlib's
`Multiset.esymm`.

## Main results

* `elemSeries`, `logDerivSeries`, `derivative_elemSeries`.
* `coeff_elemSeries`, `coeff_logDerivSeries`.
* `elemSeries_eq_egfA_bell_complete`.
* `esymm_eq_bell_complete`, `esymm_eq_neg_bell_complete`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

section Symmetric

variable {ι : Type*} (A : Type*) [CommRing A] [Algebra ℚ A]

/-- The power sums `p_r = ∑_{i ∈ s} u_i^r`. -/
def powerSum (s : Finset ι) (u : ι → A) (r : ℕ) : A := ∑ i ∈ s, u i ^ r

/-- The Newton weights `x_r = (-1)^{r-1} (r-1)! p_r`, with `x_0 = 0`. -/
noncomputable def newtonWeight (s : Finset ι) (u : ι → A) (r : ℕ) : A :=
  if r = 0 then 0 else (-1 : A) ^ (r - 1) * ((r - 1).factorial : A) * powerSum A s u r

/-- The generating function `E(t) = ∏_{i ∈ s} (1 + u_i t)`. -/
noncomputable def elemSeries (s : Finset ι) (u : ι → A) : A⟦X⟧ :=
  ∏ i ∈ s, (1 + PowerSeries.C (u i) * X)

/-- The logarithmic derivative `W(t) = ∑_{i ∈ s} u_i/(1 + u_i t)`, written without an
inverse as `u_i` times the geometric series of `-u_i`. -/
noncomputable def logDerivSeries (s : Finset ι) (u : ι → A) : A⟦X⟧ :=
  ∑ i ∈ s, PowerSeries.C (u i) * geomSeries (-(u i))

/-- `(1 + a t) · a/(1 + a t) = a`, with no inverse taken. -/
theorem one_add_C_mul_X_mul_geom (a : A) :
    (1 + PowerSeries.C a * X) * (PowerSeries.C a * geomSeries (-a)) = PowerSeries.C a := by
  have h := one_sub_C_mul_X_mul_geomSeries (-a)
  have he : (1 : A⟦X⟧) - PowerSeries.C (-a) * X = 1 + PowerSeries.C a * X := by
    rw [map_neg, neg_mul, sub_neg_eq_add]
  rw [he] at h
  calc (1 + PowerSeries.C a * X) * (PowerSeries.C a * geomSeries (-a))
      = PowerSeries.C a * ((1 + PowerSeries.C a * X) * geomSeries (-a)) := by ring
    _ = PowerSeries.C a := by rw [h, mul_one]

/-- The derivative of a single factor. -/
theorem derivative_one_add_C_mul_X (a : A) :
    d⁄dX A (1 + PowerSeries.C a * X) = PowerSeries.C a := by
  rw [map_add, Derivation.map_one_eq_zero, zero_add, Derivation.leibniz, derivative_C,
    smul_zero, add_zero, PowerSeries.derivative_X, smul_eq_mul, mul_one]

/-- **The logarithmic derivative:** `E' = E · W`. -/
theorem derivative_elemSeries (s : Finset ι) (u : ι → A) :
    d⁄dX A (elemSeries A s u) = elemSeries A s u * logDerivSeries A s u := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [elemSeries, logDerivSeries, Finset.prod_empty, Finset.sum_empty,
      Derivation.map_one_eq_zero, mul_zero]
  | insert a s ha ih =>
    rw [elemSeries, Finset.prod_insert ha, ← elemSeries, logDerivSeries,
      Finset.sum_insert ha, ← logDerivSeries, Derivation.leibniz,
      derivative_one_add_C_mul_X, ih, smul_eq_mul, smul_eq_mul]
    have hfac := one_add_C_mul_X_mul_geom A (u a)
    calc (1 + PowerSeries.C (u a) * X) * (elemSeries A s u * logDerivSeries A s u)
          + elemSeries A s u * PowerSeries.C (u a)
        = (1 + PowerSeries.C (u a) * X) * (elemSeries A s u * logDerivSeries A s u)
          + elemSeries A s u *
            ((1 + PowerSeries.C (u a) * X) *
              (PowerSeries.C (u a) * geomSeries (-(u a)))) := by rw [hfac]
      _ = (1 + PowerSeries.C (u a) * X) * elemSeries A s u *
            (PowerSeries.C (u a) * geomSeries (-(u a)) + logDerivSeries A s u) := by ring

/-- `E(0) = 1`. -/
theorem constantCoeff_elemSeries (s : Finset ι) (u : ι → A) :
    constantCoeff (elemSeries A s u) = 1 := by
  classical
  rw [elemSeries, map_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [map_add, map_one, map_mul, constantCoeff_X, mul_zero, add_zero]

/-- The coefficients of `W` are the signed power sums. -/
theorem coeff_logDerivSeries (s : Finset ι) (u : ι → A) (r : ℕ) :
    coeff r (logDerivSeries A s u) = (-1 : A) ^ r * powerSum A s u (r + 1) := by
  rw [logDerivSeries, map_sum, powerSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_C_mul, coeff_geomSeries]
  ring

/-- `W` is the derivative of the Newton weight series. -/
theorem logDerivSeries_eq_derivative_egfA (s : Finset ι) (u : ι → A) :
    logDerivSeries A s u = d⁄dX A (egfA A (newtonWeight A s u)) := by
  refine PowerSeries.ext fun r => ?_
  rw [coeff_logDerivSeries, derivative_egfA, coeff_egfA, Bell.shift_apply, newtonWeight,
    if_neg (Nat.succ_ne_zero r), Nat.add_sub_cancel]
  have hfac : algebraMap ℚ A (1 / r.factorial) * ((r.factorial : ℕ) : A) = 1 := by
    have hn : ((r.factorial : ℚ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
    rw [← map_natCast (algebraMap ℚ A) r.factorial, ← map_mul, one_div, inv_mul_cancel₀ hn,
      map_one]
  calc (-1 : A) ^ r * powerSum A s u (r + 1)
      = algebraMap ℚ A (1 / r.factorial) * ((r.factorial : ℕ) : A) *
          ((-1 : A) ^ r * powerSum A s u (r + 1)) := by rw [hfac, one_mul]
    _ = algebraMap ℚ A (1 / r.factorial) *
          ((-1 : A) ^ r * ((r.factorial : ℕ) : A) * powerSum A s u (r + 1)) := by ring

/-- The Bell side satisfies the same differential equation. -/
theorem derivative_egfA_bell_complete (x : ℕ → A) :
    d⁄dX A (egfA A (Bell.complete x)) =
      egfA A (Bell.complete x) * d⁄dX A (egfA A x) := by
  rw [derivative_egfA, derivative_egfA, egfA_mul]
  congr 1
  funext n
  rw [Bell.shift_apply, Bell.complete_succ]

/-- **The two sides agree:** `∏_i (1 + u_i t) = ∑_n B_n(x) t^n/n!`. -/
theorem elemSeries_eq_egfA_bell_complete (s : Finset ι) (u : ι → A) :
    elemSeries A s u = egfA A (Bell.complete (newtonWeight A s u)) := by
  set x := newtonWeight A s u with hx
  set W := d⁄dX A (egfA A x) with hW
  have hE : d⁄dX A (elemSeries A s u) = elemSeries A s u * W := by
    rw [derivative_elemSeries, logDerivSeries_eq_derivative_egfA]
  have hB : d⁄dX A (egfA A (Bell.complete x)) = egfA A (Bell.complete x) * W :=
    derivative_egfA_bell_complete A x
  have hD : d⁄dX A (elemSeries A s u - egfA A (Bell.complete x)) =
      (elemSeries A s u - egfA A (Bell.complete x)) * W := by
    rw [map_sub, hE, hB, sub_mul]
  have h0 : constantCoeff (elemSeries A s u - egfA A (Bell.complete x)) = 0 := by
    rw [map_sub, constantCoeff_elemSeries, constantCoeff_egfA, Bell.complete_zero, sub_self]
  have := eq_zero_of_derivative_eq_mul (A := A) hD h0
  rwa [sub_eq_zero] at this

/-- The coefficients of `E` are the elementary symmetric functions. -/
theorem coeff_elemSeries (s : Finset ι) (u : ι → A) (n : ℕ) :
    coeff n (elemSeries A s u) = ∑ t ∈ s.powersetCard n, ∏ i ∈ t, u i := by
  classical
  have hcomm : elemSeries A s u = ∏ i ∈ s, (PowerSeries.C (u i) * X + 1) := by
    rw [elemSeries]
    exact Finset.prod_congr rfl fun i _ => add_comm _ _
  rw [hcomm, Finset.prod_add, map_sum, Finset.powersetCard_eq_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hterm : (∏ i ∈ t, PowerSeries.C (u i) * X) * ∏ i ∈ s \ t, (1 : A⟦X⟧)
      = PowerSeries.C (∏ i ∈ t, u i) * X ^ t.card := by
    rw [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib, Finset.prod_const,
      ← map_prod]
  rw [hterm, coeff_C_mul, coeff_X_pow]
  by_cases h : t.card = n
  · rw [if_pos h.symm, if_pos h, mul_one]
  · rw [if_neg (fun hc : n = t.card => h hc.symm), if_neg h, mul_zero]

/-- **Elementary symmetric functions through the complete Bell polynomials:**
`e_n = (1/n!) B_n(p_1, -1! p_2, 2! p_3, …)`. -/
theorem esymm_eq_bell_complete (s : Finset ι) (u : ι → A) (n : ℕ) :
    ∑ t ∈ s.powersetCard n, ∏ i ∈ t, u i =
      algebraMap ℚ A (1 / n.factorial) * Bell.complete (newtonWeight A s u) n := by
  rw [← coeff_elemSeries, elemSeries_eq_egfA_bell_complete, coeff_egfA]

/-- The same, with Mathlib's `Multiset.esymm` on the left. -/
theorem multiset_esymm_eq_bell_complete (s : Finset ι) (u : ι → A) (n : ℕ) :
    (s.val.map u).esymm n =
      algebraMap ℚ A (1 / n.factorial) * Bell.complete (newtonWeight A s u) n := by
  rw [Finset.esymm_map_val, ← esymm_eq_bell_complete]

/-- **The sign variant:** `e_n = ((-1)^n/n!) B_n(-p_1, -1! p_2, …, -(n-1)! p_n)`, from the
weighted homogeneity of the Bell polynomials. -/
theorem esymm_eq_neg_bell_complete (s : Finset ι) (u : ι → A) (n : ℕ) :
    ∑ t ∈ s.powersetCard n, ∏ i ∈ t, u i =
      (-1 : A) ^ n * algebraMap ℚ A (1 / n.factorial) *
        Bell.complete (fun r => if r = 0 then 0 else -(((r - 1).factorial : ℕ) : A) *
          powerSum A s u r) n := by
  have hw : (fun r => if r = 0 then 0 else -(((r - 1).factorial : ℕ) : A) *
      powerSum A s u r) = fun r => (-1 : A) ^ r * newtonWeight A s u r := by
    funext r
    rcases eq_or_ne r 0 with rfl | hr
    · rw [if_pos rfl, newtonWeight, if_pos rfl, mul_zero]
    · obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
      rw [if_neg (Nat.succ_ne_zero m), newtonWeight, if_neg (Nat.succ_ne_zero m),
        Nat.add_sub_cancel]
      have hsq : (-1 : A) ^ (m + 1) * (-1 : A) ^ m = -1 := by
        rw [← pow_add, show m + 1 + m = 2 * m + 1 by ring, pow_succ, pow_mul]
        norm_num
      calc -((m.factorial : ℕ) : A) * powerSum A s u (m + 1)
          = ((-1 : A) ^ (m + 1) * (-1 : A) ^ m) *
              (((m.factorial : ℕ) : A) * powerSum A s u (m + 1)) := by rw [hsq]; ring
        _ = (-1 : A) ^ (m + 1) *
              ((-1 : A) ^ m * ((m.factorial : ℕ) : A) * powerSum A s u (m + 1)) := by ring
  rw [hw, esymm_eq_bell_complete]
  have hhom : Bell.complete (fun r => (-1 : A) ^ r * newtonWeight A s u r) n =
      (-1 : A) ^ n * Bell.complete (newtonWeight A s u) n := by
    rw [bell_complete_eq_sum_partialBell, bell_complete_eq_sum_partialBell, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [partialBell_pow_mul]
  rw [hhom]
  have hsqn : (-1 : A) ^ n * (-1 : A) ^ n = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc algebraMap ℚ A (1 / n.factorial) * Bell.complete (newtonWeight A s u) n
      = ((-1 : A) ^ n * (-1 : A) ^ n) *
          (algebraMap ℚ A (1 / n.factorial) * Bell.complete (newtonWeight A s u) n) := by
        rw [hsqn, one_mul]
    _ = (-1 : A) ^ n * algebraMap ℚ A (1 / n.factorial) *
          ((-1 : A) ^ n * Bell.complete (newtonWeight A s u) n) := by ring

end Symmetric

end Fabius
