import FabiusFunction.QPochhammerInfinite
import FabiusFunction.RvachevPochhammerFactorization
import Mathlib.Analysis.Analytic.Order

/-!
# Entire complex q-Pochhammer products

For every strict complex contraction `q`, this module promotes the infinite
q-Pochhammer product

`(a;q)_∞ = ∏' j : ℕ, (1 - a * q ^ j)`

from pointwise convergence to a locally uniformly convergent entire function
of `a`.  Its zero set is exactly the set detected by the displayed factors,
in a division-free form that includes the degenerate nome `q = 0`.  Each of
those zeros is simple.

The generic symbol `qPochhammerInfIn` now provides all of these analytic
facts, including actual derivative nonvanishing and analytic order one at raw
factor zeros.  Since `complexQPochhammerInf` is definitionally its complex
specialization, this module is a compatibility layer for the original four
declaration names used by the geometric-sinc factorization literature.  No
analytic product or zero-cofactor argument is reproved here.

## Main results

* `hasProdLocallyUniformly_complexQPochhammerInf` gives locally uniform
  convergence on the whole complex plane.
* `complexQPochhammerInf_differentiable` proves that `(·;q)_∞` is entire.
* `complexQPochhammerInf_eq_zero_iff` gives the exact factor-zero locus,
  without dividing by a power of `q`.
* `complexQPochhammerInf_eq_zero_iff_eq_inv_pow` rewrites that locus as the
  usual lattice `a = (q ^ j)⁻¹` when `q ≠ 0`.
* `analyticOrderAt_complexQPochhammerInf_of_eq_zero` proves that every zero
  has analytic order one, including the unique zero at `a = 1` when `q = 0`.
-/

set_option autoImplicit false

open Topology

namespace Fabius

noncomputable section

-- Keep the analytic product API on the standard noncomputable complex
-- C-star-algebra hierarchy, as in `RvachevPochhammerFactorization`.
attribute [-instance] Complex.commRing

private theorem complexQPochhammerInf_eq_qPochhammerInfIn (a q : ℂ) :
    complexQPochhammerInf a q = qPochhammerInfIn a q := rfl

/-- For `‖q‖ < 1`, the factors defining `(a;q)_∞` converge locally
uniformly as functions of `a` on the whole complex plane. -/
theorem hasProdLocallyUniformly_complexQPochhammerInf
    (q : ℂ) (hq : ‖q‖ < 1) :
    HasProdLocallyUniformly
      (fun (j : ℕ) (a : ℂ) => 1 - a * q ^ j)
      (fun a : ℂ => complexQPochhammerInf a q) := by
  simpa only [complexQPochhammerInf_eq_qPochhammerInfIn] using
    (hasProdLocallyUniformly_qPochhammerInfIn (𝕜 := ℂ) hq)

/-- For every strict complex contraction `q`, the function
`a ↦ (a;q)_∞` is entire. -/
theorem complexQPochhammerInf_differentiable
    (q : ℂ) (hq : ‖q‖ < 1) :
    Differentiable ℂ (fun a : ℂ => complexQPochhammerInf a q) := by
  simpa only [complexQPochhammerInf_eq_qPochhammerInfIn] using
    differentiable_qPochhammerInfIn hq

/-- The infinite complex q-Pochhammer product vanishes exactly when one of
its displayed factors vanishes.  The factor-zero form is intentional: it
remains correct for the degenerate strict contraction `q = 0`. -/
theorem complexQPochhammerInf_eq_zero_iff
    (a q : ℂ) (hq : ‖q‖ < 1) :
    complexQPochhammerInf a q = 0 ↔
      ∃ j : ℕ, 1 - a * q ^ j = 0 := by
  have hzero := tprod_scaled_eq_zero_iff
    (fun z : ℂ => 1 - z) (fun j : ℕ => q ^ j)
    (summable_norm_qpow q hq) one_sub_sub_one_isBigO a
  simpa only [smul_eq_mul, mul_comm, complexQPochhammerInf] using hzero

/-- For a nonzero strict contraction, the zeros of `(a;q)_∞` are exactly
the reciprocal powers of `q`.  The nonzero hypothesis is essential for this
division-based spelling; the preceding factor-zero theorem also covers
`q = 0`. -/
theorem complexQPochhammerInf_eq_zero_iff_eq_inv_pow
    (a q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    complexQPochhammerInf a q = 0 ↔
      ∃ j : ℕ, a = (q ^ j)⁻¹ := by
  rw [complexQPochhammerInf_eq_zero_iff a q hq]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    have hqj : q ^ j ≠ 0 := pow_ne_zero j hq0
    apply mul_right_cancel₀ hqj
    rw [(sub_eq_zero.mp hj).symm, inv_mul_cancel₀ hqj]
  · rintro ⟨j, rfl⟩
    refine ⟨j, sub_eq_zero.mpr ?_⟩
    exact (inv_mul_cancel₀ (pow_ne_zero j hq0)).symm

set_option maxHeartbeats 400000 in
private theorem complexQPochhammerInf_eq_finite_mul_shift
    (a q : ℂ) (hq : ‖q‖ < 1) (n : ℕ) :
    complexQPochhammerInf a q =
      finiteQPochhammerIn a q n *
        complexQPochhammerInf (a * q ^ n) q := by
  have htail : HasProd
      (fun k : ℕ => 1 - a * q ^ (k + n))
      (complexQPochhammerInf (a * q ^ n) q) := by
    refine (hasProd_complexQPochhammerInf (a * q ^ n) hq).congr_fun ?_
    intro k
    rw [pow_add]
    ring
  rw [finiteQPochhammerIn]
  exact htail.prod_range_mul.tprod_eq

private theorem complexQPochhammerFactor_zero_index_unique
    (a q : ℂ) (hq : ‖q‖ < 1) {j k : ℕ}
    (hj : 1 - a * q ^ j = 0) (hk : 1 - a * q ^ k = 0) :
    j = k := by
  have haj : a * q ^ j = 1 := (sub_eq_zero.mp hj).symm
  have hak : a * q ^ k = 1 := (sub_eq_zero.mp hk).symm
  by_cases hq0 : q = 0
  · subst q
    have hj0 : j = 0 := by
      by_contra hjne
      rw [zero_pow hjne, mul_zero] at haj
      exact zero_ne_one haj
    have hk0 : k = 0 := by
      by_contra hkne
      rw [zero_pow hkne, mul_zero] at hak
      exact zero_ne_one hak
    exact hj0.trans hk0.symm
  · have ha0 : a ≠ 0 := by
      intro ha
      rw [ha, zero_mul] at haj
      exact zero_ne_one haj
    have hpows : q ^ j = q ^ k := by
      apply mul_left_cancel₀ ha0
      exact haj.trans hak.symm
    apply pow_right_injective₀ (norm_pos_iff.mpr hq0) (ne_of_lt hq)
    simpa only [norm_pow] using congrArg norm hpows

private theorem complexQPochhammerInf_eq_sub_mul_cofactor
    (a q : ℂ) (hq : ‖q‖ < 1) {j : ℕ}
    (hj : 1 - a * q ^ j = 0) (z : ℂ) :
    complexQPochhammerInf z q =
      (z - a) *
        ((-q ^ j) * finiteQPochhammerIn z q j *
          complexQPochhammerInf (z * q ^ (j + 1)) q) := by
  have haj : a * q ^ j = 1 := (sub_eq_zero.mp hj).symm
  have hfactor : 1 - z * q ^ j = (z - a) * (-q ^ j) := by
    calc
      1 - z * q ^ j = a * q ^ j - z * q ^ j := by rw [haj]
      _ = (z - a) * (-q ^ j) := by ring
  rw [complexQPochhammerInf_eq_finite_mul_shift z q hq (j + 1),
    finiteQPochhammerIn_succ, hfactor]
  ring

/-- Every zero of the entire function `a ↦ (a;q)_∞` is simple.  The result
uses the raw factor-zero hypothesis and therefore includes `q = 0`, where
the only zero is the factor at index zero. -/
theorem analyticOrderAt_complexQPochhammerInf_of_eq_zero
    (a q : ℂ) (hq : ‖q‖ < 1)
    (ha : complexQPochhammerInf a q = 0) :
    analyticOrderAt (fun z : ℂ => complexQPochhammerInf z q) a = 1 := by
  have ha' : qPochhammerInfIn a q = 0 := by
    simpa only [complexQPochhammerInf_eq_qPochhammerInfIn] using ha
  simpa only [complexQPochhammerInf_eq_qPochhammerInfIn] using
    analyticOrderAt_qPochhammerInfIn_of_eq_zero a q hq ha'

end

end Fabius
