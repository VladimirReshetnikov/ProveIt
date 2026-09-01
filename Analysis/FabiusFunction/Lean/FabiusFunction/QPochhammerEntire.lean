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

The historical complex symbol is definitionally the generic
`qPochhammerInfIn` specialized to `ℂ`; the convergence, regularity, and zero
theorems below reuse that general API. This module adds the analytic-order
statement.

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
* `analyticOrderAt_qPochhammerInfIn_of_eq_zero` gives the same conclusion
  directly for the generic symbol specialized to `ℂ`.
-/

set_option autoImplicit false

namespace Fabius

noncomputable section

-- Keep the analytic product API on the standard noncomputable complex
-- C-star-algebra hierarchy, as in `RvachevPochhammerFactorization`.
attribute [-instance] Complex.commRing

/-- For `‖q‖ < 1`, the factors defining `(a;q)_∞` converge locally
uniformly as functions of `a` on the whole complex plane. -/
theorem hasProdLocallyUniformly_complexQPochhammerInf
    (q : ℂ) (hq : ‖q‖ < 1) :
    HasProdLocallyUniformly
      (fun (j : ℕ) (a : ℂ) => 1 - a * q ^ j)
      (fun a : ℂ => complexQPochhammerInf a q) := by
  rw [show (fun a : ℂ => complexQPochhammerInf a q) =
      fun a : ℂ => qPochhammerInfIn a q from
    funext fun a => complexQPochhammerInf_eq_qPochhammerInfIn a q]
  exact hasProdLocallyUniformly_qPochhammerInfIn hq

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
  rw [complexQPochhammerInf_eq_qPochhammerInfIn,
    qPochhammerInfIn_eq_zero_iff a hq]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, sub_eq_zero.mpr hj.symm⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, (sub_eq_zero.mp hj).symm⟩

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

/-- Every zero of the entire function `a ↦ (a;q)_∞` is simple.  The result
uses the raw factor-zero hypothesis and therefore includes `q = 0`, where
the only zero is the factor at index zero. -/
theorem analyticOrderAt_complexQPochhammerInf_of_eq_zero
    (a q : ℂ) (hq : ‖q‖ < 1)
    (ha : complexQPochhammerInf a q = 0) :
    analyticOrderAt (fun z : ℂ => complexQPochhammerInf z q) a = 1 := by
  obtain ⟨j, hj⟩ := (complexQPochhammerInf_eq_zero_iff a q hq).mp ha
  have haj : a * q ^ j = 1 := (sub_eq_zero.mp hj).symm
  have hqj : q ^ j ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at haj
    exact zero_ne_one haj
  have hprefix : finiteQPochhammerIn a q j ≠ 0 := by
    rw [finiteQPochhammerIn, Finset.prod_ne_zero_iff]
    intro k hk hzero
    have hkj := complexQPochhammerFactor_zero_index_unique
      a q hq hj hzero
    have hlt : k < j := Finset.mem_range.mp hk
    omega
  have hshift : a * q ^ (j + 1) = q := by
    rw [pow_succ, ← mul_assoc, haj, one_mul]
  have htail :
      complexQPochhammerInf (a * q ^ (j + 1)) q ≠ 0 := by
    rw [complexQPochhammerInf_eq_qPochhammerInfIn, hshift]
    exact qPochhammerInfIn_self_ne_zero hq
  have hderiv :
      HasDerivAt (fun z : ℂ => complexQPochhammerInf z q)
        (-(q ^ j) *
          (finiteQPochhammerIn a q j *
            complexQPochhammerInf (a * q ^ (j + 1)) q)) a := by
    simpa only [complexQPochhammerInf_eq_qPochhammerInfIn] using
      hasDerivAt_qPochhammerInfIn_of_mul_pow_eq_one hq j haj
  have hderiv_ne :
      deriv (fun z : ℂ => complexQPochhammerInf z q) a ≠ 0 := by
    rw [hderiv.deriv]
    exact mul_ne_zero (neg_ne_zero.mpr hqj)
      (mul_ne_zero hprefix htail)
  exact ((complexQPochhammerInf_differentiable q hq).analyticAt a)
    |>.analyticOrderAt_eq_one_of_zero_deriv_ne_zero ha hderiv_ne

/-- Every zero of the generic infinite q-Pochhammer symbol specialized to
the complex numbers has analytic order one. This is the generic-name form of
the preceding theorem, transported across the definitional bridge between the
two symbols. -/
theorem analyticOrderAt_qPochhammerInfIn_of_eq_zero
    (a q : ℂ) (hq : ‖q‖ < 1)
    (ha : qPochhammerInfIn a q = 0) :
    analyticOrderAt (fun z : ℂ => qPochhammerInfIn z q) a = 1 := by
  have ha' : complexQPochhammerInf a q = 0 := by
    rw [complexQPochhammerInf_eq_qPochhammerInfIn]
    exact ha
  have hfun : (fun z : ℂ => qPochhammerInfIn z q) =
      fun z : ℂ => complexQPochhammerInf z q :=
    funext fun z => (complexQPochhammerInf_eq_qPochhammerInfIn z q).symm
  rw [hfun]
  exact analyticOrderAt_complexQPochhammerInf_of_eq_zero a q hq ha'

end

end Fabius
