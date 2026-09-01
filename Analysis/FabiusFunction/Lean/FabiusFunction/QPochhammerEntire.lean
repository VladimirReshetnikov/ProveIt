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
  rw [complexQPochhammerInf_eq_qPochhammerInfIn,
    qPochhammerInfIn_eq_zero_iff a hq]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, sub_eq_zero.mpr hj.symm⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, (sub_eq_zero.mp hj).symm⟩

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
