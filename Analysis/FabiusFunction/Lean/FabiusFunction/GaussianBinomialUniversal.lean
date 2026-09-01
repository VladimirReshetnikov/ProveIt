import FabiusFunction.FiniteQBinomialCore
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# The universal Gaussian coefficient

The Gaussian coefficient `[n,k]_q` is defined by the `q`-Pascal recurrence in
every semiring, so it is the image of one **universal polynomial**
`[n,k]_X ∈ ℕ[X]` under evaluation at `q`.  In particular `[n,k]_q` is a
polynomial in `q` with natural-number coefficients: polynomiality and
positivity are one and the same statement here, and both are immediate from
the naturality `φ [n,k]_q = [n,k]_{φ q}` of the recurrence.

## Main declarations

* `gaussianBinomial_eq_eval₂_universal`: `[n,k]_q = ([n,k]_X)(q)` for the
  universal polynomial `[n,k]_X ∈ ℕ[X]`.
* `gaussianBinomial_eq_eval_map_universal`: the same with the coefficients
  mapped into `R` first.
-/

set_option autoImplicit false

namespace Fabius

open Polynomial

variable {R : Type*} [CommSemiring R]

/-- **Polynomiality and positivity**: `[n,k]_q` is the value at `q` of the universal
polynomial `[n,k]_X ∈ ℕ[X]`, whose coefficients are natural numbers. -/
theorem gaussianBinomial_eq_eval₂_universal (q : R) (n k : ℕ) :
    gaussianBinomial q n k =
      (gaussianBinomial (X : ℕ[X]) n k).eval₂ (Nat.castRingHom R) q := by
  have h := map_gaussianBinomial (eval₂RingHom (Nat.castRingHom R) q) (X : ℕ[X]) n k
  rw [coe_eval₂RingHom, eval₂_X] at h
  exact h.symm

/-- The universal polynomial, with coefficients cast into `R`, evaluates to `[n,k]_q`. -/
theorem gaussianBinomial_eq_eval_map_universal (q : R) (n k : ℕ) :
    gaussianBinomial q n k =
      ((gaussianBinomial (X : ℕ[X]) n k).map (Nat.castRingHom R)).eval q := by
  rw [eval_map, gaussianBinomial_eq_eval₂_universal]

end Fabius
