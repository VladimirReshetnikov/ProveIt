import FabiusFunction.ExponentialRiordan

/-!
# The Stirling transforms as substitutions of exponential generating functions

If `A(t) = ∑_n a_n t^n/n!` then

`A(e^t - 1) = ∑_n (∑_k S(n,k) a_k) t^n/n!` and `A(log(1+t)) = ∑_n (∑_k s(n,k) a_k) t^n/n!`,

the second-kind and the signed first-kind Stirling transforms.  Both are the
action of the exponential Riordan arrays `[1, e^t - 1]` and `[1, log(1+t)]`.

## Main results

* `egfA_subst_exp_sub_one`, `egfA_subst_log`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- **The Stirling transform of the second kind as a substitution:**
`A(e^t - 1) = ∑_n (∑_{k ≤ n} S(n,k) a_k) t^n/n!`. -/
theorem egfA_subst_exp_sub_one (a : ℕ → A) :
    (egfA A a).subst (exp A - 1) =
      egfA A fun n => ∑ k ∈ Finset.range (n + 1), (Nat.stirlingSecond n k : A) * a k := by
  have h := expRiordan_action A (f := exp A - 1) (by simp [constantCoeff_exp]) 1 a
  rw [one_mul] at h
  rw [h]
  congr 1
  funext n
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [expRiordan_one_exp_sub_one]

/-- **The signed Stirling transform of the first kind as a substitution:**
`A(log(1+t)) = ∑_n (∑_{k ≤ n} s(n,k) a_k) t^n/n!`. -/
theorem egfA_subst_log (a : ℕ → A) :
    (egfA A a).subst (log A) =
      egfA A fun n => ∑ k ∈ Finset.range (n + 1),
        algebraMap ℚ A (signedStirlingFirst n k) * a k := by
  have h := expRiordan_action A (f := log A) constantCoeff_log 1 a
  rw [one_mul] at h
  rw [h]
  congr 1
  funext n
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [expRiordan_one_log]

end Fabius
