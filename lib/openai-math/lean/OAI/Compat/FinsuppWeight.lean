/-
Added for ProveIt (not an upstream file; distributed under Apache-2.0).
Express a finitely supported weight as a sum over its finite index type.
This local proof uses Mathlib v4.32.0's existing finite-sum theorem; no
upstream proof text is copied.
-/
import Mathlib.Data.Finsupp.Weight

set_option autoImplicit false
open scoped BigOperators

theorem Finsupp.weight_eq_sum {σ R M : Type*} [Fintype σ] [Semiring R]
    [AddCommMonoid M] [Module R M] (w : σ → M) (f : σ →₀ R) :
    Finsupp.weight w f = ∑ i, f i • w i := by
  rw [Finsupp.weight_apply]
  exact Finsupp.sum_fintype _ _ (fun i => zero_smul R (w i))
