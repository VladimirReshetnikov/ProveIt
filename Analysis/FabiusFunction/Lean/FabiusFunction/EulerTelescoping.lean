import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Euler's telescoping lemma

For `u_0, …, u_N` and `v_0, …, v_N` in a field, with `w_k = u_k - v_k` and
`w_0 v_1 ⋯ v_N ≠ 0`,

`∑_{k=0}^{N} (w_k/w_0) · (u_0 ⋯ u_{k-1})/(v_1 ⋯ v_k) = (1/w_0) · ((u_0 ⋯ u_N)/(v_1 ⋯ v_N) - v_0)`.

The `k`-th summand (`k ≥ 1`) is the difference of two consecutive values of
`u_0 ⋯ u_k/(v_1 ⋯ v_k)`, so the sum telescopes.  This is the engine behind the very-well-poised
summations (Jackson's `₈φ₇`, the `₆φ₅` sum).

## Main declarations

* `euler_telescoping`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- **Euler's telescoping lemma**: with `w_k = u_k - v_k`, `w_0 ≠ 0` and `v_1, …, v_N ≠ 0`,
`∑_{k=0}^{N} (w_k/w_0) · (∏_{i<k} u_i)/(∏_{i<k} v_{i+1}) = (1/w_0)((∏_{i≤N} u_i)/(∏_{i<N} v_{i+1}) - v_0)`. -/
theorem euler_telescoping {K : Type*} [Field K] (u v : ℕ → K) (h0 : u 0 - v 0 ≠ 0) :
    ∀ N : ℕ, (∀ i < N, v (i + 1) ≠ 0) →
      ∑ k ∈ range (N + 1), (u k - v k) / (u 0 - v 0) *
          ((∏ i ∈ range k, u i) / ∏ i ∈ range k, v (i + 1)) =
        1 / (u 0 - v 0) * ((∏ i ∈ range (N + 1), u i) / (∏ i ∈ range N, v (i + 1)) - v 0) := by
  intro N
  induction N with
  | zero =>
    intro _
    simp only [zero_add, sum_range_one, prod_range_zero, prod_range_one, div_one]
    field_simp
  | succ N ih =>
    intro hv
    have hQ : ∏ i ∈ range N, v (i + 1) ≠ 0 :=
      prod_ne_zero_iff.mpr fun i hi => hv i (by simp at hi; omega)
    have hvN : v (N + 1) ≠ 0 := hv N (Nat.lt_succ_self N)
    rw [sum_range_succ, ih fun i hi => hv i (by omega), prod_range_succ (fun i => v (i + 1)) N,
      prod_range_succ u (N + 1)]
    field_simp
    ring

end Fabius
