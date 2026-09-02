import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.LinearCombination

/-!
# Certificates: telescoping, recurrence uniqueness, and the polynomial identity principle

Three small, completely general tools behind certified `q`-identities.

* **Finite telescoping certificate.**  If `∑_j A_j T_j(k) = G(k+1) - G(k)` on the summation
  range and `G` vanishes at both ends, then `∑_j A_j ∑_k T_j(k) = 0`: the certified recurrence
  for the sums.
* **Identity certification.**  Two sequences satisfying the same linear recurrence of order `r`
  with nonvanishing leading coefficient, and agreeing at the first `r` values, agree everywhere.
* **Polynomial identity principle.**  If `p₁/q₁ = p₂/q₂` at infinitely many points of a field
  where the denominators are nonzero, then `p₁ q₂ = p₂ q₁` as polynomials; conversely the cleared
  identity specializes safely to every point where the denominators are nonzero.

## Main declarations

* `telescoping_certificate`, `telescoping_certificate_Ico`.
* `eq_of_recurrence`.
* `rational_identity_principle`, `safe_specialization`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Finset Polynomial

section Telescoping

variable {R : Type*} [CommRing R]

/-- **Finite telescoping certificate** on `k < N`: if `∑_{j≤r} A_j T_j(k) = G(k+1) - G(k)` for
`k < N` and `G 0 = G N = 0`, then `∑_{j≤r} A_j ∑_{k<N} T_j(k) = 0`. -/
theorem telescoping_certificate {r N : ℕ} (A : ℕ → R) (T : ℕ → ℕ → R) (G : ℕ → R)
    (h : ∀ k < N, ∑ j ∈ range (r + 1), A j * T j k = G (k + 1) - G k)
    (h0 : G 0 = 0) (hN : G N = 0) :
    ∑ j ∈ range (r + 1), A j * ∑ k ∈ range N, T j k = 0 := by
  calc ∑ j ∈ range (r + 1), A j * ∑ k ∈ range N, T j k
      = ∑ k ∈ range N, ∑ j ∈ range (r + 1), A j * T j k := by
        simp_rw [mul_sum]
        exact sum_comm
    _ = ∑ k ∈ range N, (G (k + 1) - G k) := sum_congr rfl fun k hk => h k (mem_range.mp hk)
    _ = G N - G 0 := sum_range_sub G N
    _ = 0 := by rw [h0, hN, sub_zero]

/-- **Finite telescoping certificate** on `L ≤ k < U`. -/
theorem telescoping_certificate_Ico {r L U : ℕ} (hLU : L ≤ U) (A : ℕ → R) (T : ℕ → ℕ → R)
    (G : ℕ → R) (h : ∀ k, L ≤ k → k < U → ∑ j ∈ range (r + 1), A j * T j k = G (k + 1) - G k)
    (hL : G L = 0) (hU : G U = 0) :
    ∑ j ∈ range (r + 1), A j * ∑ k ∈ Ico L U, T j k = 0 := by
  simp_rw [sum_Ico_eq_sum_range]
  refine telescoping_certificate (N := U - L) A (fun j k => T j (L + k)) (fun k => G (L + k))
    (fun k hk => ?_) (by simpa using hL) (by rwa [Nat.add_sub_cancel' hLU])
  rw [← add_assoc]
  exact h (L + k) (Nat.le_add_right L k) (by omega)

end Telescoping

section Recurrence

variable {K : Type*} [Field K]

/-- **Identity certification**: sequences satisfying the same linear recurrence
`∑_{j≤r} A_j(n) S(n+j) = 0` with `A_r(n) ≠ 0`, and agreeing at `S 0, …, S (r-1)`, agree
everywhere. -/
theorem eq_of_recurrence {r : ℕ} (A : ℕ → ℕ → K) (hA : ∀ n, A r n ≠ 0) (S T : ℕ → K)
    (hS : ∀ n, ∑ j ∈ range (r + 1), A j n * S (n + j) = 0)
    (hT : ∀ n, ∑ j ∈ range (r + 1), A j n * T (n + j) = 0)
    (hinit : ∀ i < r, S i = T i) : ∀ n, S n = T n := by
  intro n
  refine Nat.strong_induction_on n fun n ih => ?_
  rcases lt_or_ge n r with hn | hn
  · exact hinit n hn
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + r := ⟨n - r, by omega⟩
    have hS' := hS m
    have hT' := hT m
    rw [sum_range_succ] at hS' hT'
    have hsum : ∑ j ∈ range r, A j m * S (m + j) = ∑ j ∈ range r, A j m * T (m + j) :=
      sum_congr rfl fun j hj => by rw [ih (m + j) (by have := mem_range.mp hj; omega)]
    have hlead : A r m * S (m + r) = A r m * T (m + r) := by
      linear_combination hS' - hT' - hsum
    exact mul_left_cancel₀ (hA m) hlead

end Recurrence

section Identity

variable {K : Type*} [Field K]

/-- **Polynomial identity principle** for quotients: if `p₁/q₁ = p₂/q₂` at infinitely many points
where both denominators are nonzero, then `p₁ q₂ = p₂ q₁` as polynomials. -/
theorem rational_identity_principle (p₁ q₁ p₂ q₂ : K[X])
    (h : {z : K | q₁.eval z ≠ 0 ∧ q₂.eval z ≠ 0 ∧
      p₁.eval z / q₁.eval z = p₂.eval z / q₂.eval z}.Infinite) :
    p₁ * q₂ = p₂ * q₁ := by
  refine eq_of_infinite_eval_eq _ _ (h.mono fun z hz => ?_)
  obtain ⟨h1, h2, h3⟩ := hz
  rw [Set.mem_setOf_eq, eval_mul, eval_mul]
  rwa [div_eq_div_iff h1 h2] at h3

/-- **Safe specialization**: the cleared identity `p₁ q₂ = p₂ q₁` specializes to
`p₁(z)/q₁(z) = p₂(z)/q₂(z)` at every `z` where the denominators are nonzero. -/
theorem safe_specialization {p₁ q₁ p₂ q₂ : K[X]} (h : p₁ * q₂ = p₂ * q₁) {z : K}
    (h1 : q₁.eval z ≠ 0) (h2 : q₂.eval z ≠ 0) :
    p₁.eval z / q₁.eval z = p₂.eval z / q₂.eval z := by
  rw [div_eq_div_iff h1 h2, ← eval_mul, ← eval_mul, h]

end Identity

end Fabius
