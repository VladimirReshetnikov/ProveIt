import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace BoundaryConservation

/-- Exact weighted conservation for a finite sequence of carry equations.
`carry i` is the incoming carry at position `i`; `carry (i+1)` the outgoing one. -/
theorem weighted_conservation (ρ : ℕ) (raw digits carry : ℕ → ℕ) (n : ℕ)
    (hrec : ∀ i < n, raw i + carry i = digits i + ρ * carry (i+1)) :
    (∑ i ∈ Finset.range n, raw i * ρ^i) + carry 0 =
      (∑ i ∈ Finset.range n, digits i * ρ^i) + carry n * ρ^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprev := ih (fun i hi => hrec i (by omega))
    have hlast := congrArg (fun x : ℕ => x * ρ^n) (hrec n (by omega))
    simp only [Finset.sum_range_succ, pow_succ]
    nlinarith only [hprev, hlast]

/-- A shared boundary carry cancels exactly between two normalizations.
No coefficient, digit, modulus, positivity or upper-bound hypothesis is needed. -/
theorem increment_of_equal_boundary (ρ : ℕ)
    (raw raw' digits digits' carry carry' : ℕ → ℕ) (n δ : ℕ)
    (hrec : ∀ i < n, raw i + carry i = digits i + ρ * carry (i+1))
    (hrec' : ∀ i < n, raw' i + carry' i = digits' i + ρ * carry' (i+1))
    (hin : carry 0 = carry' 0) (hout : carry n = carry' n)
    (hraw : (∑ i ∈ Finset.range n, raw' i * ρ^i) =
      (∑ i ∈ Finset.range n, raw i * ρ^i) + δ) :
    (∑ i ∈ Finset.range n, digits' i * ρ^i) =
      (∑ i ∈ Finset.range n, digits i * ρ^i) + δ := by
  have h := weighted_conservation ρ raw digits carry n hrec
  have h' := weighted_conservation ρ raw' digits' carry' n hrec'
  rw [← hin, ← hout, hraw] at h'
  omega

/-- The exact position inequalities needed for the actual dummy stencil.
There is no coefficient-mass estimate or radix in this arithmetic statement. -/
theorem actual_dummy_support {N j s e : ℕ}
    (hnext : j+1 < N) (htime : j+s < N) (he : e ≤ 2020) :
    (977 + 2011*j) + e < N*2011 ∧
      (977 + 2011*j) + 2011*s < N*2011 := by omega

/-- A polynomial with exponents below the cyclic length has the same ordinary
and folded evaluation; the coefficient sizes are unrestricted. -/
theorem unfolded_weighted_increment {ι : Type*} [Fintype ι]
    (ρ n j : ℕ) (a e : ι → ℕ) (hnoWrap : ∀ i, j + e i < n) :
    (∑ i, a i * ρ^((j+e i)%n)) = (∑ i, a i * ρ^(e i)) * ρ^j := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.mod_eq_of_lt (hnoWrap i), pow_add]
  ring

#print axioms weighted_conservation
#print axioms increment_of_equal_boundary
#print axioms actual_dummy_support
#print axioms unfolded_weighted_increment
end BoundaryConservation
