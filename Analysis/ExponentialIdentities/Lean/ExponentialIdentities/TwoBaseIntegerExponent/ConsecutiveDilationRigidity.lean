import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Consecutive-dilation rigidity

A `q`-monomial polynomial that vanishes at `q` consecutive diagonal dilations
`(2^n X, 3^n Y)` (`n = n₀, …, n₀ + q - 1`) of one positive point is identically zero.
On the curve the monomial `X^i Y^j` rescales by the eigenvalue `(2^i 3^j)^n`, so the
hypothesis is a homogeneous Vandermonde system in `q` distinct positive eigenvalues; the
kernel core `eq_zero_of_consecutive_vanishing` eliminates the largest node by the shifted
difference `R_{k+1} - x_Q R_k` and inducts.  Consequently no fixed sparse trap can retire
a persistent normalized orbit point: traps must move with the block.  This is the
finite-algebra heart of the trap-lattice report's dilation-rigidity theorem, and the
`q`-shift upgrade of the one-shift toric semi-invariant rigidity
(`ToricMonomialRigidity`).
-/

namespace LeanProofs.TwoBaseIntegerExponent.DilationRigidity

open Finset

/-- **Vandermonde elimination.**  If `x 0, …, x (q-1)` are positive and strictly
increasing and the exponential sums `∑ e, d e · (x e)^(n₀+k)` vanish for
`k = 0, …, q-1`, then every `d e` vanishes. -/
theorem eq_zero_of_consecutive_vanishing :
    ∀ (q : ℕ) (x d : ℕ → ℚ) (n₀ : ℕ),
      (∀ e, e < q → 0 < x e) →
      (∀ e f, e < f → f < q → x e < x f) →
      (∀ k, k < q → ∑ e ∈ range q, d e * x e ^ (n₀ + k) = 0) →
      ∀ e, e < q → d e = 0 := by
  intro q
  induction q with
  | zero =>
    intro x d n₀ _ _ _ e he
    omega
  | succ Q ih =>
    intro x d n₀ hpos hmono hvan
    -- Eliminate the largest node: the shifted difference kills index `Q`.
    have hvan' : ∀ k, k < Q →
        ∑ e ∈ range Q, (d e * (x e - x Q)) * x e ^ (n₀ + k) = 0 := by
      intro k hk
      have h1 := hvan (k + 1) (by omega)
      have h2 := hvan k (by omega)
      have expand : ∑ e ∈ range (Q + 1), (d e * (x e - x Q)) * x e ^ (n₀ + k)
          = (∑ e ∈ range (Q + 1), d e * x e ^ (n₀ + (k + 1)))
            + (-(x Q)) * ∑ e ∈ range (Q + 1), d e * x e ^ (n₀ + k) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun e _ => ?_
        have hexp : n₀ + (k + 1) = (n₀ + k) + 1 := by omega
        rw [hexp, pow_succ]
        ring
      have key : ∑ e ∈ range (Q + 1), (d e * (x e - x Q)) * x e ^ (n₀ + k) = 0 := by
        rw [expand, h1, h2]
        ring
      rw [Finset.sum_range_succ] at key
      simpa using key
    have hall : ∀ e, e < Q → d e = 0 := by
      intro e he
      have h0 := ih x (fun e => d e * (x e - x Q)) n₀
        (fun e he' => hpos e (by omega))
        (fun e f hef hf => hmono e f hef (by omega))
        hvan' e he
      have hlt : x e < x Q := hmono e Q he (by omega)
      have hne : x e - x Q ≠ 0 := by linarith
      rcases mul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h hne
    intro e he
    rcases Nat.lt_or_ge e Q with heQ | heQ
    · exact hall e heQ
    · have heq : e = Q := by omega
      rw [heq]
      have h0 := hvan 0 (by omega)
      rw [Finset.sum_range_succ] at h0
      have hz : ∑ f ∈ range Q, d f * x f ^ (n₀ + 0) = 0 :=
        Finset.sum_eq_zero fun f hf => by
          rw [hall f (Finset.mem_range.mp hf)]
          ring
      rw [hz, zero_add] at h0
      have hxQ : x Q ^ (n₀ + 0) ≠ 0 :=
        pow_ne_zero _ (ne_of_gt (hpos Q (by omega)))
      rcases mul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h hxQ

/-- **Consecutive-dilation rigidity.**  A `q`-monomial pattern
`P(X,Y) = ∑ c_e X^{i_e} Y^{j_e}` vanishing at `q` consecutive diagonal dilations
`(2^n X, 3^n Y)` of a positive point `(X, Y)` is identically zero (eigenvalues
`2^{i_e} 3^{j_e}` listed in increasing order).  No fixed sparse trap can hold a
persistent normalized orbit point. -/
theorem consecutive_dilation_rigidity {q : ℕ} {i j : ℕ → ℕ} {c : ℕ → ℚ} {X Y : ℚ}
    (hX : 0 < X) (hY : 0 < Y) (n₀ : ℕ)
    (hmono : ∀ e f, e < f → f < q →
      (2 : ℚ) ^ i e * 3 ^ j e < (2 : ℚ) ^ i f * 3 ^ j f)
    (hvan : ∀ k, k < q → ∑ e ∈ range q,
      (c e * X ^ i e * Y ^ j e) * ((2 : ℚ) ^ i e * 3 ^ j e) ^ (n₀ + k) = 0) :
    ∀ e, e < q → c e = 0 := by
  intro e he
  have hpos : ∀ e, e < q → (0 : ℚ) < 2 ^ i e * 3 ^ j e := by
    intro f _
    positivity
  have h0 := eq_zero_of_consecutive_vanishing q
    (fun e => (2 : ℚ) ^ i e * 3 ^ j e)
    (fun e => c e * X ^ i e * Y ^ j e) n₀ hpos hmono hvan e he
  have hXY : X ^ i e * Y ^ j e ≠ 0 := by positivity
  have : c e * (X ^ i e * Y ^ j e) = 0 := by
    calc c e * (X ^ i e * Y ^ j e) = c e * X ^ i e * Y ^ j e := by ring
      _ = 0 := h0
  rcases mul_eq_zero.mp this with h | h
  · exact h
  · exact absurd h hXY

end LeanProofs.TwoBaseIntegerExponent.DilationRigidity
