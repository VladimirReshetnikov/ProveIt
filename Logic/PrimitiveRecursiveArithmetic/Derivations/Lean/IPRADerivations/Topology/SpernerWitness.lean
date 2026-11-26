import IPRADerivations.Foundations.BoundedReflection
import IPRADerivations.Core.OrderCertificates

/-!
# The one-dimensional Sperner cell, found by bounded search

Packet: `topology/approximate_brouwer_ipra`, `parity.tex`, "Finite Sperner lemma": "the number of cells with
all `d + 1` colors is odd. The first such cell in word order can therefore be found by scanning at most `N^d`
words." In dimension one the scan needs no parity: for a colouring `b(i, x)` of the grid `0, …, N` (`N` an
object-level term) with `b(0, x) = 0` and `b(N, x) ≠ 0`, the first vertex of nonzero colour is a primitive
recursive term, and the cell ending there carries both colours:

* `C b N x`: the first `i ≤ N` with `b(i, x) ≠ 0`;
* `first_change`: `0 < C ≤ N` and `b(C, x) ≠ 0`;
* `before_change`: `b(j, x) = 0` for every `j < C`;
* `sperner_cell`: the cell `[C − 1, C]` has colours `b(C − 1, x) = 0` and `b(C, x) ≠ 0`.

The parity statement in dimension one is `Topology/Sperner`; the approximate fixed point built on such a cell
is `Topology/BrouwerInterval`.
-/

namespace LeanProofs.IPRA.Topology.SpernerWitness

open_ipra
open LeanProofs.IPRA.Foundations.BoundedReflection (exB wit ex_intro ex_elim ex_least)

variable {n : ℕ} {Γ : List (Fm PTm n)}

variable (b : PTm 2)

/-- The first vertex of nonzero colour. -/
abbrev C (N x : PTm n) : PTm n := wit b (succ N) x

/-- The scan succeeds strictly inside the grid: `0 < C ≤ N` and `b(C) ≠ 0`. -/
theorem first_change (N x : PTm n) (h0 : Γ ⊢[PRAAx] inst2 b zero x ≐ zero)
    (hN : Γ ⊢[PRAAx] neg (inst2 b N x ≐ zero)) :
    Γ ⊢[PRAAx] (lt zero (C b N x) ⋏ le (C b N x) N) ⋏ neg (inst2 b (C b N x) x ≐ zero) := by
  have hex := ex_intro b hN (le_refl (succ N))
  have w := ex_elim b hex
  have a₁ : Γ ⊢[PRAAx] le (succ (C b N x)) (succ N) := Prf.andE₁ w
  have a₂ := Prf.andE₂ w
  refine .andI (.andI ?_ ?_) a₂
  · refine .orE (lt_or_le zero (C b N x)) Prf.hyp0 ?_
    have hz : (le (C b N x) zero :: Γ) ⊢[PRAAx] le (C b N x) zero := Prf.hyp0
    have eW : (le (C b N x) zero :: Γ) ⊢[PRAAx] C b N x ≐ zero := le_antisymm hz (zero_le _)
    exact .botE _ (.impE a₂.wk ((congrInst2 b eW (.eqRefl x)).eqTrans h0.wk))
  · ipra_le sl a₁

/-- Before the change every vertex has colour zero. -/
theorem before_change {N x j : PTm n} (hj : Γ ⊢[PRAAx] lt j (C b N x)) : Γ ⊢[PRAAx] inst2 b j x ≐ zero :=
  ex_least b hj

/-- The Sperner cell `[C − 1, C]`: colour zero at its left end, nonzero colour at its right end. -/
theorem sperner_cell (N x : PTm n) (h0 : Γ ⊢[PRAAx] inst2 b zero x ≐ zero)
    (hN : Γ ⊢[PRAAx] neg (inst2 b N x ≐ zero)) :
    Γ ⊢[PRAAx] (inst2 b (monus (C b N x) (succ zero)) x ≐ zero) ⋏ neg (inst2 b (C b N x) x ≐ zero) := by
  have w := first_change b N x h0 hN
  have hW : Γ ⊢[PRAAx] le (succ zero) (C b N x) := Prf.andE₁ (Prf.andE₁ w)
  have e := natEq (eq_add_of_le hW)
  have hj : Γ ⊢[PRAAx] lt (monus (C b N x) (succ zero)) (C b N x) := by
    show Γ ⊢[PRAAx] le (succ (monus (C b N x) (succ zero))) (C b N x)
    ipra_le 0 with e
  exact .andI (before_change b hj) (Prf.andE₂ w)

end LeanProofs.IPRA.Topology.SpernerWitness
