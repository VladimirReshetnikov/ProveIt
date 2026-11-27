import IPRADerivations.Foundations.WindowStability

/-!
# Bounded cardinality gives an empty window

Packet: `foundations/ipra_framework`, `paper/sections/05_metastability.tex`, Theorem `thm:empty-window`
("Bounded cardinality, finite empty window"): if a decidable predicate has at most `B` solutions, then
among `B + 1` pairwise disjoint windows `[c_i, c_{i+1})`, `i ≤ B`, a bounded search finds one in which the
predicate fails everywhere.

The counting core. Let `w(i, x)` be the number of solutions in the `i`-th window (a bounded sum of the
characteristic bits over the window). Disjointness of the windows and the cardinality premise enter as the
single inequality `∑_{i ≤ B} w(i, x) ≤ B` (the windows together contain at most `B` solutions).

* `pos_of_ne`: `w ≠ 0` gives `1 ≤ w`;
* `empty_window`: from `∑_{i<B+1} w(i, x) ≤ B`, `∃ i < B + 1. w(i, x) = 0`. The index is the least one,
  `mu w (B + 1) x`. The case distinction is the bounded decision of `Foundations/LeastBoundedWitness`; if no
  window count vanished, each would be at least one and the sum at least `B + 1`.

A window whose count is zero contains no solution (`sum_zero_elim` of `Core/BoundedSums`). The windows
`c_{i+1} = F(a, c_i) + 1` and the derivation of the total from the cardinality theorem are data of the
application.
-/

namespace LeanProofs.IPRA.Foundations.EmptyWindow

open_ipra exports
open LeanProofs.IPRA.Foundations.LeastBoundedWitness (ExW NoW decision)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- A nonzero count is at least one. -/
theorem pos_of_ne {a : PTm n} (h : Γ ⊢[PRAAx] neg (a ≐ zero)) : Γ ⊢[PRAAx] le one a := by
  refine .orE (zero_or_succ a) (.botE _ (Prf.impE h.wk Prf.hyp0)) ?_
  have e := natEq (Prf.hyp0 : ((a ≐ succ (pred a)) :: Γ) ⊢[PRAAx] a ≐ succ (pred a))
  ipra_le 𝔟 (pred a) using linear_combination e

/-- `thm:empty-window`: if `B + 1` window counts add up to at most `B`, one of them is zero. -/
theorem empty_window {w : PTm 2} {B x : PTm n} (h : Γ ⊢[PRAAx] le (ap2 (sumF w) (succ B) x) B) :
    Γ ⊢[PRAAx] ExW w (succ B) x := by
  refine .orE (decision (f := w) (succ B) x) Prf.hyp0 ?_
  have hN : (NoW w (succ B) x :: Γ) ⊢[PRAAx] NoW w (succ B) x := Prf.hyp0
  have hlow : (NoW w (succ B) x :: Γ) ⊢[PRAAx] le (succ B * one) (ap2 (sumF w) (succ B) x) := by
    refine sum_lower (.allI (.impI ?_))
    have e : Syn.shift (one : PTm n) = one := by simp [Syn.shift]
    rw [e]
    exact pos_of_ne (Prf.impE hN.allOpen.wk Prf.hyp0)
  have h' := h.wk (ψ := NoW w (succ B) x)
  refine not_succ_le_self B _ ?_
  ipra_le sl hlow + sl h'

end LeanProofs.IPRA.Foundations.EmptyWindow
