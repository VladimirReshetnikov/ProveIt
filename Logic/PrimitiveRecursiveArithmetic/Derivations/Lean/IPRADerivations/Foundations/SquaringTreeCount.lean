import IPRADerivations.Core.BoundedSums
import IPRADerivations.Core.Powers
import IPRADerivations.Core.OrderCertificates

/-!
# The node count of the repeated-squaring recursion tree

Packet: `foundations/ipra_complexity_foundations_2026-11-20`, `tex/space.tex`, after "Finite repeated squaring":
"The recursion tree has at most `1 + (2N) + ⋯ + (2N)^j ≤ (2N + 1)^{j+1}` nodes. Multiplication by the explicit
per-node bookkeeping and adjacency cost gives a primitive-recursive clock for an iterative stack machine."

* `geom_le`: `∑_{i≤j} x^i ≤ (x + 1)^j` for all `x, j` (quantifier-free induction: the new term `x^{j+1}` is at
  most `x (x + 1)^j`), sharper than the paper's exponent `j + 1`;
* `tree_count`: `∑_{i≤j} (2N)^i ≤ (2N + 1)^{j+1}`, the packet's bound.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.SquaringTreeCount

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The body `x^i`; variables `0 = i`, `1 = x`. -/
abbrev powB : PTm 2 := pw (var 1) (var 0)

theorem inst2_powB (i x : PTm n) : inst2 powB i x = pw x i := by simp [inst2]

/-- `∑_{i≤j} x^i`. -/
abbrev G (j x : PTm n) : PTm n := ap2 (sumF powB) (succ j) x

theorem geom_base (x : PTm n) : Γ ⊢[PRAAx] le (G zero x) (pw (succ x) zero) := by
  have e1 := natEq (sum_succ' (Γ := Γ) powB zero x)
  have e0 := natEq (sum_zero (Γ := Γ) powB x)
  have p1 := natEq (pw_zero (Γ := Γ) x)
  have p2 := natEq (pw_zero (Γ := Γ) (succ x))
  rw [inst2_powB] at e1
  ipra_le 0 using
    rw [e1, e0, p1, p2]; ring

theorem geom_step {j x : PTm n} (ih : Γ ⊢[PRAAx] le (G j x) (pw (succ x) j)) :
    Γ ⊢[PRAAx] le (G (succ j) x) (pw (succ x) (succ j)) := by
  have hm := pw_le_pw (Γ := Γ) j (le_succ_self x)
  have e1 := natEq (sum_succ' (Γ := Γ) powB (succ j) x)
  rw [inst2_powB] at e1
  have e2 := natEq (pw_succ (Γ := Γ) x j)
  have e3 := natEq (pw_succ (Γ := Γ) (succ x) j)
  ipra_le sl ih + 𝔟 x * sl hm with e3 - e1 - e2

/-- Variables `0 = j` (induction), `1 = x`. -/
private abbrev gF : Fm PTm 2 := le (G (var 0) (var 1)) (pw (succ (var 1)) (var 0))

private theorem g₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] gF := by
  refine ind _ (le_QF _ _) ?_ ?_
  · simp
    exact geom_base _
  · simp
    exact geom_step Prf.hyp0

/-- `∑_{i≤j} x^i ≤ (x + 1)^j`. -/
theorem geom_le (j x : PTm n) : Γ ⊢[PRAAx] le (G j x) (pw (succ x) j) := by
  have h := inst (Γ := Γ) g₀ (![j, x] : Fin 2 → PTm n)
  simpa using h

/-- The recursion tree bound `∑_{i≤j} (2N)^i ≤ (2N + 1)^{j+1}`. -/
theorem tree_count (j N : PTm n) :
    Γ ⊢[PRAAx] le (G j (num 2 * N)) (pw (succ (num 2 * N)) (succ j)) := by
  have h := geom_le (Γ := Γ) j (num 2 * N)
  have e := natEq (pw_succ (Γ := Γ) (succ (num 2 * N)) j)
  have hs : Γ ⊢[PRAAx] le (pw (succ (num 2 * N)) j) (pw (succ (num 2 * N)) (succ j)) := by
    ipra_le 𝔟 (pw (succ (num 2 * N)) j) * (2 * 𝔟 N) with e
  exact le_trans h hs

end LeanProofs.IPRA.Foundations.SquaringTreeCount
