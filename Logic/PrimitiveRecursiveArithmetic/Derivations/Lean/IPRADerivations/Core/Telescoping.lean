import IPRADerivations.Core.SumLemmas
import IPRADerivations.Core.LinearCombination

/-!
# Telescoping sums

* `tele_nat`: `∑_{i<N} a(i+1) + a(0) = ∑_{i<N} a(i) + a(N)`;
* `tele_signed`: for a signed sequence `p − q` given by its positive and negative parts,
  `∑_{i<N} ((p − q)(i+1) − (p − q)(i)) = (p − q)(N) − (p − q)(0)`, written without subtraction:
  `∑_{i<N} (p(i+1) + q(i)) + p(0) + q(N) = ∑_{i<N} (p(i) + q(i+1)) + p(N) + q(0)`;
* `closed_signed`: if `(p − q)(N) = (p − q)(0)`, the two sums are equal, i.e. the sum of the
  differences around a closed chain is zero.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `∑_{i<N} a(i+1) + a(0) = ∑_{i<N} a(i) + a(N)`. -/
theorem tele_nat (a : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (shiftBody a)) N x + inst2 a zero x ≐ ap2 (sumF a) N x + inst2 a N x := by
  ipra_lc natEq (sum_succ' (Γ := Γ) a N x) - natEq (sum_shift (Γ := Γ) a N x)

/-- The body `p(i+1) + q(i)`. -/
abbrev upB (p q : PTm 2) : PTm 2 := addBody (shiftBody p) q
/-- The body `p(i) + q(i+1)`. -/
abbrev dnB (p q : PTm 2) : PTm 2 := addBody p (shiftBody q)

theorem tele_signed_base (p q : PTm 2) (x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (upB p q)) zero x + inst2 p zero x + inst2 q zero x ≐
      ap2 (sumF (dnB p q)) zero x + inst2 p zero x + inst2 q zero x := by
  ipra_lc natEq (sum_zero (Γ := Γ) (upB p q) x) - natEq (sum_zero (Γ := Γ) (dnB p q) x)

theorem tele_signed_step (p q : PTm 2) {N x : PTm n}
    (ih : Γ ⊢[PRAAx] ap2 (sumF (upB p q)) N x + inst2 p zero x + inst2 q N x ≐
      ap2 (sumF (dnB p q)) N x + inst2 p N x + inst2 q zero x) :
    Γ ⊢[PRAAx] ap2 (sumF (upB p q)) (succ N) x + inst2 p zero x + inst2 q (succ N) x ≐
      ap2 (sumF (dnB p q)) (succ N) x + inst2 p (succ N) x + inst2 q zero x := by
  have s₁ := sum_succ' (Γ := Γ) (upB p q) N x
  rw [inst2_addBody, inst2_shiftBody] at s₁
  have s₂ := sum_succ' (Γ := Γ) (dnB p q) N x
  rw [inst2_addBody, inst2_shiftBody] at s₂
  ipra_lc natEq ih + natEq s₁ - natEq s₂

/-- Variables: `0 = N` (induction), `1 = x`. -/
private abbrev teleF (p q : PTm 2) : Fm PTm 2 :=
  ap2 (sumF (upB p q)) (var 0) (var 1) + inst2 p zero (var 1) + inst2 q (var 0) (var 1) ≐
    ap2 (sumF (dnB p q)) (var 0) (var 1) + inst2 p (var 0) (var 1) + inst2 q zero (var 1)

private theorem tele₀ (p q : PTm 2) : ([] : List (Fm PTm 2)) ⊢[PRAAx] teleF p q := by
  ipra_ind [subst_ap2, subst_inst2]
  · exact tele_signed_base p q _
  · exact tele_signed_step p q Prf.hyp0

/-- Signed telescoping:
`∑_{i<N} (p(i+1) + q(i)) + p(0) + q(N) = ∑_{i<N} (p(i) + q(i+1)) + p(N) + q(0)`. -/
theorem tele_signed (p q : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (upB p q)) N x + inst2 p zero x + inst2 q N x ≐
      ap2 (sumF (dnB p q)) N x + inst2 p N x + inst2 q zero x := by
  have i := inst (Γ := Γ) (tele₀ p q) (![N, x] : Fin 2 → PTm n)
  simpa [subst_inst2] using i

/-- Around a closed chain, `(p − q)(N) = (p − q)(0)`, the differences sum to zero. -/
theorem closed_signed (p q : PTm 2) {N x : PTm n}
    (hc : Γ ⊢[PRAAx] inst2 p N x + inst2 q zero x ≐ inst2 p zero x + inst2 q N x) :
    Γ ⊢[PRAAx] ap2 (sumF (upB p q)) N x ≐ ap2 (sumF (dnB p q)) N x := by
  refine add_right_cancel (c := inst2 p zero x + inst2 q N x) ?_
  have t := natEq (tele_signed (Γ := Γ) p q N x); have c := natEq hc
  apply deriveNat; ipra_simps
  linear_combination t + c

end LeanProofs.IPRA
