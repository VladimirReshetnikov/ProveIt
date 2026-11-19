import IPRADerivations.Core.IntOrder

/-!
# Overlapping branches for a robust comparison with zero

Packet: `foundations/ipra_cfp_contract_compiler_2026-11-15`, `paper/sections/07_branching.tex`, Lemma
"Overlapping-branch soundness": for a rational approximation `a` with `|x − a| ≤ η` and the guards
`L(a) : a ≤ η`, `R(a) : a ≥ −η`, "`L(a)` implies `x ≤ 2η`, and `R(a)` implies `x ≥ −2η`. Moreover
`L(a) ∨ R(a)` is decidable and always true."

With signed integer terms `x`, `a` (numerators over a common denominator), the natural error `η`, and the
integer order `zle` of `Core/IntOrder`; `|x − a| ≤ η` is the pair `x ≤ a + η`, `a ≤ x + η`:

* `left_branch`: `x ≤ a + η` and `a ≤ η` give `x ≤ 2η`;
* `right_branch`: `a ≤ x + η` and `−η ≤ a` give `−2η ≤ x`;
* `branch_cover`: `a ≤ η` or `−η ≤ a`, for every `a` (a decidable case split on the natural parts).
-/

namespace LeanProofs.IPRA.Foundations.OverlapBranches

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `L(a)` gives `x ≤ 2η`. -/
theorem left_branch {x a : ZT n} {η : PTm n} (h : Γ ⊢[PRAAx] zle x (a + ZT.ofNat η))
    (hL : Γ ⊢[PRAAx] zle a (ZT.ofNat η)) : Γ ⊢[PRAAx] zle x (ZT.ofNat (η + η)) := by
  have e₁ := zle_toZ h
  have e₂ := zle_toZ hL
  refine zle_of_toZ (monus ((a + ZT.ofNat η).pos + x.neg) (x.pos + (a + ZT.ofNat η).neg) +
    monus ((ZT.ofNat η).pos + a.neg) (a.pos + (ZT.ofNat η).neg)) ?_
  simp only [ZT.toZ_add, ZT.toZ_ofNat, Q.mk_add, map_add] at e₁ e₂ ⊢
  linear_combination e₁ + e₂

/-- `R(a)` gives `−2η ≤ x`. -/
theorem right_branch {x a : ZT n} {η : PTm n} (h : Γ ⊢[PRAAx] zle a (x + ZT.ofNat η))
    (hR : Γ ⊢[PRAAx] zle (-ZT.ofNat η) a) : Γ ⊢[PRAAx] zle (-ZT.ofNat (η + η)) x := by
  have e₁ := zle_toZ h
  have e₂ := zle_toZ hR
  refine zle_of_toZ (monus ((x + ZT.ofNat η).pos + a.neg) (a.pos + (x + ZT.ofNat η).neg) +
    monus (a.pos + (-ZT.ofNat η).neg) ((-ZT.ofNat η).pos + a.neg)) ?_
  simp only [ZT.toZ_add, ZT.toZ_neg, ZT.toZ_ofNat, Q.mk_add, map_add] at e₁ e₂ ⊢
  linear_combination e₁ + e₂

/-- One of the two guards always holds. -/
theorem branch_cover (a : ZT n) (η : PTm n) :
    Γ ⊢[PRAAx] zle a (ZT.ofNat η) ⋎ zle (-ZT.ofNat η) a := by
  refine .orE (le_total a.pos (η + a.neg)) ?_ ?_
  · refine .orI₁ (zle_of_toZ (monus (η + a.neg) a.pos) ?_)
    have e := natEq (eq_add_of_le (Prf.hyp0 : (le a.pos (η + a.neg) :: Γ) ⊢[PRAAx] _))
    rw [toZ_def, ZT.toZ_ofNat]
    simp only [Q.mk_add, map_add] at e
    linear_combination -e
  · refine .orI₂ (zle_of_toZ (monus a.pos a.neg + η) ?_)
    have h : (le (η + a.neg) a.pos :: Γ) ⊢[PRAAx] le (η + a.neg) a.pos := Prf.hyp0
    have e := natEq (eq_add_of_le (le_trans (le_of_eq_add (d := η) (add_comm _ _)) h))
    rw [ZT.toZ_neg, ZT.toZ_ofNat, toZ_def a]
    simp only [Q.mk_add, map_add] at e ⊢
    linear_combination -e

end LeanProofs.IPRA.Foundations.OverlapBranches
