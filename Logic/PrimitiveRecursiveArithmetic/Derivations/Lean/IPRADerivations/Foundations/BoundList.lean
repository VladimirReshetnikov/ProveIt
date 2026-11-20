import IPRADerivations.Foundations.PointList
import IPRADerivations.Probability.UnionUtility
import IPRADerivations.Core.OrderCertificates

/-!
# Height bounds and complete solution lists

Packet: `foundations/ipra_cfp_contract_compiler_2026-11-15`, `paper/sections/08_search_height.tex`, Theorem
"Bound–list equivalence": for a fixed decidable coding, (i) a verified height bound `H` produces a complete
finite solution list by bounded enumeration; (ii) a verified complete finite list produces a height bound,
the maximum code height of its entries.

The solution predicate is a bit `S(x, p)` (decidable coding), solutions are codes `x`.

(i) With the height bound `S(x) = 1 → x ≤ H` (code height), the list is the rank and select of the solutions
below `H + 1` (`Foundations/FilteredEnumeration`):

* `list_sound`: every entry `L[r] = sel r`, `r < ℓ`, is a solution;
* `list_complete`: every solution `x` is the entry `L[rank x]` with `rank x < ℓ`.

(ii) With a complete list `L(r, p)`, `r < ℓ`, and code heights `ht(x, p)`, the bound is
`M = max_{r<ℓ} ht(L(r))` (`UnionUtility.Mx` of `htLB`):

* `height_of_entry`: an entry `x = L(r)`, `r < ℓ`, has `ht(x) ≤ M`;
* `height_of_list`: if completeness is an existential `S(x) = 1 → ∃ r < ℓ, L(r) = x`, every solution has
  `ht(x) ≤ M`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.BoundList

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.FilteredEnumeration (rank sel sel_spec sel_rank rank_lt_size)
open LeanProofs.IPRA.Foundations.PointList (bit_one)
open LeanProofs.IPRA.Foundations.BoundedReflection (one_ne_zero)
open LeanProofs.IPRA.Probability.UnionUtility (Mx mx_upper)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Δ : List (Fm PTm k)}

/-! ## (i) From a height bound to a complete list -/

section List

variable (S : PTm 2)

/-- Every entry of the enumerated list is a solution. -/
theorem list_sound (hbit : ∀ x p : PTm k, Δ ⊢[PRAAx] le (inst2 S x p) one) {r H p : PTm k}
    (hr : Δ ⊢[PRAAx] lt r (rank S (succ H) p)) : Δ ⊢[PRAAx] inst2 S (sel S r (succ H) p) p ≐ one :=
  bit_one (hbit _ _) (Prf.andE₁ (Prf.andE₂ (sel_spec S hr)))

/-- Every solution is listed: `x = L[rank x]` with `rank x < ℓ`. -/
theorem list_complete {x H p : PTm k} (hH : Δ ⊢[PRAAx] le x H) (hS : Δ ⊢[PRAAx] inst2 S x p ≐ one) :
    Δ ⊢[PRAAx] lt (rank S x p) (rank S (succ H) p) ⋏ (sel S (rank S x p) (succ H) p ≐ x) := by
  have hx : Δ ⊢[PRAAx] lt x (succ H) := by
    show Δ ⊢[PRAAx] le (succ x) (succ H)
    ipra_le sl hH
  have kept : Δ ⊢[PRAAx] neg (inst2 S x p ≐ zero) := .impI (one_ne_zero _ (hS.wk.eqSymm.eqTrans Prf.hyp0))
  exact .andI (rank_lt_size S hx kept) (sel_rank S hx kept)

end List

/-! ## (ii) From a complete list to a height bound -/

section Height

variable (L ht : PTm 2)

/-- The heights of the entries, `ht(L(r, p), p)`. -/
def htLB : PTm 2 := Syn.subst ![L, Syn.var 1] ht

theorem inst2_htLB (r p : PTm k) : inst2 (htLB L ht) r p = inst2 ht (inst2 L r p) p := by
  simp only [inst2, htLB, Syn.subst_subst]
  congr 1; funext t; fin_cases t <;> simp

/-- An entry of the list has height at most the maximum. -/
theorem height_of_entry {r ℓ x p : PTm k} (hr : Δ ⊢[PRAAx] lt r ℓ) (hx : Δ ⊢[PRAAx] inst2 L r p ≐ x) :
    Δ ⊢[PRAAx] le (inst2 ht x p) (Mx (htLB L ht) ℓ p) := by
  have m := mx_upper (htLB L ht) (x := p) hr
  rw [inst2_htLB] at m
  exact le_congr (congrInst2 ht hx (.eqRefl p)) (.eqRefl _) m

/-- A complete list gives a height bound: every solution has height at most `max_{r<ℓ} ht(L(r))`. -/
theorem height_of_list {ℓ x p : PTm k}
    (hcomp : Δ ⊢[PRAAx] Fm.ex (lt (Syn.var 0) (Syn.shift ℓ) ⋏
      (inst2 L (Syn.var 0) (Syn.shift p) ≐ Syn.shift x))) :
    Δ ⊢[PRAAx] le (inst2 ht x p) (Mx (htLB L ht) ℓ p) := by
  refine .exE hcomp ?_
  have h0 : ((lt (Syn.var 0) (Syn.shift ℓ) ⋏ (inst2 L (Syn.var 0) (Syn.shift p) ≐ Syn.shift x)) ::
      Δ.map Fm.shift) ⊢[PRAAx] lt (Syn.var 0) (Syn.shift ℓ) ⋏
        (inst2 L (Syn.var 0) (Syn.shift p) ≐ Syn.shift x) := Prf.hyp0
  have c := height_of_entry L ht (Prf.andE₁ h0) (Prf.andE₂ h0)
  rw [Fm.shift, subst_le]
  simpa [Syn.shift, Mx, subst_inst2] using c

end Height

end LeanProofs.IPRA.Foundations.BoundList
