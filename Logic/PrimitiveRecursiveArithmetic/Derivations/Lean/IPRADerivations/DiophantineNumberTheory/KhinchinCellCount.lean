import IPRADerivations.Foundations.SumLocal
import IPRADerivations.DiophantineNumberTheory.KhinchinMargin
import IPRADerivations.Foundations.CrossingSearch
import IPRADerivations.AnalyticNumberTheory.LogRefinement

/-!
# The (K11) count inside one coarse cell (`hurwitz_khinchin_ipra`)

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`, (K11): "`|⋃_{k=K}^B E_k(J)| ≥ L/16384`".

`KhinchinBlock.block_cover` gives, for the cell's block with `J^*` the middle half (`γ − α = 2`, `b₀ + 1 = 4G`,
`KhinchinCellParams`), the count `2 T ≤ 8192 · 4G · Σ_{c<N} u(c)` of its covered grid cells. When the block covers
nothing outside the cell's fine range `[L, L + r)` (`KhinchinBlockLocal.block_out`) and the grid is `T = rG`:

* `count_local`: `r ≤ 16384 Σ_{k<r} u(L + k)` — the cell count `w r ≤ (c+1) Σ_k sg(v(k))` of
  `KhinchinRoundCounts.round_from_counts` (for an uncovered cell `w = 1`, `c + 1 = 16384`), by
  `Foundations.SumLocal.sum_local` and cancelling `2G`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.KhinchinCellCount

open_ipra exports
open LeanProofs.IPRA.Foundations.SumLocal (sum_local)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The block count localized to the cell: `r ≤ 16384 Σ_{k<r} u(L + k)`. -/
theorem count_local (u : PTm 2) {N L r P p : PTm n}
    (hcov : Γ ⊢[PRAAx] le (two * (r * succ p)) (num 8192 * (num 4 * succ p) * ap2 (sumF u) N P))
    (hHN : Γ ⊢[PRAAx] le (L + r) N)
    (hlo : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift L) ⟶ inst2 u (var 0) (Syn.shift P) ≐ zero))
    (hhi : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (monus N (L + r))) ⟶
      inst2 u (Syn.shift (L + r) + var 0) (Syn.shift P) ≐ zero)) :
    Γ ⊢[PRAAx] le r (num 16384 * ap2 (sumF (offB u)) r (pairT L P)) := by
  have hLH : Γ ⊢[PRAAx] le L (L + r) := by ipra_le 𝔞 r
  have hsl := sum_local u hLH hHN hlo hhi
  have em : Γ ⊢[PRAAx] monus (L + r) L ≐ r := monus_of_eq (.eqRefl _)
  have e := natEq (hsl.eqTrans (congrAp2 (sumF (offB u)) em (.eqRefl _)))
  have pos : Γ ⊢[PRAAx] two * succ p ≐ succ (pred (two * succ p)) :=
    LeanProofs.IPRA.AnalyticNumberTheory.LogRefinement.pos_of_eq
      (show Γ ⊢[PRAAx] two * succ p ≐ succ (succ p + p) by ipra_ring)
  refine cancel pos ?_
  ipra_le sl hcov with 32768 * (𝔞 p + 1) * e

end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinCellCount
