import IPRADerivations.DiophantineNumberTheory.KhinchinUnionVanish
import IPRADerivations.DiophantineNumberTheory.KhinchinCellCount
import IPRADerivations.DiophantineNumberTheory.KhinchinCellParams
import IPRADerivations.Core.Header

/-!
# From a cell's block count to its round count (`hurwitz_khinchin_ipra`)

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`, (K11) in a gap and the round of (K2).

For coarse cell `g < G = p + 1` with the parameters of `KhinchinCellParams` (`α = 4g+1`, `γ = 4g+3`,
`b₀ + 1 = 4G`), a grid `T = R! G'` equal to `r G`, and the cell's fine range `[rg, rg + r)` inside `[0, T M)`:

* `cell_bridge`: the conclusion of `KhinchinBlock.block_cover` for the cell's block,
  `(γ − α) T ≤ 8192 (b₀ + 1) Σ_{c<TM} sg(⋃)(c)`, together with the per-scale margins of `block_out`, gives
  `r ≤ 16384 Σ_{k<r} sg(⋃)(rg + k)` — the per-cell count of `KhinchinRoundCounts.round_from_counts`. It chains
  `KhinchinCellParams.cell_gap`/`cell_hL`, `KhinchinUnionVanish.union_vanish_lo`/`hi` and
  `KhinchinCellCount.count_local`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.KhinchinCellBridge

open_ipra
open LeanProofs.IPRA.Signum (sg)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBlockScales (Xt bB)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinUnionVanish (union_vanish_lo union_vanish_hi)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinCellCount (count_local)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinCellParams (αc γc b0c cell_gap cell_hL)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- One cell: the block count and the margins give `r ≤ 16384 Σ_{k<r} sg(⋃)(rg + k)`. -/
theorem cell_bridge (wb : PTm 2) {B K0 M R G' g p r : PTm n}
    (hT : Γ ⊢[PRAAx] fact R * G' ≐ r * succ p)
    (hcov : Γ ⊢[PRAAx] le (monus (γc g) (αc g) * (fact R * G'))
      (num 8192 * succ (b0c p) *
        ap2 (sumF (sg (oB (bB wb)))) (fact R * G' * M) (pairT B (Xt K0 M R G' (αc g) (γc g) (b0c p)))))
    (hH : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift B) ⟶
      le (fact (Syn.shift R) * Syn.shift G' * Syn.shift (γc g) +
          inst2 wb (var 0) (Xt (Syn.shift K0) (Syn.shift M) (Syn.shift R) (Syn.shift G') (Syn.shift (αc g))
            (Syn.shift (γc g)) (Syn.shift (b0c p))) * succ (Syn.shift (b0c p)))
        (Syn.shift (r * g + r) * succ (Syn.shift (b0c p)))))
    (hHN : Γ ⊢[PRAAx] le (r * g + r) (fact R * G' * M)) :
    Γ ⊢[PRAAx] le r (num 16384 *
      ap2 (sumF (offB (sg (oB (bB wb))))) r (pairT (r * g) (pairT B (Xt K0 M R G' (αc g) (γc g) (b0c p))))) := by
  have hL : Γ ⊢[PRAAx] le (r * g * succ (b0c p)) (fact R * G' * αc g) :=
    le_congr (.eqRefl _) (congrMul hT.eqSymm (.eqRefl _)) (cell_hL r g p)
  have lo := union_vanish_lo wb hL hH
  have hi := union_vanish_hi wb (N := monus (fact R * G' * M) (r * g + r)) hL hH
  have e1 := natEq (cell_gap (Γ := Γ) g)
  have e2 := natEq hT
  have hcov' : Γ ⊢[PRAAx] le (two * (r * succ p))
      (num 8192 * (num 4 * succ p) *
        ap2 (sumF (sg (oB (bB wb)))) (fact R * G' * M) (pairT B (Xt K0 M R G' (αc g) (γc g) (b0c p)))) := by
    ipra_le sl hcov with 𝔞 (fact R) * 𝔞 G' * e1 + 2 * e2
  exact count_local (sg (oB (bB wb))) hcov' hHN lo hi

end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinCellBridge
