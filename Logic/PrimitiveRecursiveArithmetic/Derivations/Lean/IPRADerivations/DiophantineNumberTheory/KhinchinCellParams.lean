import IPRADerivations.DiophantineNumberTheory.KhinchinMargin
import IPRADerivations.AnalyticNumberTheory.LogRefinement
import IPRADerivations.Foundations.CrossingSearch
import IPRADerivations.Core.Header

/-!
# The parameters of one coarse cell (`hurwitz_khinchin_ipra`, assembling (K2))

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`: "`J^* = (a + L/4, b − L/4)`" and (K4)
"`L K ≥ 256 b₀`-type" conditions for the block construction in a gap `J` of length `L`.

The coarse grid has `G = p + 1` cells; cell `g < G` is `[g/G, (g+1)/G)`, refined into `r` fine cells, so the fine
grid is `T = rG` and the cell is the fine range `[rg, r(g+1))`. Its block uses the middle half
`J^* = ((4g+1)/4G, (4g+3)/4G)`: `α = 4g + 1`, `γ = 4g + 3`, `β = b₀ + 1 = 4G`, and `K₀ = 512G`. Then:

* `cell_hag`, `cell_hg`, `cell_hD`, `cell_hK4`: the hypotheses `α ≤ γ`, `γ ≤ b₀ + 1`, `γ − α ≥ 1` and (K4)
  `256(b₀+1) ≤ (γ − α) K₀` of `KhinchinBlock.block_cover`;
* `cell_hL`, `cell_hH`: the margins `Lβ ≤ Tα` and `Tγ + wβ ≤ Hβ` of `KhinchinBlockLocal.block_out`, the second from
  the width bound `4Q²w ≤ T` (`hW`) and `G ≤ Q²` (`four_w_le`: `4w ≤ r`).
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.KhinchinCellParams

open_ipra
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinMargin (cancel)
open LeanProofs.IPRA.AnalyticNumberTheory.LogRefinement (pos_of_eq)
open LeanProofs.IPRA.Foundations.CrossingSearch (monus_of_eq)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `α = 4g + 1`. -/
abbrev αc (g : PTm n) : PTm n := num 4 * g + one
/-- `γ = 4g + 3`. -/
abbrev γc (g : PTm n) : PTm n := num 4 * g + num 3
/-- `b₀ = 4G − 1` for `G = p + 1`. -/
abbrev b0c (p : PTm n) : PTm n := num 4 * p + num 3
/-- `K₀ = 512 G`. -/
abbrev K0c (p : PTm n) : PTm n := num 512 * succ p

theorem cell_hag (g : PTm n) : Γ ⊢[PRAAx] le (αc g) (γc g) := by ipra_le 2

theorem cell_hg {g p : PTm n} (hg : Γ ⊢[PRAAx] lt g (succ p)) : Γ ⊢[PRAAx] le (γc g) (succ (b0c p)) := by
  ipra_le 4 * sl hg + 1

theorem cell_gap (g : PTm n) : Γ ⊢[PRAAx] monus (γc g) (αc g) ≐ two :=
  monus_of_eq (by ipra_ring)

theorem cell_hD (g : PTm n) : Γ ⊢[PRAAx] monus (γc g) (αc g) ≐ succ (pred (monus (γc g) (αc g))) :=
  pos_of_eq (cell_gap g)

theorem cell_hK4 (g p : PTm n) :
    Γ ⊢[PRAAx] le (num 256 * succ (b0c p)) (monus (γc g) (αc g) * K0c p) := by
  have e := natEq (cell_gap (Γ := Γ) g)
  ipra_le 0 with 512 * (𝔞 p + 1) * e

/-- The left margin `Lβ ≤ Tα`: `rg · 4G ≤ rG (4g + 1)`. -/
theorem cell_hL (r g p : PTm n) : Γ ⊢[PRAAx] le (r * g * succ (b0c p)) (r * succ p * αc g) := by
  ipra_le 𝔞 r * (𝔞 p + 1)

/-- `4Q²w ≤ rG` and `G ≤ Q²` give `4w ≤ r`. -/
theorem four_w_le {Q w r p : PTm n} (hW : Γ ⊢[PRAAx] le (num 4 * (Q * Q) * w) (r * succ p))
    (hQ : Γ ⊢[PRAAx] le (succ p) (Q * Q)) : Γ ⊢[PRAAx] le (num 4 * w) r := by
  have pos : Γ ⊢[PRAAx] Q * Q ≐ succ (pred (Q * Q)) := pos_of_eq ((eq_add_of_le hQ).eqTrans (succ_add _ _))
  refine cancel pos ?_
  ipra_le sl hW + 𝔞 r * sl hQ

/-- The right margin `Tγ + wβ ≤ Hβ`: `rG(4g + 3) + 4Gw ≤ r(g+1) · 4G`, from `4w ≤ r`. -/
theorem cell_hH {Q w r g p : PTm n} (hW : Γ ⊢[PRAAx] le (num 4 * (Q * Q) * w) (r * succ p))
    (hQ : Γ ⊢[PRAAx] le (succ p) (Q * Q)) :
    Γ ⊢[PRAAx] le (r * succ p * γc g + w * succ (b0c p)) (r * succ g * succ (b0c p)) := by
  have h := four_w_le hW hQ
  ipra_le (𝔞 p + 1) * sl h

end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinCellParams
