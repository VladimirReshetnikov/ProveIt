import IPRADerivations.Core.Tactic
import IPRADerivations.Core.LinearCombination

/-!
# The radial algebra of the Kerr–Newman family

Packet: `geometry/four_metrics_ipra_2026-11-15` (the notation `eq:notation`, the determinant
remark after `eq:maxwell`, `prop:radial` and `cor:unique`). With

  `s = 1 − x²`,  `Σ = r² + a² x²`,  `P = r² + a²`,  `Δ = r² − 2 m r + a² + q²`,

the following are polynomial identities over the integers:

* `sigma_identity`: `P − a² s = Σ`;
* `radial_solution` (`prop:radial`, `cor:unique`): `d = Δ` solves the radial equation
  `r² − a² + d − r d′ = q²`, with `d′ = 2r − 2m` (and `d″ = 2`);
* `block_det`: for the `(t, φ)` block of `Σ g`, with entries
  `G_tt = −Δ + s a²`, `G_tφ = Δ a s − s a P`, `G_φφ = −Δ a² s² + s P²`,
  `G_tt G_φφ − G_tφ² = −Δ s (P − a² s)²`, for arbitrary `Δ, s, a, P`. Together with the diagonal
  entries `Σ/Δ` and `Σ/s` this gives `det g = −Σ²`;
* `radial_unique` (`cor:unique`, the coefficient step): a monic quadratic `d = r² + c₁ r + c₀`
  that satisfies the radial equation has `c₀ = a² + q²`.

The curvature computations of the packet are in `Geometry/KerrNewmanConnection` and
`Geometry/KerrNewmanRicci`.
-/

namespace LeanProofs.IPRA.Geometry.KerrNewmanAlgebra

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

section Radial

abbrev r : ZT 10 := .var2 0 1
abbrev m : ZT 10 := .var2 2 3
abbrev a : ZT 10 := .var2 4 5
abbrev q : ZT 10 := .var2 6 7
abbrev x : ZT 10 := .var2 8 9

abbrev s : ZT 10 := ZT.natLit 1 - x * x
abbrev Sg : ZT 10 := r * r + a * a * (x * x)
abbrev P : ZT 10 := r * r + a * a
abbrev Dl : ZT 10 := r * r - ZT.natLit 2 * m * r + a * a + q * q
/-- `Δ′ = 2r − 2m`. -/
abbrev Dl' : ZT 10 := ZT.natLit 2 * r - ZT.natLit 2 * m

def sigmaFormula : Fm PTm 10 := ZT.eq (P - a * a * s) Sg

def radialFormula : Fm PTm 10 := ZT.eq (r * r - a * a + Dl - r * Dl') (q * q)

theorem sigma_open : ([] : List (Fm PTm 10)) ⊢[PRAAx] sigmaFormula := by
  unfold sigmaFormula; ipra_ring

theorem radial_open : ([] : List (Fm PTm 10)) ⊢[PRAAx] radialFormula := by
  unfold radialFormula; ipra_ring

/-- `P − a² s = Σ`. -/
theorem sigma_identity : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 10 sigmaFormula := closeAll 10 sigma_open

/-- `Δ = r² − 2mr + a² + q²` solves `r² − a² + d − r d′ = q²`. -/
theorem radial_solution : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 10 radialFormula := closeAll 10 radial_open

end Radial

section Block

abbrev D : ZT 8 := .var2 0 1
abbrev s' : ZT 8 := .var2 2 3
abbrev a' : ZT 8 := .var2 4 5
abbrev P' : ZT 8 := .var2 6 7

abbrev Gtt : ZT 8 := -D + s' * (a' * a')
abbrev Gtp : ZT 8 := D * a' * s' - s' * a' * P'
abbrev Gpp : ZT 8 := -(D * (a' * a') * (s' * s')) + s' * (P' * P')

def blockDetFormula : Fm PTm 8 :=
  ZT.eq (Gtt * Gpp - ZT.sq Gtp) (-(D * s' * ZT.sq (P' - a' * a' * s')))

theorem block_det_open : ([] : List (Fm PTm 8)) ⊢[PRAAx] blockDetFormula := by
  unfold blockDetFormula; ipra_ring

/-- `G_tt G_φφ − G_tφ² = −Δ s (P − a² s)²`. -/
theorem block_det : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 8 blockDetFormula := closeAll 8 block_det_open

end Block

/-- `cor:unique`, the coefficient step: a monic quadratic radial function `r² + c₁ r + c₀` that
satisfies `r² − a² + d − r d′ = q²` has `c₀ = a² + q²`. -/
theorem radial_unique {n : ℕ} {Γ : List (Fm PTm n)} {r c₀ c₁ a q : ZT n}
    (h : Γ ⊢[PRAAx] ZT.eq (r * r - a * a + (r * r + c₁ * r + c₀) - r * (ZT.natLit 2 * r + c₁)) (q * q)) :
    Γ ⊢[PRAAx] ZT.eq c₀ (a * a + q * q) := by
  ipra_lc ZT.toZ_eq h

end LeanProofs.IPRA.Geometry.KerrNewmanAlgebra
