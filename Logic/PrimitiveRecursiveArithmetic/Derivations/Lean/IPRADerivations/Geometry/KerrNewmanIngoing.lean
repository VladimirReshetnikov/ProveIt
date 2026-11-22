import IPRADerivations.Core.PolynomialImplications

/-!
# The ingoing chart and the static specialization (`four_metrics_ipra`)

Packet: `geometry/four_metrics_ipra_2026-11-15`, Section "A rational atlas across radial and
polar coordinate poles" (`eq:ingoing`, `eq:ingoinginv`) and Subsection "Reissner–Nordström
and its elementary verification" (`eq:RN`, `eq:staticRic`).

**The ingoing chart.** With `s = 1 − x²`, `Σ = r² + a² x²`, `P = r² + a²`,
`Δ = r² − 2 m r + a² + q²`, the metric `eq:ingoing` in the coordinate order `(v, r, x, ψ)` has

`g_vv = −(Δ − a² s)/Σ`, `g_vr = 1`, `g_vψ = −a s (P − Δ)/Σ`, `g_rr = 0`, `g_rψ = −a s`,
`g_ψψ = s (P² − a² Δ s)/Σ`, `g_xx = Σ/s`,

and `eq:ingoinginv` states `Σ g⁻¹ = [[a² s, P, 0, a], [P, Δ, 0, a], [0, 0, s, 0],
[a, a, 0, 1/s]]`. The nine products of the `(v, r, ψ)` block of `g` with this matrix, cleared
of `Σ` and `s`, are the polynomial identities `ingoing_vv`, …, `ingoing_psipsi`: the diagonal
ones give `Σ²` (resp. `Σ`, `Σ² s`) and the others `0`. No inverse power of `Δ` occurs, so the
identities hold at `Δ = 0` as well.

**Reissner–Nordström.** With `F = r² f = r² − 2 m r + q²`: the quotient-rule numerators
`r³ f′ = 2 m r − 2 q²` (`rn_f1`) and `r⁴ f″ = −4 m r + 6 q²` (`rn_f2`), and the two
components of `eq:staticRic` for this `f`: `r⁴ (f″/2 + f′/r) = q²` (`rn_tt`, doubled) and
`r² (1 − f − r f′) = q²` (`rn_theta`).

Each statement is a closed sentence of iPRA over integer variables
(`Core/PolynomialImplications`). The differentiations and `prop:regular` (the field equations
in the ingoing chart, valid at `Δ = 0`) are `Geometry/KerrNewmanIngoingConnection`,
`Geometry/KerrNewmanIngoingRicci` and `Geometry/KerrNewmanIngoingMaxwell`; the static entries
from `lem:offshell` are `Geometry/KerrNewmanStatic`; `det g₊ = −Σ²` is not stated.
-/

namespace LeanProofs.IPRA.Geometry.KerrNewmanIngoing

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ZExp

local notation "vr" => (ZExp.var 0 : ZExp 5)
local notation "vx" => (ZExp.var 1 : ZExp 5)
local notation "va" => (ZExp.var 2 : ZExp 5)
local notation "vm" => (ZExp.var 3 : ZExp 5)
local notation "vq" => (ZExp.var 4 : ZExp 5)

/-- `s = 1 − x²`. -/
abbrev sS : ZExp 5 := 1 - vx ^ 2
/-- `Σ = r² + a² x²`. -/
abbrev Sg : ZExp 5 := vr ^ 2 + va ^ 2 * vx ^ 2
/-- `P = r² + a²`. -/
abbrev Pp : ZExp 5 := vr ^ 2 + va ^ 2
/-- `Δ = r² − 2 m r + a² + q²`. -/
abbrev Dl : ZExp 5 := vr ^ 2 - 2 * vm * vr + va ^ 2 + vq ^ 2
/-- The numerator of `g_vv` over `Σ`. -/
abbrev gvv : ZExp 5 := -(Dl - va ^ 2 * sS)
/-- The numerator of `g_vψ` over `Σ`. -/
abbrev gvp : ZExp 5 := -(va * sS * (Pp - Dl))
/-- The numerator of `g_ψψ` over `Σ`. -/
abbrev gpp : ZExp 5 := sS * (Pp ^ 2 - va ^ 2 * Dl * sS)

/-! ## The inverse of the ingoing metric -/

theorem ingoing_vv : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (gvv * (va ^ 2 * sS) + Pp * Sg + gvp * va, Sg ^ 2)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

theorem ingoing_vr : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (gvv * Pp + Dl * Sg + gvp * va, 0)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

theorem ingoing_vpsi : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (gvv * (va * sS) + va * Sg * sS + gvp, 0)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

theorem ingoing_rv : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (va ^ 2 * sS + (-(va * sS)) * va, 0)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

theorem ingoing_rr : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (Pp + (-(va * sS)) * va, Sg)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

theorem ingoing_rpsi : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (va * sS + (-(va * sS)) * 1, 0)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

theorem ingoing_psiv : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (gvp * (va ^ 2 * sS) + (-(va * sS)) * Pp * Sg + gpp * va, 0)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

theorem ingoing_psir : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (gvp * Pp + (-(va * sS)) * Dl * Sg + gpp * va, 0)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

theorem ingoing_psipsi : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (gvp * (va * sS) + (-(va * sS)) * va * Sg * sS + gpp, Sg ^ 2 * sS)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

/-! ## Reissner–Nordström -/

/-- `F = r² f = r² − 2 m r + q²`. -/
abbrev Fn : ZExp 5 := vr ^ 2 - 2 * vm * vr + vq ^ 2
/-- `r³ f′ = 2 m r − 2 q²`. -/
abbrev N1 : ZExp 5 := 2 * vm * vr - 2 * vq ^ 2
/-- `r⁴ f″ = −4 m r + 6 q²`. -/
abbrev N2 : ZExp 5 := 6 * vq ^ 2 - 4 * vm * vr

/-- The quotient-rule numerator of `f′` for `f = F / r²`: `F′ r − 2 F` with `F′ = 2 r − 2 m`. -/
theorem rn_f1 : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] ((2 * vr - 2 * vm) * vr - 2 * Fn, N1)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

/-- The quotient-rule numerator of `f″` for `f′ = N₁ / r³`: `N₁′ r − 3 N₁` with `N₁′ = 2 m`. -/
theorem rn_f2 : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (2 * vm * vr - 3 * N1, N2)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

/-- `r⁴ (f″/2 + f′/r) = q²`, doubled: the `tt` and `rr` components of `eq:staticRic`. -/
theorem rn_tt : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (N2 + 2 * N1, 2 * vq ^ 2)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

/-- `r² (1 − f − r f′) = q²`: the angular components of `eq:staticRic`. -/
theorem rn_theta : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
    (imp [] (vr ^ 2 - Fn - N1, vq ^ 2)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

end LeanProofs.IPRA.Geometry.KerrNewmanIngoing
