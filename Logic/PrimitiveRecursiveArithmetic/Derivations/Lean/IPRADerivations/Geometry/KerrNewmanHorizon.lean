import IPRADerivations.Geometry.KerrNewmanIngoingConnection
import IPRADerivations.Geometry.KerrNewmanConnection

/-!
# Horizons, the stationary limit and curvature invariants (`four_metrics_ipra`)

Packet: `geometry/four_metrics_ipra_2026-11-15`, Section "Local horizons, stationary limits,
and curvature": `eq:roots`, the stationary-limit equation, `eq:chi`, `eq:horizonkilling` with
the surface-gravity identity, `eq:RicSquared`, and `eq:equatorK` with its two lower bounds.

## Roots and the stationary limit (indeterminates `r, x, a, m, q`)

With the metric `eq:ingoing` of `Geometry/KerrNewmanIngoingConnection` (`Σ = r² + a² x²`,
`s = 1 − x²`, `P = r² + a²`, `Δ = r² − 2mr + a² + q²`):

* `roots` (`eq:roots`): `Δ = (r − m)² − (m² − a² − q²)`;
* `delta_prime`: the formal derivative `Δ′ = 2r − 2m`;
* `stationary_limit`: `g_vv = −(r² − 2mr + q² + a² x²)/Σ`, so the null locus of `∂_v` is
  `r² − 2mr + q² + a² x² = 0`.

## The Killing horizon (`eq:chi`, `eq:horizonkilling`)

"Let `r₀` be a specified root of `Δ` … Define `Ω₀ = a/P₀`, `χ = ∂_v + Ω₀ ∂_ψ`." With `Om = a/P`:

* `chi_p`, `chi_b`: `p₊(χ) = 1 − a s Ω₀ = Σ/P₀`, `b₊(χ) = P₀ Ω₀ − a = 0`;
* `chi_null`: under `Δ = 0`, `g₊(χ, χ) = g_vv + 2 Ω₀ g_vψ + Ω₀² g_ψψ = 0`;
* `chi_flat_v`, `chi_flat_r`, `chi_flat_p`: the components of `χ♭ = g₊(χ, ·)`: under `Δ = 0`,
  `g_vv + Ω₀ g_vψ = 0` and `g_vψ + Ω₀ g_ψψ = 0`, and `g_vr + Ω₀ g_rψ = Σ/P₀` (the `x`-component
  vanishes because `g_vx = g_xψ = 0`): `χ♭ = (Σ/P₀) dr`.

## The surface gravity (indeterminates `r, x, a, d, v, p₀`)

"Keeping `Ω₀` constant when differentiating the squared norm gives, at `r₀`,
`d(g₊(χ, χ)) = −(Δ′(r₀) Σ/P₀²) dr = −2κ χ♭`, `κ = Δ′(r₀)/(2P₀)`." The radial function is the
indeterminate `d` with derivative `v` (so that `Δ = 0` and `Δ′` are a hypothesis and a symbol),
and `P₀` is the constant indeterminate `p₀`; `Ω₀ = a/p₀`. Under `d = 0` and `p₀ = P`:

* `surface_r`: `∂_r g₊(χ, χ) = −v Σ/P₀²`;
* `surface_x`: `∂_x g₊(χ, χ) = 0`;
* `surface_gravity`: `∂_r g₊(χ, χ) = −2 (v/(2P₀)) (Σ/P₀)`, that is `d(g₊(χ, χ)) = −2κ χ♭`.

## The square of the Ricci tensor (indeterminates `r, x, a, d, U, V`)

For the radial-function metric of `lem:offshell` with `U`, `V` left as indeterminates (so that
`Ric = U (…) + V (…)` as in `eq:offshell`), in the Boyer–Lindquist coordinates of
`Geometry/KerrNewmanConnection`:

* `mixed_tt`, `mixed_tp`, `mixed_pt`, `mixed_pp`, `mixed_rr`, `mixed_xx`: the mixed tensor
  `A = g⁻¹ Ric` has `A^t_t = −(U P + V a² s)/Σ`, `A^t_φ = a (U + V) P s/Σ`,
  `A^φ_t = −a (U + V)/Σ`, `A^φ_φ = (U a² s + V P)/Σ`, `A^r_r = −U`, `A^x_x = V`;
* `mixed_trace`: `tr A = −2U + 2V` (the scalar curvature of `lem:offshell`);
* `ricci_square`: `R_{μν} R^{μν} = tr(A²) = 2U² + 2V²`. With `U = V = q²/Σ²`
  (`Geometry/KerrNewmanEinstein.kn_U`, `kn_V`) this is `eq:RicSquared`,
  `R_{μν} R^{μν} = 4q⁴/Σ⁴` ("Each of its four diagonal coframe contributions is `q⁴/Σ⁴`").

## The equatorial Kretschmann scalar (indeterminates `r, x, a, m, q`)

`Kn` is the bracket of `eq:Kretschmann` (`𝒦 = 8 Kn/Σ⁶`). The Kretschmann scalar itself (the
full Riemann tensor, `eq:Riemann`, `eq:paircontract`) is not derived here.

* `equator_K` (`eq:equatorK`): at `x = 0`, `8 Kn/Σ⁶ = 8 (6 (m r − q²)² + q⁴)/r⁸`;
* `equator_square`: `7 (6 (m r − q²)² + q⁴) = (7q² − 6 m r)² + 6 m² r²`;
* `equator_bound_m`: `56 (6 (m r − q²)² + q⁴) = 48 m² r² + 8 (7q² − 6 m r)²`, the
  sum-of-squares certificate of `𝒦 ≥ 48 m²/(7 r⁶)` at the equator;
* `equator_bound_q`: `8 (6 (m r − q²)² + q⁴) = 8 q⁴ + 48 (m r − q²)²`, the certificate of
  `𝒦 ≥ 8 q⁴/r⁸`.

Every statement is an implication between polynomial equations, mostly identities of
fractions cleared of denominators (`Frac.eqn`), a closed sentence of iPRA certified in every
commutative ring.
-/

namespace LeanProofs.IPRA.Geometry.KerrNewmanHorizon

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ZExp

/-! ## Roots, the stationary limit and the Killing horizon -/

section Horizon

open LeanProofs.IPRA.Geometry.KerrNewmanIngoingConnection (δr δr_0 δr_1 δr_2 δr_3 δr_4 Sg sx Pp
  Dl gvv gvr gvp grp gpp)

local notation "r" => (ZExp.var 0 : ZExp 5)
local notation "x" => (ZExp.var 1 : ZExp 5)
local notation "a" => (ZExp.var 2 : ZExp 5)
local notation "m" => (ZExp.var 3 : ZExp 5)
local notation "q" => (ZExp.var 4 : ZExp 5)

/-- `eq:roots`: `Δ = (r − m)² − (m² − a² − q²)`. -/
theorem roots :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Dl, (r - m) ^ 2 - (m ^ 2 - a ^ 2 - q ^ 2))) :=
  derive_imp _ _ (by ipra_poly R ρ h [Dl]; ring)

/-- The formal derivative `Δ′ = 2r − 2m`. -/
theorem delta_prime :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5) (imp [] (der δr Dl, 2 * r - 2 * m)) :=
  derive_imp _ _ (by frac_poly R ρ h [Dl, δr_0, δr_1, δr_2, δr_3, δr_4]; ring)

/-- The stationary limit: `g_vv = −(r² − 2mr + q² + a² x²)/Σ`. -/
theorem stationary_limit :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn gvv ⟨-(r ^ 2 - 2 * m * r + q ^ 2 + a ^ 2 * x ^ 2), Sg⟩)) :=
  derive_imp _ _ (by frac_poly R ρ h [gvv, Dl, Sg, sx]; ring)

/-- `Ω₀ = a/P₀`, the angular velocity of the horizon `eq:chi`. -/
def Om : Frac 5 := ⟨a, Pp⟩

/-- `p₊(χ) = 1 − a s Ω₀ = Σ/P₀`. -/
theorem chi_p :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 1 - Frac.ofZ (a * sx) * Om) ⟨Sg, Pp⟩)) :=
  derive_imp _ _ (by frac_poly R ρ h [Om, Sg, sx, Pp]; ring)

/-- `b₊(χ) = P₀ Ω₀ − a = 0`. -/
theorem chi_b :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ (-a) + Frac.ofZ Pp * Om) (Frac.ofZ 0))) :=
  derive_imp _ _ (by frac_poly R ρ h [Om, Pp]; ring)

/-- `eq:horizonkilling`: at a root of `Δ`, `g₊(χ, χ) = 0`. -/
theorem chi_null :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [(Dl, 0)] (Frac.eqn (gvv + Frac.ofZ 2 * Om * gvp + Om * Om * gpp) (Frac.ofZ 0))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvp, gpp, Om, Sg, sx, Pp]
    rw [h]
    ring)

/-- `χ♭`, component `v`: at a root of `Δ`, `g_vv + Ω₀ g_vψ = 0`. -/
theorem chi_flat_v :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [(Dl, 0)] (Frac.eqn (gvv + Om * gvp) (Frac.ofZ 0))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvp, Om, Sg, sx, Pp]
    rw [h]
    ring)

/-- `χ♭`, component `r`: `g_vr + Ω₀ g_rψ = Σ/P₀`. -/
theorem chi_flat_r :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (gvr + Om * grp) ⟨Sg, Pp⟩)) :=
  derive_imp _ _ (by frac_poly R ρ h [gvr, grp, Om, Sg, sx, Pp]; ring)

/-- `χ♭`, component `ψ`: at a root of `Δ`, `g_vψ + Ω₀ g_ψψ = 0`. -/
theorem chi_flat_p :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [(Dl, 0)] (Frac.eqn (gvp + Om * gpp) (Frac.ofZ 0))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvp, gpp, Om, Sg, sx, Pp]
    rw [h]
    ring)

end Horizon

/-! ## The surface gravity -/

section SurfaceGravity

local notation "r" => (ZExp.var 0 : ZExp 6)
local notation "x" => (ZExp.var 1 : ZExp 6)
local notation "a" => (ZExp.var 2 : ZExp 6)
local notation "d" => (ZExp.var 3 : ZExp 6)
local notation "v" => (ZExp.var 4 : ZExp 6)
local notation "p₀" => (ZExp.var 5 : ZExp 6)

/-- `∂_r` with `∂_r d = v`; `a`, `x` and `p₀` are constants (`v` is not differentiated). -/
def δg : Fin 6 → ZExp 6
  | ⟨0, _⟩ => 1
  | ⟨3, _⟩ => v
  | _ => 0

/-- `∂_x`. -/
def δh : Fin 6 → ZExp 6
  | ⟨1, _⟩ => 1
  | _ => 0

theorem δg_0 : δg 0 = 1 := rfl
theorem δg_1 : δg 1 = 0 := rfl
theorem δg_2 : δg 2 = 0 := rfl
theorem δg_3 : δg 3 = v := rfl
theorem δg_4 : δg 4 = 0 := rfl
theorem δg_5 : δg 5 = 0 := rfl
theorem δh_0 : δh 0 = 0 := rfl
theorem δh_1 : δh 1 = 1 := rfl
theorem δh_2 : δh 2 = 0 := rfl
theorem δh_3 : δh 3 = 0 := rfl
theorem δh_4 : δh 4 = 0 := rfl
theorem δh_5 : δh 5 = 0 := rfl

/-- `Σ = r² + a² x²`. -/
def SgS : ZExp 6 := r ^ 2 + a ^ 2 * x ^ 2
/-- `s = 1 − x²`. -/
def sxS : ZExp 6 := 1 - x ^ 2
/-- `P = r² + a²`. -/
def PpS : ZExp 6 := r ^ 2 + a ^ 2
/-- `g_vv = (−d + a² s)/Σ`. -/
def hvv : Frac 6 := ⟨-d + a ^ 2 * sxS, SgS⟩
/-- `g_vψ = −a s (P − d)/Σ`. -/
def hvp : Frac 6 := ⟨-(a * sxS * (PpS - d)), SgS⟩
/-- `g_ψψ = s (P² − a² d s)/Σ`. -/
def hpp : Frac 6 := ⟨sxS * (PpS ^ 2 - a ^ 2 * d * sxS), SgS⟩
/-- `Ω₀ = a/p₀`, constant. -/
def Oc : Frac 6 := ⟨a, p₀⟩
/-- The squared norm `g₊(χ, χ)` of `χ = ∂_v + Ω₀ ∂_ψ`. -/
def Nf : Frac 6 := hvv + Frac.ofZ 2 * Oc * hvp + Oc * Oc * hpp

/-- The horizon: `d = Δ = 0` and `p₀ = P`. -/
abbrev horizonHyps : List (ZExp 6 × ZExp 6) := [(d, 0), (p₀, PpS)]

/-- `∂_r g₊(χ, χ) = −Δ′(r₀) Σ/P₀²` at the horizon. -/
theorem surface_r :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp horizonHyps (Frac.eqn (Frac.d δg Nf) ⟨-(v * SgS), PpS ^ 2⟩)) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Nf, hvv, hvp, hpp, Oc, SgS, sxS, PpS, δg_0, δg_1, δg_2, δg_3, δg_4, δg_5]
    obtain ⟨h₁, h₂⟩ := h
    simp only [h₁, h₂]
    ring)

/-- `∂_x g₊(χ, χ) = 0` at the horizon. -/
theorem surface_x :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp horizonHyps (Frac.eqn (Frac.d δh Nf) (Frac.ofZ 0))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Nf, hvv, hvp, hpp, Oc, SgS, sxS, PpS, δh_0, δh_1, δh_2, δh_3, δh_4, δh_5]
    obtain ⟨h₁, h₂⟩ := h
    simp only [h₁, h₂]
    ring)

/-- The surface gravity: `d(g₊(χ, χ)) = −2κ χ♭` with `κ = Δ′(r₀)/(2P₀)` and
`χ♭ = (Σ/P₀) dr`. -/
theorem surface_gravity :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp horizonHyps (Frac.eqn (Frac.d δg Nf) (Frac.ofZ (-2) * ⟨v, 2 * p₀⟩ * ⟨SgS, p₀⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Nf, hvv, hvp, hpp, Oc, SgS, sxS, PpS, δg_0, δg_1, δg_2, δg_3, δg_4, δg_5]
    obtain ⟨h₁, h₂⟩ := h
    simp only [h₁, h₂]
    ring)

end SurfaceGravity

/-! ## The square of the Ricci tensor -/

section RicciSquare

open LeanProofs.IPRA.Geometry.KerrNewmanBase (Sg sx)
open LeanProofs.IPRA.Geometry.KerrNewmanConnection (Pp itt itp ipp irr ixx)

local notation "r" => (ZExp.var 0 : ZExp 6)
local notation "x" => (ZExp.var 1 : ZExp 6)
local notation "a" => (ZExp.var 2 : ZExp 6)
local notation "d" => (ZExp.var 3 : ZExp 6)
local notation "U" => (ZExp.var 4 : ZExp 6)
local notation "V" => (ZExp.var 5 : ZExp 6)

/-- `R_tt = U d/Σ + V s a²/Σ`, with `U`, `V` indeterminates. -/
def Qtt : Frac 6 := Frac.ofZ U * ⟨d, Sg⟩ + Frac.ofZ V * ⟨sx * a ^ 2, Sg⟩
/-- `R_tφ = −U d a s/Σ − V s a P/Σ`. -/
def Qtp : Frac 6 := -(Frac.ofZ U * ⟨d * a * sx, Sg⟩) - Frac.ofZ V * ⟨sx * a * Pp, Sg⟩
/-- `R_φφ = U d a² s²/Σ + V s P²/Σ`. -/
def Qpp : Frac 6 := Frac.ofZ U * ⟨d * a ^ 2 * sx ^ 2, Sg⟩ + Frac.ofZ V * ⟨sx * Pp ^ 2, Sg⟩
/-- `R_rr = −U Σ/d`. -/
def Qrr : Frac 6 := -(Frac.ofZ U * ⟨Sg, d⟩)
/-- `R_xx = V Σ/s`. -/
def Qxx : Frac 6 := Frac.ofZ V * ⟨Sg, sx⟩

/-- `A^t_t = −(U P + V a² s)/Σ`. -/
def Att : Frac 6 := ⟨-(U * Pp + V * a ^ 2 * sx), Sg⟩
/-- `A^t_φ = a (U + V) P s/Σ`. -/
def Atp : Frac 6 := ⟨a * (U + V) * Pp * sx, Sg⟩
/-- `A^φ_t = −a (U + V)/Σ`. -/
def Apt : Frac 6 := ⟨-(a * (U + V)), Sg⟩
/-- `A^φ_φ = (U a² s + V P)/Σ`. -/
def App : Frac 6 := ⟨U * a ^ 2 * sx + V * Pp, Sg⟩

/-- `A^t_t = g^{tt} R_tt + g^{tφ} R_φt`. -/
theorem mixed_tt :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (itt * Qtt + itp * Qtp) Att)) :=
  derive_imp _ _ (by frac_poly R ρ h [itt, itp, Qtt, Qtp, Att, Pp, Sg, sx]; ring)

/-- `A^t_φ = g^{tt} R_tφ + g^{tφ} R_φφ`. -/
theorem mixed_tp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (itt * Qtp + itp * Qpp) Atp)) :=
  derive_imp _ _ (by frac_poly R ρ h [itt, itp, Qtp, Qpp, Atp, Pp, Sg, sx]; ring)

/-- `A^φ_t = g^{φt} R_tt + g^{φφ} R_φt`. -/
theorem mixed_pt :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (itp * Qtt + ipp * Qtp) Apt)) :=
  derive_imp _ _ (by frac_poly R ρ h [itp, ipp, Qtt, Qtp, Apt, Pp, Sg, sx]; ring)

/-- `A^φ_φ = g^{φt} R_tφ + g^{φφ} R_φφ`. -/
theorem mixed_pp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (itp * Qtp + ipp * Qpp) App)) :=
  derive_imp _ _ (by frac_poly R ρ h [itp, ipp, Qtp, Qpp, App, Pp, Sg, sx]; ring)

/-- `A^r_r = g^{rr} R_rr = −U`. -/
theorem mixed_rr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (irr * Qrr) (Frac.ofZ (-U)))) :=
  derive_imp _ _ (by frac_poly R ρ h [irr, Qrr, Sg]; ring)

/-- `A^x_x = g^{xx} R_xx = V`. -/
theorem mixed_xx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (ixx * Qxx) (Frac.ofZ V))) :=
  derive_imp _ _ (by frac_poly R ρ h [ixx, Qxx, Sg, sx]; ring)

/-- `tr A = −2U + 2V`. -/
theorem mixed_trace :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Att + App + Frac.ofZ (-U) + Frac.ofZ V) (Frac.ofZ (2 * V - 2 * U)))) :=
  derive_imp _ _ (by frac_poly R ρ h [Att, App, Pp, Sg, sx]; ring)

/-- `R_{μν} R^{μν} = tr(A²) = 2U² + 2V²`; at `U = V = q²/Σ²` this is `eq:RicSquared`. -/
theorem ricci_square :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Att * Att + Frac.ofZ 2 * (Atp * Apt) + App * App
        + Frac.ofZ (-U) * Frac.ofZ (-U) + Frac.ofZ V * Frac.ofZ V)
        (Frac.ofZ (2 * U ^ 2 + 2 * V ^ 2)))) :=
  derive_imp _ _ (by frac_poly R ρ h [Att, Atp, Apt, App, Pp, Sg, sx]; ring)

end RicciSquare

/-! ## The equatorial Kretschmann scalar -/

section Equator

local notation "r" => (ZExp.var 0 : ZExp 5)
local notation "x" => (ZExp.var 1 : ZExp 5)
local notation "a" => (ZExp.var 2 : ZExp 5)
local notation "m" => (ZExp.var 3 : ZExp 5)
local notation "q" => (ZExp.var 4 : ZExp 5)

/-- The bracket of `eq:Kretschmann`: `𝒦 = 8 Kn/Σ⁶`. -/
def Kn : ZExp 5 :=
  6 * m ^ 2 * (r ^ 6 - 15 * r ^ 4 * a ^ 2 * x ^ 2 + 15 * r ^ 2 * a ^ 4 * x ^ 4 - a ^ 6 * x ^ 6)
    - 12 * m * q ^ 2 * r * (r ^ 4 - 10 * r ^ 2 * a ^ 2 * x ^ 2 + 5 * a ^ 4 * x ^ 4)
    + q ^ 4 * (7 * r ^ 4 - 34 * r ^ 2 * a ^ 2 * x ^ 2 + 7 * a ^ 4 * x ^ 4)

/-- `eq:equatorK`: at `x = 0`, `8 Kn/Σ⁶ = 8 (6 (m r − q²)² + q⁴)/r⁸`. -/
theorem equator_K :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [(x, 0)] (Frac.eqn ⟨8 * Kn, (r ^ 2 + a ^ 2 * x ^ 2) ^ 6⟩
        ⟨8 * (6 * (m * r - q ^ 2) ^ 2 + q ^ 4), r ^ 8⟩)) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Kn]
    rw [h]
    ring)

/-- Completing the square: `7 (6 (m r − q²)² + q⁴) = (7q² − 6 m r)² + 6 m² r²`. -/
theorem equator_square :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (7 * (6 * (m * r - q ^ 2) ^ 2 + q ^ 4),
        (7 * q ^ 2 - 6 * m * r) ^ 2 + 6 * m ^ 2 * r ^ 2)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

/-- The certificate of `𝒦 ≥ 48 m²/(7 r⁶)` at the equator:
`56 (6 (m r − q²)² + q⁴) = 48 m² r² + 8 (7q² − 6 m r)²`. -/
theorem equator_bound_m :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (56 * (6 * (m * r - q ^ 2) ^ 2 + q ^ 4),
        48 * m ^ 2 * r ^ 2 + 8 * (7 * q ^ 2 - 6 * m * r) ^ 2)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

/-- The certificate of `𝒦 ≥ 8 q⁴/r⁸` at the equator:
`8 (6 (m r − q²)² + q⁴) = 8 q⁴ + 48 (m r − q²)²`. -/
theorem equator_bound_q :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (8 * (6 * (m * r - q ^ 2) ^ 2 + q ^ 4), 8 * q ^ 4 + 48 * (m * r - q ^ 2) ^ 2)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

end Equator

end LeanProofs.IPRA.Geometry.KerrNewmanHorizon
