import IPRADerivations.Geometry.KerrNewmanConnection

/-!
# The Ricci tensor of the radial-function metric and of the Kerr–Newman family

Packet: `geometry/four_metrics_ipra_2026-11-15`, `lem:offshell` ("Radial-function Ricci
identity") and `thm:KN` ("Kerr–Newman Ricci tensor").

`lem:offshell`: "Replace `Δ` by `d` in `eq:master` and assume `Σ d s ≠ 0`. Define
`N = r² − a² + d − r v`, `V = N/Σ²`, `U = V + (w − 2)/(2Σ)`. Then
`Ric(g) = U ((d/Σ) p² − (Σ/d) dr²) + V ((Σ/s) dx² + (s/Σ) b²)`", with the one-forms
`p = dt − a s dφ`, `b = P dφ − a dt`. In components (the index `p` stands for `φ`):

`R_tt = U d/Σ + V s a²/Σ`, `R_tφ = −U d a s/Σ − V s a P/Σ`,
`R_φφ = U d a² s²/Σ + V s P²/Σ`, `R_rr = −U Σ/d`, `R_xx = V Σ/s`,

and the other entries vanish.

The Ricci tensor is computed from the convention `eq:ricci`,

`R_{μν} = Σ_λ ∂_λ Γ^λ_{μν} − ∂_ν Σ_λ Γ^λ_{μλ} + Σ_{λ,ρ} (Γ^λ_{μν} Γ^ρ_{λρ} − Γ^ρ_{μλ} Γ^λ_{νρ})`,

with the connection coefficients of `Geometry/KerrNewmanConnection` (reduced fractions
`Gλ_μν`, each certified there as the value of `eq:gamma`) and `∂_t = ∂_φ = 0`. For each entry
`R_{μν}` with at least one nonvanishing term:

* `Rμν_tk`: the `k`-th nonvanishing term (a derivative `∂_λ Γ` taken by
  `Foundations/FormalDerivation`, or a product `Γ Γ`) equals the numerator `Rμν_nk` over the
  common denominator `Rμν_cd`;
* `ricci_μν`: the signed sum of these numerators over the common denominator is the fraction of
  `eq:offshell` (`0` for `R_rx`). The sign of each term is its sign in `eq:ricci`.

The entries `R_tr`, `R_tx`, `R_rφ`, `R_xφ` have no nonvanishing term: in every term of
`eq:ricci` one factor is a vanishing coefficient or a derivative along `t` or `φ`.

`thm:KN`: "Here `v = 2r − 2m`, `w = 2`, and
`N = r² − a² + (r² − 2mr + a² + q²) − r(2r − 2m) = q²`. Consequently `U = V = q²/Σ²`":
`kn_N`, `kn_w` are the two specializations, as implications from `d = Δ`, `v = 2r − 2m`, `w = 2`.

The numerators were proposed by a computer algebra script; every identity is checked by Lean
as an identity of fractions cleared of denominators, a closed sentence of iPRA certified in
every commutative ring. The hypothesis `Σ d s ≠ 0` is the reading of the cleared identities as
equalities of rational functions.
-/

namespace LeanProofs.IPRA.Geometry.KerrNewmanRicci

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Geometry.KerrNewmanBase (δr δx δr_0 δr_1 δr_2 δr_3 δr_4 δr_5 δx_0 δx_1 δx_2
  δx_3 δx_4 δx_5 Sg sx)
open LeanProofs.IPRA.Geometry.KerrNewmanConnection
open ZExp

local notation "r" => (ZExp.var 0 : ZExp 6)
local notation "x" => (ZExp.var 1 : ZExp 6)
local notation "a" => (ZExp.var 2 : ZExp 6)
local notation "d" => (ZExp.var 3 : ZExp 6)
local notation "v" => (ZExp.var 4 : ZExp 6)
local notation "w" => (ZExp.var 5 : ZExp 6)

/-- `N = r² − a² + d − r v` (`eq:UV`). -/
def Nn : ZExp 6 := r ^ 2 - a ^ 2 + d - r * v
/-- `V = N/Σ²`. -/
def Vf : Frac 6 := ⟨Nn, Sg ^ 2⟩
/-- `U = V + (w − 2)/(2Σ)`. -/
def Uf : Frac 6 := Vf + ⟨w - 2, 2 * Sg⟩

/-! ## The entry `R_{tt}` -/

/-- The common denominator of the terms of `R_{tt}`. -/
def Rtt_cd : ZExp 6 := 4 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `∂_r Γ^r_{tt}` over the common denominator. -/
def Rtt_n1 : ZExp 6 := -2 * (a ^ 2 * x ^ 2 + r ^ 2) * (-a ^ 4 * d * w * x ^ 4 + 2 * a ^ 4 * d *
    x ^ 4 - 2 * a ^ 4 * d * x ^ 2 + 2 * a ^ 4 * r * v * x ^ 4 - 2 * a ^ 4 * r * v * x ^ 2 -
    a ^ 4 * v ^ 2 * x ^ 4 + 2 * a ^ 2 * d ^ 2 * x ^ 2 - 2 * a ^ 2 * d * r ^ 2 * w * x ^ 2 - 10 *
    a ^ 2 * d * r ^ 2 * x ^ 2 + 10 * a ^ 2 * d * r ^ 2 + 8 * a ^ 2 * d * r * v * x ^ 2 + 2 *
    a ^ 2 * r ^ 3 * v * x ^ 2 - 2 * a ^ 2 * r ^ 3 * v - 2 * a ^ 2 * r ^ 2 * v ^ 2 * x ^ 2 - 10 *
    d ^ 2 * r ^ 2 - d * r ^ 4 * w + 8 * d * r ^ 3 * v - r ^ 4 * v ^ 2)
/-- `∂_r Γ^r_{tt}`, reduced to the common denominator. -/
theorem Rtt_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δr Gr_tt) (⟨Rtt_n1, Rtt_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_tt, Rtt_n1, Rtt_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2,
        δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `∂_x Γ^x_{tt}` over the common denominator. -/
def Rtt_n2 : ZExp 6 := 4 * a ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 - d + r ^ 2) * (3 * a ^ 2 *
    x ^ 4 - 5 * a ^ 2 * x ^ 2 - 3 * r ^ 2 * x ^ 2 + r ^ 2)
/-- `∂_x Γ^x_{tt}`, reduced to the common denominator. -/
theorem Rtt_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx Gx_tt) (⟨Rtt_n2, Rtt_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_tt, Rtt_n2, Rtt_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2,
        δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{tt} Γ^t_{rt}` over the common denominator. -/
def Rtt_n3 : ZExp 6 := (a ^ 2 + r ^ 2) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v *
    x ^ 2 + 2 * d * r - r ^ 2 * v) ^ 2
/-- `Γ^r_{tt} Γ^t_{rt}`, reduced to the common denominator. -/
theorem Rtt_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_tt * Gt_tr) (⟨Rtt_n3, Rtt_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_tt, Gt_tr, Rtt_n3, Rtt_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{tt} Γ^r_{rr}` over the common denominator. -/
def Rtt_n4 : ZExp 6 := (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 * v * x ^ 2 - 2 * d * r + r ^ 2 * v) *
    (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^r_{tt} Γ^r_{rr}`, reduced to the common denominator. -/
theorem Rtt_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_tt * Gr_rr) (⟨Rtt_n4, Rtt_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rr, Gr_tt, Rtt_n4, Rtt_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{tt} Γ^x_{rx}` over the common denominator. -/
def Rtt_n5 : ZExp 6 := -2 * d * r * (a ^ 2 * x ^ 2 + r ^ 2) * (2 * a ^ 2 * r * x ^ 2 - 2 *
    a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^r_{tt} Γ^x_{rx}`, reduced to the common denominator. -/
theorem Rtt_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_tt * Gx_rx) (⟨Rtt_n5, Rtt_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_tt, Gx_rx, Rtt_n5, Rtt_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{tt} Γ^p_{rp}` over the common denominator. -/
def Rtt_n6 : ZExp 6 := -(2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r -
    r ^ 2 * v) * (2 * a ^ 4 * r * x ^ 2 - 2 * a ^ 4 * r + a ^ 4 * v * x ^ 4 - a ^ 4 * v * x ^ 2 +
    2 * a ^ 2 * d * r + 2 * a ^ 2 * r ^ 3 * x ^ 2 - 2 * a ^ 2 * r ^ 3 + a ^ 2 * r ^ 2 * v *
    x ^ 2 - a ^ 2 * r ^ 2 * v + 2 * d * r ^ 3)
/-- `Γ^r_{tt} Γ^p_{rp}`, reduced to the common denominator. -/
theorem Rtt_t6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_tt * Gp_rp) (⟨Rtt_n6, Rtt_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rp, Gr_tt, Rtt_n6, Rtt_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{tt} Γ^t_{xt}` over the common denominator. -/
def Rtt_n7 : ZExp 6 := -4 * a ^ 4 * x ^ 2 * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) ^ 2
/-- `Γ^x_{tt} Γ^t_{xt}`, reduced to the common denominator. -/
theorem Rtt_t7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_tt * Gt_tx) (⟨Rtt_n7, Rtt_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tx, Gx_tt, Rtt_n7, Rtt_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{tt} Γ^r_{xr}` over the common denominator. -/
def Rtt_n8 : ZExp 6 := -4 * a ^ 4 * x ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) *
    (a ^ 2 - d + r ^ 2)
/-- `Γ^x_{tt} Γ^r_{xr}`, reduced to the common denominator. -/
theorem Rtt_t8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_tt * Gr_rx) (⟨Rtt_n8, Rtt_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Gx_tt, Rtt_n8, Rtt_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{tt} Γ^x_{xx}` over the common denominator. -/
def Rtt_n9 : ZExp 6 := 4 * a ^ 2 * x ^ 2 * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 -
    d + r ^ 2)
/-- `Γ^x_{tt} Γ^x_{xx}`, reduced to the common denominator. -/
theorem Rtt_t9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_tt * Gx_xx) (⟨Rtt_n9, Rtt_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_tt, Gx_xx, Rtt_n9, Rtt_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{tt} Γ^p_{xp}` over the common denominator. -/
def Rtt_n10 : ZExp 6 := -4 * a ^ 2 * x ^ 2 * (a ^ 2 - d + r ^ 2) * (a ^ 4 * x ^ 4 - a ^ 4 *
    x ^ 2 + a ^ 4 + a ^ 2 * d * x ^ 2 - a ^ 2 * d + a ^ 2 * r ^ 2 * x ^ 2 + a ^ 2 * r ^ 2 + r ^ 4)
/-- `Γ^x_{tt} Γ^p_{xp}`, reduced to the common denominator. -/
theorem Rtt_t10 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_tt * Gp_xp) (⟨Rtt_n10, Rtt_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_xp, Gx_tt, Rtt_n10, Rtt_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{tt} Γ^t_{tr}` over the common denominator. -/
def Rtt_n11 : ZExp 6 := (a ^ 2 + r ^ 2) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v *
    x ^ 2 + 2 * d * r - r ^ 2 * v) ^ 2
/-- `Γ^r_{tt} Γ^t_{tr}`, reduced to the common denominator. -/
theorem Rtt_t11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_tt * Gt_tr) (⟨Rtt_n11, Rtt_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_tt, Gt_tr, Rtt_n11, Rtt_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{tt} Γ^t_{tx}` over the common denominator. -/
def Rtt_n12 : ZExp 6 := -4 * a ^ 4 * x ^ 2 * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) ^ 2
/-- `Γ^x_{tt} Γ^t_{tx}`, reduced to the common denominator. -/
theorem Rtt_t12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_tt * Gt_tx) (⟨Rtt_n12, Rtt_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tx, Gx_tt, Rtt_n12, Rtt_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{tr} Γ^r_{tt}` over the common denominator. -/
def Rtt_n13 : ZExp 6 := (a ^ 2 + r ^ 2) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v *
    x ^ 2 + 2 * d * r - r ^ 2 * v) ^ 2
/-- `Γ^t_{tr} Γ^r_{tt}`, reduced to the common denominator. -/
theorem Rtt_t13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_tr * Gr_tt) (⟨Rtt_n13, Rtt_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_tt, Gt_tr, Rtt_n13, Rtt_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^p_{tr} Γ^r_{tp}` over the common denominator. -/
def Rtt_n14 : ZExp 6 := a ^ 2 * (x - 1) * (x + 1) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r -
    a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v) ^ 2
/-- `Γ^p_{tr} Γ^r_{tp}`, reduced to the common denominator. -/
theorem Rtt_t14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gp_tr * Gr_tp) (⟨Rtt_n14, Rtt_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_tr, Gr_tp, Rtt_n14, Rtt_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{tx} Γ^x_{tt}` over the common denominator. -/
def Rtt_n15 : ZExp 6 := -4 * a ^ 4 * x ^ 2 * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) ^ 2
/-- `Γ^t_{tx} Γ^x_{tt}`, reduced to the common denominator. -/
theorem Rtt_t15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_tx * Gx_tt) (⟨Rtt_n15, Rtt_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tx, Gx_tt, Rtt_n15, Rtt_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^p_{tx} Γ^x_{tp}` over the common denominator. -/
def Rtt_n16 : ZExp 6 := -4 * a ^ 2 * x ^ 2 * (a ^ 2 + r ^ 2) * (a ^ 2 - d + r ^ 2) ^ 2
/-- `Γ^p_{tx} Γ^x_{tp}`, reduced to the common denominator. -/
theorem Rtt_t16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gp_tx * Gx_tp) (⟨Rtt_n16, Rtt_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_tx, Gx_tp, Rtt_n16, Rtt_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{tp} Γ^p_{tr}` over the common denominator. -/
def Rtt_n17 : ZExp 6 := a ^ 2 * (x - 1) * (x + 1) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r -
    a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v) ^ 2
/-- `Γ^r_{tp} Γ^p_{tr}`, reduced to the common denominator. -/
theorem Rtt_t17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_tp * Gp_tr) (⟨Rtt_n17, Rtt_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_tr, Gr_tp, Rtt_n17, Rtt_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{tp} Γ^p_{tx}` over the common denominator. -/
def Rtt_n18 : ZExp 6 := -4 * a ^ 2 * x ^ 2 * (a ^ 2 + r ^ 2) * (a ^ 2 - d + r ^ 2) ^ 2
/-- `Γ^x_{tp} Γ^p_{tx}`, reduced to the common denominator. -/
theorem Rtt_t18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_tp * Gp_tx) (⟨Rtt_n18, Rtt_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_tx, Gx_tp, Rtt_n18, Rtt_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R_{tt}` (`eq:offshell`): the signed sum of its terms is `Uf * ⟨d, Sg⟩ + Vf * ⟨sx * a ^ 2,
        Sg⟩`. -/
theorem ricci_tt :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Rtt_n1 + Rtt_n2 + Rtt_n3 + Rtt_n4 + Rtt_n5 + Rtt_n6 + Rtt_n7 + Rtt_n8 +
        Rtt_n9 + Rtt_n10 - Rtt_n11 - Rtt_n12 - Rtt_n13 - Rtt_n14 - Rtt_n15 - Rtt_n16 - Rtt_n17 -
        Rtt_n18, Rtt_cd⟩) (Uf * ⟨d, Sg⟩ + Vf * ⟨sx * a ^ 2, Sg⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Rtt_n1, Rtt_n2, Rtt_n3, Rtt_n4, Rtt_n5, Rtt_n6, Rtt_n7, Rtt_n8, Rtt_n9,
        Rtt_n10, Rtt_n11, Rtt_n12, Rtt_n13, Rtt_n14, Rtt_n15, Rtt_n16, Rtt_n17, Rtt_n18, Rtt_cd,
        Uf, Vf, Nn, Sg, sx, Pp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4,
        δx_5]
    ring)

/-! ## The entry `R_{tp}` -/

/-- The common denominator of the terms of `R_{tp}`. -/
def Rtp_cd : ZExp 6 := 4 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `∂_r Γ^r_{tp}` over the common denominator. -/
def Rtp_n1 : ZExp 6 := -2 * a * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (-a ^ 4 * d * w *
    x ^ 4 + 2 * a ^ 4 * d * x ^ 4 - 2 * a ^ 4 * d * x ^ 2 + 2 * a ^ 4 * r * v * x ^ 4 - 2 *
    a ^ 4 * r * v * x ^ 2 - a ^ 4 * v ^ 2 * x ^ 4 + 2 * a ^ 2 * d ^ 2 * x ^ 2 - 2 * a ^ 2 * d *
    r ^ 2 * w * x ^ 2 - 10 * a ^ 2 * d * r ^ 2 * x ^ 2 + 10 * a ^ 2 * d * r ^ 2 + 8 * a ^ 2 * d *
    r * v * x ^ 2 + 2 * a ^ 2 * r ^ 3 * v * x ^ 2 - 2 * a ^ 2 * r ^ 3 * v - 2 * a ^ 2 * r ^ 2 *
    v ^ 2 * x ^ 2 - 10 * d ^ 2 * r ^ 2 - d * r ^ 4 * w + 8 * d * r ^ 3 * v - r ^ 4 * v ^ 2)
/-- `∂_r Γ^r_{tp}`, reduced to the common denominator. -/
theorem Rtp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δr Gr_tp) (⟨Rtp_n1, Rtp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_tp, Rtp_n1, Rtp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2,
        δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `∂_x Γ^x_{tp}` over the common denominator. -/
def Rtp_n2 : ZExp 6 := -4 * a * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 - d + r ^ 2) *
    (3 * a ^ 2 * x ^ 4 - 5 * a ^ 2 * x ^ 2 - 3 * r ^ 2 * x ^ 2 + r ^ 2)
/-- `∂_x Γ^x_{tp}`, reduced to the common denominator. -/
theorem Rtp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx Gx_tp) (⟨Rtp_n2, Rtp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_tp, Rtp_n2, Rtp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2,
        δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{tp} Γ^t_{rt}` over the common denominator. -/
def Rtp_n3 : ZExp 6 := a * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (2 * a ^ 2 * r * x ^ 2 - 2 *
    a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v) ^ 2
/-- `Γ^r_{tp} Γ^t_{rt}`, reduced to the common denominator. -/
theorem Rtp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_tp * Gt_tr) (⟨Rtp_n3, Rtp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_tp, Gt_tr, Rtp_n3, Rtp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{tp} Γ^r_{rr}` over the common denominator. -/
def Rtp_n4 : ZExp 6 := a * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 * v * x ^ 2 - 2 *
    d * r + r ^ 2 * v) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r -
    r ^ 2 * v)
/-- `Γ^r_{tp} Γ^r_{rr}`, reduced to the common denominator. -/
theorem Rtp_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_tp * Gr_rr) (⟨Rtp_n4, Rtp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rr, Gr_tp, Rtp_n4, Rtp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{tp} Γ^x_{rx}` over the common denominator. -/
def Rtp_n5 : ZExp 6 := -2 * a * d * r * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (2 *
    a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^r_{tp} Γ^x_{rx}`, reduced to the common denominator. -/
theorem Rtp_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_tp * Gx_rx) (⟨Rtp_n5, Rtp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_tp, Gx_rx, Rtp_n5, Rtp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{tp} Γ^p_{rp}` over the common denominator. -/
def Rtp_n6 : ZExp 6 := -a * (x - 1) * (x + 1) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 *
    v * x ^ 2 + 2 * d * r - r ^ 2 * v) * (2 * a ^ 4 * r * x ^ 2 - 2 * a ^ 4 * r + a ^ 4 * v *
    x ^ 4 - a ^ 4 * v * x ^ 2 + 2 * a ^ 2 * d * r + 2 * a ^ 2 * r ^ 3 * x ^ 2 - 2 * a ^ 2 *
    r ^ 3 + a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 * v + 2 * d * r ^ 3)
/-- `Γ^r_{tp} Γ^p_{rp}`, reduced to the common denominator. -/
theorem Rtp_t6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_tp * Gp_rp) (⟨Rtp_n6, Rtp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rp, Gr_tp, Rtp_n6, Rtp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{tp} Γ^t_{xt}` over the common denominator. -/
def Rtp_n7 : ZExp 6 := 4 * a ^ 3 * x ^ 2 * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 - d +
    r ^ 2) ^ 2
/-- `Γ^x_{tp} Γ^t_{xt}`, reduced to the common denominator. -/
theorem Rtp_t7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_tp * Gt_tx) (⟨Rtp_n7, Rtp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tx, Gx_tp, Rtp_n7, Rtp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{tp} Γ^r_{xr}` over the common denominator. -/
def Rtp_n8 : ZExp 6 := 4 * a ^ 3 * x ^ 2 * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 +
    r ^ 2) * (a ^ 2 - d + r ^ 2)
/-- `Γ^x_{tp} Γ^r_{xr}`, reduced to the common denominator. -/
theorem Rtp_t8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_tp * Gr_rx) (⟨Rtp_n8, Rtp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Gx_tp, Rtp_n8, Rtp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{tp} Γ^x_{xx}` over the common denominator. -/
def Rtp_n9 : ZExp 6 := -4 * a * x ^ 2 * (a ^ 2 + r ^ 2) ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 -
    d + r ^ 2)
/-- `Γ^x_{tp} Γ^x_{xx}`, reduced to the common denominator. -/
theorem Rtp_t9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_tp * Gx_xx) (⟨Rtp_n9, Rtp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_tp, Gx_xx, Rtp_n9, Rtp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{tp} Γ^p_{xp}` over the common denominator. -/
def Rtp_n10 : ZExp 6 := 4 * a * x ^ 2 * (a ^ 2 + r ^ 2) * (a ^ 2 - d + r ^ 2) * (a ^ 4 * x ^ 4 -
    a ^ 4 * x ^ 2 + a ^ 4 + a ^ 2 * d * x ^ 2 - a ^ 2 * d + a ^ 2 * r ^ 2 * x ^ 2 + a ^ 2 *
    r ^ 2 + r ^ 4)
/-- `Γ^x_{tp} Γ^p_{xp}`, reduced to the common denominator. -/
theorem Rtp_t10 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_tp * Gp_xp) (⟨Rtp_n10, Rtp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_xp, Gx_tp, Rtp_n10, Rtp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{tt} Γ^t_{pr}` over the common denominator. -/
def Rtp_n11 : ZExp 6 := -a * (x - 1) * (x + 1) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 *
    v * x ^ 2 + 2 * d * r - r ^ 2 * v) * (2 * a ^ 4 * r + a ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d * r *
    x ^ 2 - 2 * a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 + a ^ 2 * r ^ 2 * v * x ^ 2 + a ^ 2 * r ^ 2 *
    v - 4 * d * r ^ 3 + 2 * r ^ 5 + r ^ 4 * v)
/-- `Γ^r_{tt} Γ^t_{pr}`, reduced to the common denominator. -/
theorem Rtp_t11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_tt * Gt_rp) (⟨Rtp_n11, Rtp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_tt, Gt_rp, Rtp_n11, Rtp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{tt} Γ^t_{px}` over the common denominator. -/
def Rtp_n12 : ZExp 6 := -4 * a ^ 5 * x ^ 2 * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 - d + r ^ 2) ^ 2
/-- `Γ^x_{tt} Γ^t_{px}`, reduced to the common denominator. -/
theorem Rtp_t12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_tt * Gt_xp) (⟨Rtp_n12, Rtp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_xp, Gx_tt, Rtp_n12, Rtp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{tr} Γ^r_{pt}` over the common denominator. -/
def Rtp_n13 : ZExp 6 := a * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (2 * a ^ 2 * r * x ^ 2 - 2 *
    a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v) ^ 2
/-- `Γ^t_{tr} Γ^r_{pt}`, reduced to the common denominator. -/
theorem Rtp_t13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_tr * Gr_tp) (⟨Rtp_n13, Rtp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_tp, Gt_tr, Rtp_n13, Rtp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^p_{tr} Γ^r_{pp}` over the common denominator. -/
def Rtp_n14 : ZExp 6 := -a * (x - 1) * (x + 1) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 *
    v * x ^ 2 + 2 * d * r - r ^ 2 * v) * (4 * a ^ 4 * r * x ^ 2 - 2 * a ^ 4 * r + a ^ 4 * v *
    x ^ 4 - a ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d * r * x ^ 2 + 2 * a ^ 2 * d * r + 4 * a ^ 2 *
    r ^ 3 * x ^ 2 + a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 * v + 2 * r ^ 5)
/-- `Γ^p_{tr} Γ^r_{pp}`, reduced to the common denominator. -/
theorem Rtp_t14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gp_tr * Gr_pp) (⟨Rtp_n14, Rtp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_tr, Gr_pp, Rtp_n14, Rtp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{tx} Γ^x_{pt}` over the common denominator. -/
def Rtp_n15 : ZExp 6 := 4 * a ^ 3 * x ^ 2 * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 - d +
    r ^ 2) ^ 2
/-- `Γ^t_{tx} Γ^x_{pt}`, reduced to the common denominator. -/
theorem Rtp_t15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_tx * Gx_tp) (⟨Rtp_n15, Rtp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tx, Gx_tp, Rtp_n15, Rtp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^p_{tx} Γ^x_{pp}` over the common denominator. -/
def Rtp_n16 : ZExp 6 := 4 * a * x ^ 2 * (a ^ 2 - d + r ^ 2) * (a ^ 6 + a ^ 4 * d * x ^ 4 -
    a ^ 4 * d + 3 * a ^ 4 * r ^ 2 + 2 * a ^ 2 * d * r ^ 2 * x ^ 2 - 2 * a ^ 2 * d * r ^ 2 + 3 *
    a ^ 2 * r ^ 4 + r ^ 6)
/-- `Γ^p_{tx} Γ^x_{pp}`, reduced to the common denominator. -/
theorem Rtp_t16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gp_tx * Gx_pp) (⟨Rtp_n16, Rtp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_tx, Gx_pp, Rtp_n16, Rtp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{tp} Γ^p_{pr}` over the common denominator. -/
def Rtp_n17 : ZExp 6 := -a * (x - 1) * (x + 1) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 *
    v * x ^ 2 + 2 * d * r - r ^ 2 * v) * (2 * a ^ 4 * r * x ^ 2 - 2 * a ^ 4 * r + a ^ 4 * v *
    x ^ 4 - a ^ 4 * v * x ^ 2 + 2 * a ^ 2 * d * r + 2 * a ^ 2 * r ^ 3 * x ^ 2 - 2 * a ^ 2 *
    r ^ 3 + a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 * v + 2 * d * r ^ 3)
/-- `Γ^r_{tp} Γ^p_{pr}`, reduced to the common denominator. -/
theorem Rtp_t17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_tp * Gp_rp) (⟨Rtp_n17, Rtp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rp, Gr_tp, Rtp_n17, Rtp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{tp} Γ^p_{px}` over the common denominator. -/
def Rtp_n18 : ZExp 6 := 4 * a * x ^ 2 * (a ^ 2 + r ^ 2) * (a ^ 2 - d + r ^ 2) * (a ^ 4 * x ^ 4 -
    a ^ 4 * x ^ 2 + a ^ 4 + a ^ 2 * d * x ^ 2 - a ^ 2 * d + a ^ 2 * r ^ 2 * x ^ 2 + a ^ 2 *
    r ^ 2 + r ^ 4)
/-- `Γ^x_{tp} Γ^p_{px}`, reduced to the common denominator. -/
theorem Rtp_t18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_tp * Gp_xp) (⟨Rtp_n18, Rtp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_xp, Gx_tp, Rtp_n18, Rtp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R_{tp}` (`eq:offshell`): the signed sum of its terms is `-(Uf * ⟨d * a * sx, Sg⟩) - Vf *
        ⟨sx * a * Pp, Sg⟩`. -/
theorem ricci_tp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Rtp_n1 + Rtp_n2 + Rtp_n3 + Rtp_n4 + Rtp_n5 + Rtp_n6 + Rtp_n7 + Rtp_n8 +
        Rtp_n9 + Rtp_n10 - Rtp_n11 - Rtp_n12 - Rtp_n13 - Rtp_n14 - Rtp_n15 - Rtp_n16 - Rtp_n17 -
        Rtp_n18, Rtp_cd⟩) (-(Uf * ⟨d * a * sx, Sg⟩) - Vf * ⟨sx * a * Pp, Sg⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Rtp_n1, Rtp_n2, Rtp_n3, Rtp_n4, Rtp_n5, Rtp_n6, Rtp_n7, Rtp_n8, Rtp_n9,
        Rtp_n10, Rtp_n11, Rtp_n12, Rtp_n13, Rtp_n14, Rtp_n15, Rtp_n16, Rtp_n17, Rtp_n18, Rtp_cd,
        Uf, Vf, Nn, Sg, sx, Pp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4,
        δx_5]
    ring)

/-! ## The entry `R_{rr}` -/

/-- The common denominator of the terms of `R_{rr}`. -/
def Rrr_cd : ZExp 6 := 4 * d ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4

/-- The numerator of `∂_r Γ^r_{rr}` over the common denominator. -/
def Rrr_n1 : ZExp 6 := 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (-a ^ 4 * d * w * x ^ 4 + a ^ 4 *
    v ^ 2 * x ^ 4 + 2 * a ^ 2 * d ^ 2 * x ^ 2 - 2 * a ^ 2 * d * r ^ 2 * w * x ^ 2 + 2 * a ^ 2 *
    r ^ 2 * v ^ 2 * x ^ 2 - 2 * d ^ 2 * r ^ 2 - d * r ^ 4 * w + r ^ 4 * v ^ 2)
/-- `∂_r Γ^r_{rr}`, reduced to the common denominator. -/
theorem Rrr_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δr Gr_rr) (⟨Rrr_n1, Rrr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rr, Rrr_n1, Rrr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2,
        δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `∂_x Γ^x_{rr}` over the common denominator. -/
def Rrr_n2 : ZExp 6 := 4 * a ^ 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^ 2 * x ^ 4 + a ^ 2 *
    x ^ 2 + 3 * r ^ 2 * x ^ 2 - r ^ 2)
/-- `∂_x Γ^x_{rr}`, reduced to the common denominator. -/
theorem Rrr_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx Gx_rr) (⟨Rrr_n2, Rrr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rr, Rrr_n2, Rrr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2,
        δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `∂_r Γ^t_{rt}` over the common denominator. -/
def Rrr_n3 : ZExp 6 := 2 * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 6 * d * w * x ^ 4 - 2 * a ^ 6 * d *
    x ^ 4 + 2 * a ^ 6 * d * x ^ 2 + 2 * a ^ 6 * r * v * x ^ 4 - 2 * a ^ 6 * r * v * x ^ 2 -
    a ^ 6 * v ^ 2 * x ^ 4 - 2 * a ^ 4 * d ^ 2 * x ^ 2 + a ^ 4 * d * r ^ 2 * w * x ^ 4 + 2 *
    a ^ 4 * d * r ^ 2 * w * x ^ 2 - 6 * a ^ 4 * d * r ^ 2 * x ^ 4 + 12 * a ^ 4 * d * r ^ 2 *
    x ^ 2 - 6 * a ^ 4 * d * r ^ 2 + 2 * a ^ 4 * d * r * v * x ^ 4 - 2 * a ^ 4 * d * r * v *
    x ^ 2 + 2 * a ^ 4 * r ^ 3 * v * x ^ 4 - 2 * a ^ 4 * r ^ 3 * v - a ^ 4 * r ^ 2 * v ^ 2 *
    x ^ 4 - 2 * a ^ 4 * r ^ 2 * v ^ 2 * x ^ 2 - 6 * a ^ 2 * d ^ 2 * r ^ 2 * x ^ 2 + 6 * a ^ 2 *
    d ^ 2 * r ^ 2 + 2 * a ^ 2 * d * r ^ 4 * w * x ^ 2 + a ^ 2 * d * r ^ 4 * w + 2 * a ^ 2 * d *
    r ^ 4 * x ^ 2 - 2 * a ^ 2 * d * r ^ 4 + 2 * a ^ 2 * d * r ^ 3 * v * x ^ 2 - 2 * a ^ 2 * d *
    r ^ 3 * v + 2 * a ^ 2 * r ^ 5 * v * x ^ 2 - 2 * a ^ 2 * r ^ 5 * v - 2 * a ^ 2 * r ^ 4 *
    v ^ 2 * x ^ 2 - a ^ 2 * r ^ 4 * v ^ 2 + 2 * d ^ 2 * r ^ 4 + d * r ^ 6 * w - r ^ 6 * v ^ 2)
/-- `∂_r Γ^t_{rt}`, reduced to the common denominator. -/
theorem Rrr_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δr Gt_tr) (⟨Rrr_n3, Rrr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tr, Rrr_n3, Rrr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2,
        δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `∂_r Γ^r_{rr}` over the common denominator. -/
def Rrr_n4 : ZExp 6 := 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (-a ^ 4 * d * w * x ^ 4 + a ^ 4 *
    v ^ 2 * x ^ 4 + 2 * a ^ 2 * d ^ 2 * x ^ 2 - 2 * a ^ 2 * d * r ^ 2 * w * x ^ 2 + 2 * a ^ 2 *
    r ^ 2 * v ^ 2 * x ^ 2 - 2 * d ^ 2 * r ^ 2 - d * r ^ 4 * w + r ^ 4 * v ^ 2)
/-- `∂_r Γ^r_{rr}`, reduced to the common denominator. -/
theorem Rrr_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δr Gr_rr) (⟨Rrr_n4, Rrr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rr, Rrr_n4, Rrr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2,
        δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `∂_r Γ^x_{rx}` over the common denominator. -/
def Rrr_n5 : ZExp 6 := 4 * d ^ 2 * (a * x - r) * (a * x + r) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `∂_r Γ^x_{rx}`, reduced to the common denominator. -/
theorem Rrr_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δr Gx_rx) (⟨Rrr_n5, Rrr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rx, Rrr_n5, Rrr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2,
        δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `∂_r Γ^p_{rp}` over the common denominator. -/
def Rrr_n6 : ZExp 6 := -2 * (a ^ 2 * x ^ 2 + r ^ 2) * (-a ^ 6 * d * w * x ^ 6 + a ^ 6 * d * w *
    x ^ 4 - 2 * a ^ 6 * d * x ^ 4 + 2 * a ^ 6 * d * x ^ 2 + 2 * a ^ 6 * r * v * x ^ 4 - 2 *
    a ^ 6 * r * v * x ^ 2 + a ^ 6 * v ^ 2 * x ^ 6 - a ^ 6 * v ^ 2 * x ^ 4 - 2 * a ^ 4 * d ^ 2 *
    x ^ 2 - 2 * a ^ 4 * d * r ^ 2 * w * x ^ 4 + 2 * a ^ 4 * d * r ^ 2 * w * x ^ 2 - 6 * a ^ 4 *
    d * r ^ 2 * x ^ 4 + 12 * a ^ 4 * d * r ^ 2 * x ^ 2 - 6 * a ^ 4 * d * r ^ 2 + 2 * a ^ 4 * d *
    r * v * x ^ 4 - 2 * a ^ 4 * d * r * v * x ^ 2 + 2 * a ^ 4 * r ^ 3 * v * x ^ 4 - 2 * a ^ 4 *
    r ^ 3 * v + 2 * a ^ 4 * r ^ 2 * v ^ 2 * x ^ 4 - 2 * a ^ 4 * r ^ 2 * v ^ 2 * x ^ 2 - 6 *
    a ^ 2 * d ^ 2 * r ^ 2 * x ^ 2 + 6 * a ^ 2 * d ^ 2 * r ^ 2 - a ^ 2 * d * r ^ 4 * w * x ^ 2 +
    a ^ 2 * d * r ^ 4 * w + 2 * a ^ 2 * d * r ^ 4 * x ^ 2 - 2 * a ^ 2 * d * r ^ 4 + 2 * a ^ 2 *
    d * r ^ 3 * v * x ^ 2 - 2 * a ^ 2 * d * r ^ 3 * v + 2 * a ^ 2 * r ^ 5 * v * x ^ 2 - 2 *
    a ^ 2 * r ^ 5 * v + a ^ 2 * r ^ 4 * v ^ 2 * x ^ 2 - a ^ 2 * r ^ 4 * v ^ 2 + 2 * d ^ 2 * r ^ 4)
/-- `∂_r Γ^p_{rp}`, reduced to the common denominator. -/
theorem Rrr_t6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δr Gp_rp) (⟨Rrr_n6, Rrr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rp, Rrr_n6, Rrr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2,
        δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{rr} Γ^t_{rt}` over the common denominator. -/
def Rrr_n7 : ZExp 6 := (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 * v * x ^ 2 - 2 * d *
    r + r ^ 2 * v) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r -
    r ^ 2 * v)
/-- `Γ^r_{rr} Γ^t_{rt}`, reduced to the common denominator. -/
theorem Rrr_t7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_rr * Gt_tr) (⟨Rrr_n7, Rrr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rr, Gt_tr, Rrr_n7, Rrr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{rr} Γ^r_{rr}` over the common denominator. -/
def Rrr_n8 : ZExp 6 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^ 2 * v * x ^ 2 - 2 * d * r + r ^ 2 * v) ^ 2
/-- `Γ^r_{rr} Γ^r_{rr}`, reduced to the common denominator. -/
theorem Rrr_t8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_rr * Gr_rr) (⟨Rrr_n8, Rrr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rr, Rrr_n8, Rrr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2,
        δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{rr} Γ^x_{rx}` over the common denominator. -/
def Rrr_n9 : ZExp 6 := -2 * d * r * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^ 2 * v * x ^ 2 - 2 * d *
    r + r ^ 2 * v)
/-- `Γ^r_{rr} Γ^x_{rx}`, reduced to the common denominator. -/
theorem Rrr_t9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_rr * Gx_rx) (⟨Rrr_n9, Rrr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rr, Gx_rx, Rrr_n9, Rrr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{rr} Γ^p_{rp}` over the common denominator. -/
def Rrr_n10 : ZExp 6 := -(a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 * v * x ^ 2 - 2 * d * r + r ^ 2 * v) *
    (2 * a ^ 4 * r * x ^ 2 - 2 * a ^ 4 * r + a ^ 4 * v * x ^ 4 - a ^ 4 * v * x ^ 2 + 2 * a ^ 2 *
    d * r + 2 * a ^ 2 * r ^ 3 * x ^ 2 - 2 * a ^ 2 * r ^ 3 + a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 *
    r ^ 2 * v + 2 * d * r ^ 3)
/-- `Γ^r_{rr} Γ^p_{rp}`, reduced to the common denominator. -/
theorem Rrr_t10 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_rr * Gp_rp) (⟨Rrr_n10, Rrr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rp, Gr_rr, Rrr_n10, Rrr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{rr} Γ^t_{xt}` over the common denominator. -/
def Rrr_n11 : ZExp 6 := 4 * a ^ 4 * d * x ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) *
    (a ^ 2 - d + r ^ 2)
/-- `Γ^x_{rr} Γ^t_{xt}`, reduced to the common denominator. -/
theorem Rrr_t11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_rr * Gt_tx) (⟨Rrr_n11, Rrr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tx, Gx_rr, Rrr_n11, Rrr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{rr} Γ^r_{xr}` over the common denominator. -/
def Rrr_n12 : ZExp 6 := 4 * a ^ 4 * d * x ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `Γ^x_{rr} Γ^r_{xr}`, reduced to the common denominator. -/
theorem Rrr_t12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_rr * Gr_rx) (⟨Rrr_n12, Rrr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Gx_rr, Rrr_n12, Rrr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{rr} Γ^x_{xx}` over the common denominator. -/
def Rrr_n13 : ZExp 6 := -4 * a ^ 2 * d * x ^ 2 * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `Γ^x_{rr} Γ^x_{xx}`, reduced to the common denominator. -/
theorem Rrr_t13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_rr * Gx_xx) (⟨Rrr_n13, Rrr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rr, Gx_xx, Rrr_n13, Rrr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{rr} Γ^p_{xp}` over the common denominator. -/
def Rrr_n14 : ZExp 6 := 4 * a ^ 2 * d * x ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 4 * x ^ 4 -
    a ^ 4 * x ^ 2 + a ^ 4 + a ^ 2 * d * x ^ 2 - a ^ 2 * d + a ^ 2 * r ^ 2 * x ^ 2 + a ^ 2 *
    r ^ 2 + r ^ 4)
/-- `Γ^x_{rr} Γ^p_{xp}`, reduced to the common denominator. -/
theorem Rrr_t14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_rr * Gp_xp) (⟨Rrr_n14, Rrr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_xp, Gx_rr, Rrr_n14, Rrr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{rt} Γ^t_{rt}` over the common denominator. -/
def Rrr_n15 : ZExp 6 := (a ^ 2 + r ^ 2) ^ 2 * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 *
    v * x ^ 2 + 2 * d * r - r ^ 2 * v) ^ 2
/-- `Γ^t_{rt} Γ^t_{rt}`, reduced to the common denominator. -/
theorem Rrr_t15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_tr * Gt_tr) (⟨Rrr_n15, Rrr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tr, Rrr_n15, Rrr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1,
        δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^p_{rt} Γ^t_{rp}` over the common denominator. -/
def Rrr_n16 : ZExp 6 := -a ^ 2 * (x - 1) * (x + 1) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r -
    a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v) * (2 * a ^ 4 * r + a ^ 4 * v * x ^ 2 - 2 * a ^ 2 *
    d * r * x ^ 2 - 2 * a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 + a ^ 2 * r ^ 2 * v * x ^ 2 + a ^ 2 *
    r ^ 2 * v - 4 * d * r ^ 3 + 2 * r ^ 5 + r ^ 4 * v)
/-- `Γ^p_{rt} Γ^t_{rp}`, reduced to the common denominator. -/
theorem Rrr_t16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gp_tr * Gt_rp) (⟨Rrr_n16, Rrr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_tr, Gt_rp, Rrr_n16, Rrr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{rr} Γ^r_{rr}` over the common denominator. -/
def Rrr_n17 : ZExp 6 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^ 2 * v * x ^ 2 - 2 * d * r + r ^ 2 *
    v) ^ 2
/-- `Γ^r_{rr} Γ^r_{rr}`, reduced to the common denominator. -/
theorem Rrr_t17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_rr * Gr_rr) (⟨Rrr_n17, Rrr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rr, Rrr_n17, Rrr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1,
        δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{rr} Γ^r_{rx}` over the common denominator. -/
def Rrr_n18 : ZExp 6 := 4 * a ^ 4 * d * x ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `Γ^x_{rr} Γ^r_{rx}`, reduced to the common denominator. -/
theorem Rrr_t18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_rr * Gr_rx) (⟨Rrr_n18, Rrr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Gx_rr, Rrr_n18, Rrr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{rx} Γ^x_{rr}` over the common denominator. -/
def Rrr_n19 : ZExp 6 := 4 * a ^ 4 * d * x ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `Γ^r_{rx} Γ^x_{rr}`, reduced to the common denominator. -/
theorem Rrr_t19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_rx * Gx_rr) (⟨Rrr_n19, Rrr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Gx_rr, Rrr_n19, Rrr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{rx} Γ^x_{rx}` over the common denominator. -/
def Rrr_n20 : ZExp 6 := 4 * d ^ 2 * r ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `Γ^x_{rx} Γ^x_{rx}`, reduced to the common denominator. -/
theorem Rrr_t20 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_rx * Gx_rx) (⟨Rrr_n20, Rrr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rx, Rrr_n20, Rrr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1,
        δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{rp} Γ^p_{rt}` over the common denominator. -/
def Rrr_n21 : ZExp 6 := -a ^ 2 * (x - 1) * (x + 1) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r -
    a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v) * (2 * a ^ 4 * r + a ^ 4 * v * x ^ 2 - 2 * a ^ 2 *
    d * r * x ^ 2 - 2 * a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 + a ^ 2 * r ^ 2 * v * x ^ 2 + a ^ 2 *
    r ^ 2 * v - 4 * d * r ^ 3 + 2 * r ^ 5 + r ^ 4 * v)
/-- `Γ^t_{rp} Γ^p_{rt}`, reduced to the common denominator. -/
theorem Rrr_t21 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_rp * Gp_tr) (⟨Rrr_n21, Rrr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_tr, Gt_rp, Rrr_n21, Rrr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^p_{rp} Γ^p_{rp}` over the common denominator. -/
def Rrr_n22 : ZExp 6 := (2 * a ^ 4 * r * x ^ 2 - 2 * a ^ 4 * r + a ^ 4 * v * x ^ 4 - a ^ 4 * v *
    x ^ 2 + 2 * a ^ 2 * d * r + 2 * a ^ 2 * r ^ 3 * x ^ 2 - 2 * a ^ 2 * r ^ 3 + a ^ 2 * r ^ 2 *
    v * x ^ 2 - a ^ 2 * r ^ 2 * v + 2 * d * r ^ 3) ^ 2
/-- `Γ^p_{rp} Γ^p_{rp}`, reduced to the common denominator. -/
theorem Rrr_t22 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gp_rp * Gp_rp) (⟨Rrr_n22, Rrr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rp, Rrr_n22, Rrr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1,
        δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R_{rr}` (`eq:offshell`): the signed sum of its terms is `-(Uf * ⟨Sg, d⟩)`. -/
theorem ricci_rr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Rrr_n1 + Rrr_n2 - Rrr_n3 - Rrr_n4 - Rrr_n5 - Rrr_n6 + Rrr_n7 + Rrr_n8 +
        Rrr_n9 + Rrr_n10 + Rrr_n11 + Rrr_n12 + Rrr_n13 + Rrr_n14 - Rrr_n15 - Rrr_n16 - Rrr_n17 -
        Rrr_n18 - Rrr_n19 - Rrr_n20 - Rrr_n21 - Rrr_n22, Rrr_cd⟩) (-(Uf * ⟨Sg, d⟩)))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Rrr_n1, Rrr_n2, Rrr_n3, Rrr_n4, Rrr_n5, Rrr_n6, Rrr_n7, Rrr_n8, Rrr_n9,
        Rrr_n10, Rrr_n11, Rrr_n12, Rrr_n13, Rrr_n14, Rrr_n15, Rrr_n16, Rrr_n17, Rrr_n18, Rrr_n19,
        Rrr_n20, Rrr_n21, Rrr_n22, Rrr_cd, Uf, Vf, Nn, Sg, sx, Pp, δr_0, δr_1, δr_2, δr_3, δr_4,
        δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ## The entry `R_{rx}` -/

/-- The common denominator of the terms of `R_{rx}`. -/
def Rrx_cd : ZExp 6 := 2 * d * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4

/-- The numerator of `∂_r Γ^r_{rx}` over the common denominator. -/
def Rrx_n1 : ZExp 6 := -4 * a ^ 2 * d * r * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `∂_r Γ^r_{rx}`, reduced to the common denominator. -/
theorem Rrx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δr Gr_rx) (⟨Rrx_n1, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Rrx_n1, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2,
        δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `∂_x Γ^x_{rx}` over the common denominator. -/
def Rrx_n2 : ZExp 6 := -4 * a ^ 2 * d * r * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `∂_x Γ^x_{rx}`, reduced to the common denominator. -/
theorem Rrx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx Gx_rx) (⟨Rrx_n2, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rx, Rrx_n2, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2,
        δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `∂_x Γ^t_{rt}` over the common denominator. -/
def Rrx_n3 : ZExp 6 := 2 * a ^ 2 * x * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 +
    r ^ 2) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 -
    r ^ 2 * v)
/-- `∂_x Γ^t_{rt}`, reduced to the common denominator. -/
theorem Rrx_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx Gt_tr) (⟨Rrx_n3, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tr, Rrx_n3, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2,
        δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `∂_x Γ^r_{rr}` over the common denominator. -/
def Rrx_n4 : ZExp 6 := -4 * a ^ 2 * d * r * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `∂_x Γ^r_{rr}`, reduced to the common denominator. -/
theorem Rrx_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx Gr_rr) (⟨Rrx_n4, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rr, Rrx_n4, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2,
        δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `∂_x Γ^x_{rx}` over the common denominator. -/
def Rrx_n5 : ZExp 6 := -4 * a ^ 2 * d * r * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `∂_x Γ^x_{rx}`, reduced to the common denominator. -/
theorem Rrx_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx Gx_rx) (⟨Rrx_n5, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rx, Rrx_n5, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2,
        δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `∂_x Γ^p_{rp}` over the common denominator. -/
def Rrx_n6 : ZExp 6 := -2 * a ^ 2 * x * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 +
    r ^ 2) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 -
    r ^ 2 * v)
/-- `∂_x Γ^p_{rp}`, reduced to the common denominator. -/
theorem Rrx_t6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx Gp_rp) (⟨Rrx_n6, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rp, Rrx_n6, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2,
        δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{rx} Γ^t_{rt}` over the common denominator. -/
def Rrx_n7 : ZExp 6 := -a ^ 2 * x * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 +
    r ^ 2) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^r_{rx} Γ^t_{rt}`, reduced to the common denominator. -/
theorem Rrx_t7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_rx * Gt_tr) (⟨Rrx_n7, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Gt_tr, Rrx_n7, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{rx} Γ^r_{rr}` over the common denominator. -/
def Rrx_n8 : ZExp 6 := -a ^ 2 * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^ 2 *
    v * x ^ 2 - 2 * d * r + r ^ 2 * v)
/-- `Γ^r_{rx} Γ^r_{rr}`, reduced to the common denominator. -/
theorem Rrx_t8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_rx * Gr_rr) (⟨Rrx_n8, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rr, Gr_rx, Rrx_n8, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{rx} Γ^x_{rx}` over the common denominator. -/
def Rrx_n9 : ZExp 6 := 2 * a ^ 2 * d * r * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `Γ^r_{rx} Γ^x_{rx}`, reduced to the common denominator. -/
theorem Rrx_t9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_rx * Gx_rx) (⟨Rrx_n9, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Gx_rx, Rrx_n9, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{rx} Γ^p_{rp}` over the common denominator. -/
def Rrx_n10 : ZExp 6 := a ^ 2 * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (2 * a ^ 4 *
    r * x ^ 2 - 2 * a ^ 4 * r + a ^ 4 * v * x ^ 4 - a ^ 4 * v * x ^ 2 + 2 * a ^ 2 * d * r + 2 *
    a ^ 2 * r ^ 3 * x ^ 2 - 2 * a ^ 2 * r ^ 3 + a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 * v +
    2 * d * r ^ 3)
/-- `Γ^r_{rx} Γ^p_{rp}`, reduced to the common denominator. -/
theorem Rrx_t10 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_rx * Gp_rp) (⟨Rrx_n10, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rp, Gr_rx, Rrx_n10, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{rx} Γ^t_{xt}` over the common denominator. -/
def Rrx_n11 : ZExp 6 := 2 * a ^ 2 * d * r * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) *
    (a ^ 2 - d + r ^ 2)
/-- `Γ^x_{rx} Γ^t_{xt}`, reduced to the common denominator. -/
theorem Rrx_t11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_rx * Gt_tx) (⟨Rrx_n11, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tx, Gx_rx, Rrx_n11, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{rx} Γ^r_{xr}` over the common denominator. -/
def Rrx_n12 : ZExp 6 := 2 * a ^ 2 * d * r * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `Γ^x_{rx} Γ^r_{xr}`, reduced to the common denominator. -/
theorem Rrx_t12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_rx * Gr_rx) (⟨Rrx_n12, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Gx_rx, Rrx_n12, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{rx} Γ^x_{xx}` over the common denominator. -/
def Rrx_n13 : ZExp 6 := -2 * d * r * x * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `Γ^x_{rx} Γ^x_{xx}`, reduced to the common denominator. -/
theorem Rrx_t13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_rx * Gx_xx) (⟨Rrx_n13, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rx, Gx_xx, Rrx_n13, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{rx} Γ^p_{xp}` over the common denominator. -/
def Rrx_n14 : ZExp 6 := 2 * d * r * x * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 4 * x ^ 4 - a ^ 4 *
    x ^ 2 + a ^ 4 + a ^ 2 * d * x ^ 2 - a ^ 2 * d + a ^ 2 * r ^ 2 * x ^ 2 + a ^ 2 * r ^ 2 + r ^ 4)
/-- `Γ^x_{rx} Γ^p_{xp}`, reduced to the common denominator. -/
theorem Rrx_t14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_rx * Gp_xp) (⟨Rrx_n14, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_xp, Gx_rx, Rrx_n14, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{rt} Γ^t_{xt}` over the common denominator. -/
def Rrx_n15 : ZExp 6 := -a ^ 2 * x * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) *
    (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^t_{rt} Γ^t_{xt}`, reduced to the common denominator. -/
theorem Rrx_t15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_tr * Gt_tx) (⟨Rrx_n15, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tr, Gt_tx, Rrx_n15, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^p_{rt} Γ^t_{xp}` over the common denominator. -/
def Rrx_n16 : ZExp 6 := -a ^ 4 * x * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 - d + r ^ 2) * (2 *
    a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^p_{rt} Γ^t_{xp}`, reduced to the common denominator. -/
theorem Rrx_t16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gp_tr * Gt_xp) (⟨Rrx_n16, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_tr, Gt_xp, Rrx_n16, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{rr} Γ^r_{xr}` over the common denominator. -/
def Rrx_n17 : ZExp 6 := -a ^ 2 * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^ 2 *
    v * x ^ 2 - 2 * d * r + r ^ 2 * v)
/-- `Γ^r_{rr} Γ^r_{xr}`, reduced to the common denominator. -/
theorem Rrx_t17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_rr * Gr_rx) (⟨Rrx_n17, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rr, Gr_rx, Rrx_n17, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{rr} Γ^r_{xx}` over the common denominator. -/
def Rrx_n18 : ZExp 6 := 2 * a ^ 2 * d * r * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `Γ^x_{rr} Γ^r_{xx}`, reduced to the common denominator. -/
theorem Rrx_t18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_rr * Gr_xx) (⟨Rrx_n18, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_xx, Gx_rr, Rrx_n18, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{rx} Γ^x_{xr}` over the common denominator. -/
def Rrx_n19 : ZExp 6 := 2 * a ^ 2 * d * r * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `Γ^r_{rx} Γ^x_{xr}`, reduced to the common denominator. -/
theorem Rrx_t19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_rx * Gx_rx) (⟨Rrx_n19, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Gx_rx, Rrx_n19, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{rx} Γ^x_{xx}` over the common denominator. -/
def Rrx_n20 : ZExp 6 := -2 * d * r * x * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `Γ^x_{rx} Γ^x_{xx}`, reduced to the common denominator. -/
theorem Rrx_t20 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_rx * Gx_xx) (⟨Rrx_n20, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rx, Gx_xx, Rrx_n20, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{rp} Γ^p_{xt}` over the common denominator. -/
def Rrx_n21 : ZExp 6 := -a ^ 2 * x * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) * (2 * a ^ 4 * r +
    a ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d * r * x ^ 2 - 2 * a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 +
    a ^ 2 * r ^ 2 * v * x ^ 2 + a ^ 2 * r ^ 2 * v - 4 * d * r ^ 3 + 2 * r ^ 5 + r ^ 4 * v)
/-- `Γ^t_{rp} Γ^p_{xt}`, reduced to the common denominator. -/
theorem Rrx_t21 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_rp * Gp_tx) (⟨Rrx_n21, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_tx, Gt_rp, Rrx_n21, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^p_{rp} Γ^p_{xp}` over the common denominator. -/
def Rrx_n22 : ZExp 6 := x * (a ^ 4 * x ^ 4 - a ^ 4 * x ^ 2 + a ^ 4 + a ^ 2 * d * x ^ 2 - a ^ 2 *
    d + a ^ 2 * r ^ 2 * x ^ 2 + a ^ 2 * r ^ 2 + r ^ 4) * (2 * a ^ 4 * r * x ^ 2 - 2 * a ^ 4 * r +
    a ^ 4 * v * x ^ 4 - a ^ 4 * v * x ^ 2 + 2 * a ^ 2 * d * r + 2 * a ^ 2 * r ^ 3 * x ^ 2 - 2 *
    a ^ 2 * r ^ 3 + a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 * v + 2 * d * r ^ 3)
/-- `Γ^p_{rp} Γ^p_{xp}`, reduced to the common denominator. -/
theorem Rrx_t22 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gp_rp * Gp_xp) (⟨Rrx_n22, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rp, Gp_xp, Rrx_n22, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R_{rx}` (`eq:offshell`): the signed sum of its terms is `Frac.ofZ 0`. -/
theorem ricci_rx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Rrx_n1 + Rrx_n2 - Rrx_n3 - Rrx_n4 - Rrx_n5 - Rrx_n6 + Rrx_n7 + Rrx_n8 +
        Rrx_n9 + Rrx_n10 + Rrx_n11 + Rrx_n12 + Rrx_n13 + Rrx_n14 - Rrx_n15 - Rrx_n16 - Rrx_n17 -
        Rrx_n18 - Rrx_n19 - Rrx_n20 - Rrx_n21 - Rrx_n22, Rrx_cd⟩) (Frac.ofZ 0))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Rrx_n1, Rrx_n2, Rrx_n3, Rrx_n4, Rrx_n5, Rrx_n6, Rrx_n7, Rrx_n8, Rrx_n9,
        Rrx_n10, Rrx_n11, Rrx_n12, Rrx_n13, Rrx_n14, Rrx_n15, Rrx_n16, Rrx_n17, Rrx_n18, Rrx_n19,
        Rrx_n20, Rrx_n21, Rrx_n22, Rrx_cd, Uf, Vf, Nn, Sg, sx, Pp, δr_0, δr_1, δr_2, δr_3, δr_4,
        δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ## The entry `R_{xx}` -/

/-- The common denominator of the terms of `R_{xx}`. -/
def Rxx_cd : ZExp 6 := 2 * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4

/-- The numerator of `∂_r Γ^r_{xx}` over the common denominator. -/
def Rxx_n1 : ZExp 6 := 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^ 2 * d * x ^ 2 +
    a ^ 2 * r * v * x ^ 2 - d * r ^ 2 + r ^ 3 * v)
/-- `∂_r Γ^r_{xx}`, reduced to the common denominator. -/
theorem Rxx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δr Gr_xx) (⟨Rxx_n1, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_xx, Rxx_n1, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2,
        δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `∂_x Γ^x_{xx}` over the common denominator. -/
def Rxx_n2 : ZExp 6 := 2 * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (3 * a ^ 2 * x ^ 4 -
    a ^ 2 * x ^ 2 + r ^ 2 * x ^ 2 + r ^ 2)
/-- `∂_x Γ^x_{xx}`, reduced to the common denominator. -/
theorem Rxx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx Gx_xx) (⟨Rxx_n2, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_xx, Rxx_n2, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2,
        δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `∂_x Γ^t_{xt}` over the common denominator. -/
def Rxx_n3 : ZExp 6 := -2 * a ^ 2 * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) * (3 *
    a ^ 2 * x ^ 2 - r ^ 2) * (a ^ 2 - d + r ^ 2)
/-- `∂_x Γ^t_{xt}`, reduced to the common denominator. -/
theorem Rxx_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx Gt_tx) (⟨Rxx_n3, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tx, Rxx_n3, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2,
        δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `∂_x Γ^r_{xr}` over the common denominator. -/
def Rxx_n4 : ZExp 6 := -2 * a ^ 2 * (x - 1) ^ 2 * (x + 1) ^ 2 * (a * x - r) * (a * x + r) *
    (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `∂_x Γ^r_{xr}`, reduced to the common denominator. -/
theorem Rxx_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx Gr_rx) (⟨Rxx_n4, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Rxx_n4, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2,
        δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `∂_x Γ^x_{xx}` over the common denominator. -/
def Rxx_n5 : ZExp 6 := 2 * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (3 * a ^ 2 * x ^ 4 -
    a ^ 2 * x ^ 2 + r ^ 2 * x ^ 2 + r ^ 2)
/-- `∂_x Γ^x_{xx}`, reduced to the common denominator. -/
theorem Rxx_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx Gx_xx) (⟨Rxx_n5, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_xx, Rxx_n5, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2,
        δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `∂_x Γ^p_{xp}` over the common denominator. -/
def Rxx_n6 : ZExp 6 := -2 * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 6 * x ^ 8 - 2 * a ^ 6 * x ^ 6 + 6 *
    a ^ 6 * x ^ 4 - 3 * a ^ 6 * x ^ 2 + 3 * a ^ 4 * d * x ^ 6 - 6 * a ^ 4 * d * x ^ 4 + 3 *
    a ^ 4 * d * x ^ 2 + 10 * a ^ 4 * r ^ 2 * x ^ 4 - 5 * a ^ 4 * r ^ 2 * x ^ 2 + a ^ 4 * r ^ 2 -
    a ^ 2 * d * r ^ 2 * x ^ 4 + 2 * a ^ 2 * d * r ^ 2 * x ^ 2 - a ^ 2 * d * r ^ 2 + 4 * a ^ 2 *
    r ^ 4 * x ^ 4 + a ^ 2 * r ^ 4 * x ^ 2 + a ^ 2 * r ^ 4 + r ^ 6 * x ^ 2 + r ^ 6)
/-- `∂_x Γ^p_{xp}`, reduced to the common denominator. -/
theorem Rxx_t6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx Gp_xp) (⟨Rxx_n6, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_xp, Rxx_n6, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2,
        δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{xx} Γ^t_{rt}` over the common denominator. -/
def Rxx_n7 : ZExp 6 := -r * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (2 *
    a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^r_{xx} Γ^t_{rt}`, reduced to the common denominator. -/
theorem Rxx_t7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_xx * Gt_tr) (⟨Rxx_n7, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_xx, Gt_tr, Rxx_n7, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{xx} Γ^r_{rr}` over the common denominator. -/
def Rxx_n8 : ZExp 6 := -r * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^ 2 * v *
    x ^ 2 - 2 * d * r + r ^ 2 * v)
/-- `Γ^r_{xx} Γ^r_{rr}`, reduced to the common denominator. -/
theorem Rxx_t8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_xx * Gr_rr) (⟨Rxx_n8, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rr, Gr_xx, Rxx_n8, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{xx} Γ^x_{rx}` over the common denominator. -/
def Rxx_n9 : ZExp 6 := 2 * d * r ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `Γ^r_{xx} Γ^x_{rx}`, reduced to the common denominator. -/
theorem Rxx_t9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_xx * Gx_rx) (⟨Rxx_n9, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_xx, Gx_rx, Rxx_n9, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{xx} Γ^p_{rp}` over the common denominator. -/
def Rxx_n10 : ZExp 6 := r * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (2 * a ^ 4 * r *
    x ^ 2 - 2 * a ^ 4 * r + a ^ 4 * v * x ^ 4 - a ^ 4 * v * x ^ 2 + 2 * a ^ 2 * d * r + 2 *
    a ^ 2 * r ^ 3 * x ^ 2 - 2 * a ^ 2 * r ^ 3 + a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 * v +
    2 * d * r ^ 3)
/-- `Γ^r_{xx} Γ^p_{rp}`, reduced to the common denominator. -/
theorem Rxx_t10 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_xx * Gp_rp) (⟨Rxx_n10, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rp, Gr_xx, Rxx_n10, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{xx} Γ^t_{xt}` over the common denominator. -/
def Rxx_n11 : ZExp 6 := -2 * a ^ 2 * x ^ 2 * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 *
    x ^ 2 + r ^ 2) * (a ^ 2 - d + r ^ 2)
/-- `Γ^x_{xx} Γ^t_{xt}`, reduced to the common denominator. -/
theorem Rxx_t11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_xx * Gt_tx) (⟨Rxx_n11, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tx, Gx_xx, Rxx_n11, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{xx} Γ^r_{xr}` over the common denominator. -/
def Rxx_n12 : ZExp 6 := -2 * a ^ 2 * x ^ 2 * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 *
    x ^ 2 + r ^ 2) ^ 2
/-- `Γ^x_{xx} Γ^r_{xr}`, reduced to the common denominator. -/
theorem Rxx_t12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_xx * Gr_rx) (⟨Rxx_n12, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Gx_xx, Rxx_n12, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{xx} Γ^x_{xx}` over the common denominator. -/
def Rxx_n13 : ZExp 6 := 2 * x ^ 2 * (a ^ 2 + r ^ 2) ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `Γ^x_{xx} Γ^x_{xx}`, reduced to the common denominator. -/
theorem Rxx_t13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_xx * Gx_xx) (⟨Rxx_n13, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_xx, Rxx_n13, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1,
        δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{xx} Γ^p_{xp}` over the common denominator. -/
def Rxx_n14 : ZExp 6 := -2 * x ^ 2 * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 4 * x ^ 4 -
    a ^ 4 * x ^ 2 + a ^ 4 + a ^ 2 * d * x ^ 2 - a ^ 2 * d + a ^ 2 * r ^ 2 * x ^ 2 + a ^ 2 *
    r ^ 2 + r ^ 4)
/-- `Γ^x_{xx} Γ^p_{xp}`, reduced to the common denominator. -/
theorem Rxx_t14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_xx * Gp_xp) (⟨Rxx_n14, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_xp, Gx_xx, Rxx_n14, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{xt} Γ^t_{xt}` over the common denominator. -/
def Rxx_n15 : ZExp 6 := 2 * a ^ 4 * x ^ 2 * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 - d + r ^ 2) ^ 2
/-- `Γ^t_{xt} Γ^t_{xt}`, reduced to the common denominator. -/
theorem Rxx_t15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_tx * Gt_tx) (⟨Rxx_n15, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tx, Rxx_n15, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1,
        δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^p_{xt} Γ^t_{xp}` over the common denominator. -/
def Rxx_n16 : ZExp 6 := -2 * a ^ 4 * x ^ 2 * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 - d + r ^ 2) ^ 2
/-- `Γ^p_{xt} Γ^t_{xp}`, reduced to the common denominator. -/
theorem Rxx_t16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gp_tx * Gt_xp) (⟨Rxx_n16, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_tx, Gt_xp, Rxx_n16, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{xr} Γ^r_{xr}` over the common denominator. -/
def Rxx_n17 : ZExp 6 := 2 * a ^ 4 * x ^ 2 * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `Γ^r_{xr} Γ^r_{xr}`, reduced to the common denominator. -/
theorem Rxx_t17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_rx * Gr_rx) (⟨Rxx_n17, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Rxx_n17, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1,
        δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{xr} Γ^r_{xx}` over the common denominator. -/
def Rxx_n18 : ZExp 6 := 2 * d * r ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `Γ^x_{xr} Γ^r_{xx}`, reduced to the common denominator. -/
theorem Rxx_t18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_rx * Gr_xx) (⟨Rxx_n18, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_xx, Gx_rx, Rxx_n18, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{xx} Γ^x_{xr}` over the common denominator. -/
def Rxx_n19 : ZExp 6 := 2 * d * r ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `Γ^r_{xx} Γ^x_{xr}`, reduced to the common denominator. -/
theorem Rxx_t19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_xx * Gx_rx) (⟨Rxx_n19, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_xx, Gx_rx, Rxx_n19, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{xx} Γ^x_{xx}` over the common denominator. -/
def Rxx_n20 : ZExp 6 := 2 * x ^ 2 * (a ^ 2 + r ^ 2) ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `Γ^x_{xx} Γ^x_{xx}`, reduced to the common denominator. -/
theorem Rxx_t20 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_xx * Gx_xx) (⟨Rxx_n20, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_xx, Rxx_n20, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1,
        δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{xp} Γ^p_{xt}` over the common denominator. -/
def Rxx_n21 : ZExp 6 := -2 * a ^ 4 * x ^ 2 * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 - d + r ^ 2) ^ 2
/-- `Γ^t_{xp} Γ^p_{xt}`, reduced to the common denominator. -/
theorem Rxx_t21 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_xp * Gp_tx) (⟨Rxx_n21, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_tx, Gt_xp, Rxx_n21, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^p_{xp} Γ^p_{xp}` over the common denominator. -/
def Rxx_n22 : ZExp 6 := 2 * x ^ 2 * (a ^ 4 * x ^ 4 - a ^ 4 * x ^ 2 + a ^ 4 + a ^ 2 * d * x ^ 2 -
    a ^ 2 * d + a ^ 2 * r ^ 2 * x ^ 2 + a ^ 2 * r ^ 2 + r ^ 4) ^ 2
/-- `Γ^p_{xp} Γ^p_{xp}`, reduced to the common denominator. -/
theorem Rxx_t22 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gp_xp * Gp_xp) (⟨Rxx_n22, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_xp, Rxx_n22, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1,
        δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R_{xx}` (`eq:offshell`): the signed sum of its terms is `Vf * ⟨Sg, sx⟩`. -/
theorem ricci_xx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Rxx_n1 + Rxx_n2 - Rxx_n3 - Rxx_n4 - Rxx_n5 - Rxx_n6 + Rxx_n7 + Rxx_n8 +
        Rxx_n9 + Rxx_n10 + Rxx_n11 + Rxx_n12 + Rxx_n13 + Rxx_n14 - Rxx_n15 - Rxx_n16 - Rxx_n17 -
        Rxx_n18 - Rxx_n19 - Rxx_n20 - Rxx_n21 - Rxx_n22, Rxx_cd⟩) (Vf * ⟨Sg, sx⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Rxx_n1, Rxx_n2, Rxx_n3, Rxx_n4, Rxx_n5, Rxx_n6, Rxx_n7, Rxx_n8, Rxx_n9,
        Rxx_n10, Rxx_n11, Rxx_n12, Rxx_n13, Rxx_n14, Rxx_n15, Rxx_n16, Rxx_n17, Rxx_n18, Rxx_n19,
        Rxx_n20, Rxx_n21, Rxx_n22, Rxx_cd, Uf, Vf, Nn, Sg, sx, Pp, δr_0, δr_1, δr_2, δr_3, δr_4,
        δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ## The entry `R_{pp}` -/

/-- The common denominator of the terms of `R_{pp}`. -/
def Rpp_cd : ZExp 6 := 4 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `∂_r Γ^r_{pp}` over the common denominator. -/
def Rpp_n1 : ZExp 6 := 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 6 * d * w * x ^ 6 -
    a ^ 6 * d * w * x ^ 4 + 4 * a ^ 6 * d * x ^ 4 - 2 * a ^ 6 * d * x ^ 2 + 4 * a ^ 6 * r * v *
    x ^ 4 - 2 * a ^ 6 * r * v * x ^ 2 + a ^ 6 * v ^ 2 * x ^ 6 - a ^ 6 * v ^ 2 * x ^ 4 - 2 *
    a ^ 4 * d ^ 2 * x ^ 4 + 2 * a ^ 4 * d ^ 2 * x ^ 2 + 2 * a ^ 4 * d * r ^ 2 * w * x ^ 4 - 2 *
    a ^ 4 * d * r ^ 2 * w * x ^ 2 + 12 * a ^ 4 * d * r ^ 2 * x ^ 4 - 20 * a ^ 4 * d * r ^ 2 *
    x ^ 2 + 10 * a ^ 4 * d * r ^ 2 - 8 * a ^ 4 * d * r * v * x ^ 4 + 8 * a ^ 4 * d * r * v *
    x ^ 2 + 4 * a ^ 4 * r ^ 3 * v * x ^ 4 + 4 * a ^ 4 * r ^ 3 * v * x ^ 2 - 2 * a ^ 4 * r ^ 3 *
    v + 2 * a ^ 4 * r ^ 2 * v ^ 2 * x ^ 4 - 2 * a ^ 4 * r ^ 2 * v ^ 2 * x ^ 2 + 10 * a ^ 2 *
    d ^ 2 * r ^ 2 * x ^ 2 - 10 * a ^ 2 * d ^ 2 * r ^ 2 + a ^ 2 * d * r ^ 4 * w * x ^ 2 - a ^ 2 *
    d * r ^ 4 * w - 2 * a ^ 2 * d * r ^ 4 * x ^ 2 - 8 * a ^ 2 * d * r ^ 3 * v * x ^ 2 + 8 *
    a ^ 2 * d * r ^ 3 * v + 6 * a ^ 2 * r ^ 5 * v * x ^ 2 + a ^ 2 * r ^ 4 * v ^ 2 * x ^ 2 -
    a ^ 2 * r ^ 4 * v ^ 2 - 2 * d * r ^ 6 + 2 * r ^ 7 * v)
/-- `∂_r Γ^r_{pp}`, reduced to the common denominator. -/
theorem Rpp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δr Gr_pp) (⟨Rpp_n1, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_pp, Rpp_n1, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2,
        δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `∂_x Γ^x_{pp}` over the common denominator. -/
def Rpp_n2 : ZExp 6 := -4 * (a ^ 2 * x ^ 2 + r ^ 2) * (-3 * a ^ 8 * x ^ 4 + 5 * a ^ 8 * x ^ 2 +
    a ^ 6 * d * x ^ 8 + a ^ 6 * d * x ^ 6 + 3 * a ^ 6 * d * x ^ 4 - 5 * a ^ 6 * d * x ^ 2 - 9 *
    a ^ 6 * r ^ 2 * x ^ 4 + 18 * a ^ 6 * r ^ 2 * x ^ 2 - a ^ 6 * r ^ 2 + 5 * a ^ 4 * d * r ^ 2 *
    x ^ 6 + 7 * a ^ 4 * d * r ^ 2 * x ^ 4 - 13 * a ^ 4 * d * r ^ 2 * x ^ 2 + a ^ 4 * d * r ^ 2 -
    9 * a ^ 4 * r ^ 4 * x ^ 4 + 24 * a ^ 4 * r ^ 4 * x ^ 2 - 3 * a ^ 4 * r ^ 4 + 10 * a ^ 2 * d *
    r ^ 4 * x ^ 4 - 12 * a ^ 2 * d * r ^ 4 * x ^ 2 + 2 * a ^ 2 * d * r ^ 4 - 3 * a ^ 2 * r ^ 6 *
    x ^ 4 + 14 * a ^ 2 * r ^ 6 * x ^ 2 - 3 * a ^ 2 * r ^ 6 + 3 * r ^ 8 * x ^ 2 - r ^ 8)
/-- `∂_x Γ^x_{pp}`, reduced to the common denominator. -/
theorem Rpp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx Gx_pp) (⟨Rpp_n2, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_pp, Rpp_n2, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2,
        δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{pp} Γ^t_{rt}` over the common denominator. -/
def Rpp_n3 : ZExp 6 := -(a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (2 * a ^ 2 * r * x ^ 2 - 2 *
    a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v) * (4 * a ^ 4 * r * x ^ 2 - 2 * a ^ 4 *
    r + a ^ 4 * v * x ^ 4 - a ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d * r * x ^ 2 + 2 * a ^ 2 * d * r +
    4 * a ^ 2 * r ^ 3 * x ^ 2 + a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 * v + 2 * r ^ 5)
/-- `Γ^r_{pp} Γ^t_{rt}`, reduced to the common denominator. -/
theorem Rpp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_pp * Gt_tr) (⟨Rpp_n3, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_pp, Gt_tr, Rpp_n3, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{pp} Γ^r_{rr}` over the common denominator. -/
def Rpp_n4 : ZExp 6 := -(x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 * v * x ^ 2 - 2 *
    d * r + r ^ 2 * v) * (4 * a ^ 4 * r * x ^ 2 - 2 * a ^ 4 * r + a ^ 4 * v * x ^ 4 - a ^ 4 * v *
    x ^ 2 - 2 * a ^ 2 * d * r * x ^ 2 + 2 * a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 * x ^ 2 + a ^ 2 *
    r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 * v + 2 * r ^ 5)
/-- `Γ^r_{pp} Γ^r_{rr}`, reduced to the common denominator. -/
theorem Rpp_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_pp * Gr_rr) (⟨Rpp_n4, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_pp, Gr_rr, Rpp_n4, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{pp} Γ^x_{rx}` over the common denominator. -/
def Rpp_n5 : ZExp 6 := 2 * d * r * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (4 * a ^ 4 * r *
    x ^ 2 - 2 * a ^ 4 * r + a ^ 4 * v * x ^ 4 - a ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d * r * x ^ 2 +
    2 * a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 * x ^ 2 + a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 *
    v + 2 * r ^ 5)
/-- `Γ^r_{pp} Γ^x_{rx}`, reduced to the common denominator. -/
theorem Rpp_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_pp * Gx_rx) (⟨Rpp_n5, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_pp, Gx_rx, Rpp_n5, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{pp} Γ^p_{rp}` over the common denominator. -/
def Rpp_n6 : ZExp 6 := (x - 1) * (x + 1) * (2 * a ^ 4 * r * x ^ 2 - 2 * a ^ 4 * r + a ^ 4 * v *
    x ^ 4 - a ^ 4 * v * x ^ 2 + 2 * a ^ 2 * d * r + 2 * a ^ 2 * r ^ 3 * x ^ 2 - 2 * a ^ 2 *
    r ^ 3 + a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 * v + 2 * d * r ^ 3) * (4 * a ^ 4 * r *
    x ^ 2 - 2 * a ^ 4 * r + a ^ 4 * v * x ^ 4 - a ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d * r * x ^ 2 +
    2 * a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 * x ^ 2 + a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 *
    v + 2 * r ^ 5)
/-- `Γ^r_{pp} Γ^p_{rp}`, reduced to the common denominator. -/
theorem Rpp_t6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_pp * Gp_rp) (⟨Rpp_n6, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rp, Gr_pp, Rpp_n6, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{pp} Γ^t_{xt}` over the common denominator. -/
def Rpp_n7 : ZExp 6 := -4 * a ^ 2 * x ^ 2 * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) * (a ^ 6 +
    a ^ 4 * d * x ^ 4 - a ^ 4 * d + 3 * a ^ 4 * r ^ 2 + 2 * a ^ 2 * d * r ^ 2 * x ^ 2 - 2 *
    a ^ 2 * d * r ^ 2 + 3 * a ^ 2 * r ^ 4 + r ^ 6)
/-- `Γ^x_{pp} Γ^t_{xt}`, reduced to the common denominator. -/
theorem Rpp_t7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_pp * Gt_tx) (⟨Rpp_n7, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tx, Gx_pp, Rpp_n7, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{pp} Γ^r_{xr}` over the common denominator. -/
def Rpp_n8 : ZExp 6 := -4 * a ^ 2 * x ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) *
    (a ^ 6 + a ^ 4 * d * x ^ 4 - a ^ 4 * d + 3 * a ^ 4 * r ^ 2 + 2 * a ^ 2 * d * r ^ 2 * x ^ 2 -
    2 * a ^ 2 * d * r ^ 2 + 3 * a ^ 2 * r ^ 4 + r ^ 6)
/-- `Γ^x_{pp} Γ^r_{xr}`, reduced to the common denominator. -/
theorem Rpp_t8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_pp * Gr_rx) (⟨Rpp_n8, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Gx_pp, Rpp_n8, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{pp} Γ^x_{xx}` over the common denominator. -/
def Rpp_n9 : ZExp 6 := 4 * x ^ 2 * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 6 + a ^ 4 *
    d * x ^ 4 - a ^ 4 * d + 3 * a ^ 4 * r ^ 2 + 2 * a ^ 2 * d * r ^ 2 * x ^ 2 - 2 * a ^ 2 * d *
    r ^ 2 + 3 * a ^ 2 * r ^ 4 + r ^ 6)
/-- `Γ^x_{pp} Γ^x_{xx}`, reduced to the common denominator. -/
theorem Rpp_t9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_pp * Gx_xx) (⟨Rpp_n9, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_pp, Gx_xx, Rpp_n9, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{pp} Γ^p_{xp}` over the common denominator. -/
def Rpp_n10 : ZExp 6 := -4 * x ^ 2 * (a ^ 6 + a ^ 4 * d * x ^ 4 - a ^ 4 * d + 3 * a ^ 4 * r ^ 2 +
    2 * a ^ 2 * d * r ^ 2 * x ^ 2 - 2 * a ^ 2 * d * r ^ 2 + 3 * a ^ 2 * r ^ 4 + r ^ 6) * (a ^ 4 *
    x ^ 4 - a ^ 4 * x ^ 2 + a ^ 4 + a ^ 2 * d * x ^ 2 - a ^ 2 * d + a ^ 2 * r ^ 2 * x ^ 2 +
    a ^ 2 * r ^ 2 + r ^ 4)
/-- `Γ^x_{pp} Γ^p_{xp}`, reduced to the common denominator. -/
theorem Rpp_t10 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_pp * Gp_xp) (⟨Rpp_n10, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_xp, Gx_pp, Rpp_n10, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{pt} Γ^t_{pr}` over the common denominator. -/
def Rpp_n11 : ZExp 6 := -a ^ 2 * (x - 1) ^ 2 * (x + 1) ^ 2 * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 *
    r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v) * (2 * a ^ 4 * r + a ^ 4 * v * x ^ 2 - 2 *
    a ^ 2 * d * r * x ^ 2 - 2 * a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 + a ^ 2 * r ^ 2 * v * x ^ 2 +
    a ^ 2 * r ^ 2 * v - 4 * d * r ^ 3 + 2 * r ^ 5 + r ^ 4 * v)
/-- `Γ^r_{pt} Γ^t_{pr}`, reduced to the common denominator. -/
theorem Rpp_t11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_tp * Gt_rp) (⟨Rpp_n11, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_tp, Gt_rp, Rpp_n11, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{pt} Γ^t_{px}` over the common denominator. -/
def Rpp_n12 : ZExp 6 := 4 * a ^ 4 * x ^ 2 * (a ^ 2 + r ^ 2) * (x - 1) ^ 2 * (x + 1) ^ 2 *
    (a ^ 2 - d + r ^ 2) ^ 2
/-- `Γ^x_{pt} Γ^t_{px}`, reduced to the common denominator. -/
theorem Rpp_t12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_tp * Gt_xp) (⟨Rpp_n12, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_xp, Gx_tp, Rpp_n12, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{pr} Γ^r_{pt}` over the common denominator. -/
def Rpp_n13 : ZExp 6 := -a ^ 2 * (x - 1) ^ 2 * (x + 1) ^ 2 * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 *
    r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v) * (2 * a ^ 4 * r + a ^ 4 * v * x ^ 2 - 2 *
    a ^ 2 * d * r * x ^ 2 - 2 * a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 + a ^ 2 * r ^ 2 * v * x ^ 2 +
    a ^ 2 * r ^ 2 * v - 4 * d * r ^ 3 + 2 * r ^ 5 + r ^ 4 * v)
/-- `Γ^t_{pr} Γ^r_{pt}`, reduced to the common denominator. -/
theorem Rpp_t13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_rp * Gr_tp) (⟨Rpp_n13, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_tp, Gt_rp, Rpp_n13, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^p_{pr} Γ^r_{pp}` over the common denominator. -/
def Rpp_n14 : ZExp 6 := (x - 1) * (x + 1) * (2 * a ^ 4 * r * x ^ 2 - 2 * a ^ 4 * r + a ^ 4 * v *
    x ^ 4 - a ^ 4 * v * x ^ 2 + 2 * a ^ 2 * d * r + 2 * a ^ 2 * r ^ 3 * x ^ 2 - 2 * a ^ 2 *
    r ^ 3 + a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 * v + 2 * d * r ^ 3) * (4 * a ^ 4 * r *
    x ^ 2 - 2 * a ^ 4 * r + a ^ 4 * v * x ^ 4 - a ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d * r * x ^ 2 +
    2 * a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 * x ^ 2 + a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 *
    v + 2 * r ^ 5)
/-- `Γ^p_{pr} Γ^r_{pp}`, reduced to the common denominator. -/
theorem Rpp_t14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gp_rp * Gr_pp) (⟨Rpp_n14, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rp, Gr_pp, Rpp_n14, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{px} Γ^x_{pt}` over the common denominator. -/
def Rpp_n15 : ZExp 6 := 4 * a ^ 4 * x ^ 2 * (a ^ 2 + r ^ 2) * (x - 1) ^ 2 * (x + 1) ^ 2 *
    (a ^ 2 - d + r ^ 2) ^ 2
/-- `Γ^t_{px} Γ^x_{pt}`, reduced to the common denominator. -/
theorem Rpp_t15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_xp * Gx_tp) (⟨Rpp_n15, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_xp, Gx_tp, Rpp_n15, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^p_{px} Γ^x_{pp}` over the common denominator. -/
def Rpp_n16 : ZExp 6 := -4 * x ^ 2 * (a ^ 6 + a ^ 4 * d * x ^ 4 - a ^ 4 * d + 3 * a ^ 4 * r ^ 2 +
    2 * a ^ 2 * d * r ^ 2 * x ^ 2 - 2 * a ^ 2 * d * r ^ 2 + 3 * a ^ 2 * r ^ 4 + r ^ 6) * (a ^ 4 *
    x ^ 4 - a ^ 4 * x ^ 2 + a ^ 4 + a ^ 2 * d * x ^ 2 - a ^ 2 * d + a ^ 2 * r ^ 2 * x ^ 2 +
    a ^ 2 * r ^ 2 + r ^ 4)
/-- `Γ^p_{px} Γ^x_{pp}`, reduced to the common denominator. -/
theorem Rpp_t16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gp_xp * Gx_pp) (⟨Rpp_n16, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_xp, Gx_pp, Rpp_n16, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{pp} Γ^p_{pr}` over the common denominator. -/
def Rpp_n17 : ZExp 6 := (x - 1) * (x + 1) * (2 * a ^ 4 * r * x ^ 2 - 2 * a ^ 4 * r + a ^ 4 * v *
    x ^ 4 - a ^ 4 * v * x ^ 2 + 2 * a ^ 2 * d * r + 2 * a ^ 2 * r ^ 3 * x ^ 2 - 2 * a ^ 2 *
    r ^ 3 + a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 * v + 2 * d * r ^ 3) * (4 * a ^ 4 * r *
    x ^ 2 - 2 * a ^ 4 * r + a ^ 4 * v * x ^ 4 - a ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d * r * x ^ 2 +
    2 * a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 * x ^ 2 + a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 *
    v + 2 * r ^ 5)
/-- `Γ^r_{pp} Γ^p_{pr}`, reduced to the common denominator. -/
theorem Rpp_t17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_pp * Gp_rp) (⟨Rpp_n17, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rp, Gr_pp, Rpp_n17, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{pp} Γ^p_{px}` over the common denominator. -/
def Rpp_n18 : ZExp 6 := -4 * x ^ 2 * (a ^ 6 + a ^ 4 * d * x ^ 4 - a ^ 4 * d + 3 * a ^ 4 * r ^ 2 +
    2 * a ^ 2 * d * r ^ 2 * x ^ 2 - 2 * a ^ 2 * d * r ^ 2 + 3 * a ^ 2 * r ^ 4 + r ^ 6) * (a ^ 4 *
    x ^ 4 - a ^ 4 * x ^ 2 + a ^ 4 + a ^ 2 * d * x ^ 2 - a ^ 2 * d + a ^ 2 * r ^ 2 * x ^ 2 +
    a ^ 2 * r ^ 2 + r ^ 4)
/-- `Γ^x_{pp} Γ^p_{px}`, reduced to the common denominator. -/
theorem Rpp_t18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_pp * Gp_xp) (⟨Rpp_n18, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_xp, Gx_pp, Rpp_n18, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R_{pp}` (`eq:offshell`): the signed sum of its terms is `Uf * ⟨d * a ^ 2 * sx ^ 2, Sg⟩ +
        Vf * ⟨sx * Pp ^ 2, Sg⟩`. -/
theorem ricci_pp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Rpp_n1 + Rpp_n2 + Rpp_n3 + Rpp_n4 + Rpp_n5 + Rpp_n6 + Rpp_n7 + Rpp_n8 +
        Rpp_n9 + Rpp_n10 - Rpp_n11 - Rpp_n12 - Rpp_n13 - Rpp_n14 - Rpp_n15 - Rpp_n16 - Rpp_n17 -
        Rpp_n18, Rpp_cd⟩) (Uf * ⟨d * a ^ 2 * sx ^ 2, Sg⟩ + Vf * ⟨sx * Pp ^ 2, Sg⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Rpp_n1, Rpp_n2, Rpp_n3, Rpp_n4, Rpp_n5, Rpp_n6, Rpp_n7, Rpp_n8, Rpp_n9,
        Rpp_n10, Rpp_n11, Rpp_n12, Rpp_n13, Rpp_n14, Rpp_n15, Rpp_n16, Rpp_n17, Rpp_n18, Rpp_cd,
        Uf, Vf, Nn, Sg, sx, Pp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4,
        δx_5]
    ring)


/-! ## The Kerr–Newman specialization (`thm:KN`) -/

section KN

local notation "R" => (ZExp.var 0 : ZExp 8)
local notation "A" => (ZExp.var 2 : ZExp 8)
local notation "D" => (ZExp.var 3 : ZExp 8)
local notation "V" => (ZExp.var 4 : ZExp 8)
local notation "W" => (ZExp.var 5 : ZExp 8)
local notation "M" => (ZExp.var 6 : ZExp 8)
local notation "Q" => (ZExp.var 7 : ZExp 8)

/-- The Kerr–Newman radial function and its derivatives: `d = Δ = r² − 2mr + a² + q²`,
`v = 2r − 2m`, `w = 2`. -/
abbrev knHyps : List (ZExp 8 × ZExp 8) :=
  [(D, R ^ 2 - 2 * M * R + A ^ 2 + Q ^ 2), (V, 2 * R - 2 * M), (W, 2)]

/-- `thm:KN`: `N = r² − a² + Δ − r(2r − 2m) = q²`, so `V = q²/Σ²`. -/
theorem kn_N :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp knHyps (R ^ 2 - A ^ 2 + D - R * V, Q ^ 2)) :=
  derive_imp _ _ (by
    ipra_poly S ρ h
    obtain ⟨h₁, h₂, _⟩ := h
    linear_combination h₁ - ρ 0 * h₂)

/-- `thm:KN`: `w − 2 = 0`, so `U = V`. -/
theorem kn_w :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8) (imp knHyps (W - 2, 0)) :=
  derive_imp _ _ (by
    ipra_poly S ρ h
    obtain ⟨_, _, h₃⟩ := h
    linear_combination h₃)

end KN

end LeanProofs.IPRA.Geometry.KerrNewmanRicci
