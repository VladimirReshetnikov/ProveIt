import IPRADerivations.Geometry.KerrNewmanBase

/-!
# The connection of the radial-function metric (`four_metrics_ipra`)

Packet: `geometry/four_metrics_ipra_2026-11-15`, `lem:offshell` ("Radial-function Ricci
identity"), first half: the connection coefficients of the master metric `eq:master` with the
radial function left unspecified ("Write `d = Δ(r)`, `v = Δ′(r)`, and `w = Δ″(r)`. Algebraically,
these are three independent indeterminates").

In the coordinates `(t, r, x, φ)` (the index `p` stands for `φ`), with `Σ = r² + a² x²`,
`s = 1 − x²`, `P = r² + a²`, the metric `eq:master` with `Δ` replaced by `d` is

`g_tt = (−d + a² s)/Σ`, `g_tφ = −a s (P − d)/Σ`, `g_φφ = s (P² − a² d s)/Σ`,
`g_rr = Σ/d`, `g_xx = Σ/s`,

and its inverse `eq:ginv` is

`g^tt = −(P² − a² d s)/(dΣ)`, `g^tφ = −a (P − d)/(dΣ)`, `g^φφ = (d − a² s)/(d s Σ)`,
`g^rr = d/Σ`, `g^xx = s/Σ`

(`inverse_tt`, `inverse_tp`, `inverse_pt`, `inverse_pp`, `inverse_rr`, `inverse_xx`). The
coefficients do not depend on `t` and `φ`, so `∂_t = ∂_φ = 0` and only the formal derivations
`∂_r`, `∂_x` of `Geometry/KerrNewmanBase` occur.

**The connection** (`eq:gamma`):
`Γ^λ_{μν} = ½ Σ_ρ g^{λρ} (∂_μ g_{ρν} + ∂_ν g_{ρμ} − ∂_ρ g_{μν})`. For each of the twenty nonzero
coefficients `Γ^λ_{μν}` (`μ ≤ ν` in the order `t, r, x, φ`):

* `Gλ_μν` is its reduced fraction and `Gλ_μν_cd` a common denominator of its terms;
* `Gλ_μν_tk`: the `k`-th nonvanishing term `½ g^{λρ} ∂_σ g_{αβ}`, with the derivative taken by
  `Foundations/FormalDerivation`, equals the numerator `Gλ_μν_nk` over the common denominator;
* `christoffel_λ_μν`: the signed sum of these numerators over the common denominator is the
  reduced fraction (the sign of each term is its sign in `eq:gamma`).

The other twenty coefficients have no nonvanishing term. The reduced fractions and the
numerators were proposed by a computer algebra script (in expanded or factored form, in the
variables `r, x, a, d, v`); every identity is checked by Lean as an identity of fractions
cleared of denominators, a closed sentence of iPRA certified in every commutative ring.
-/

namespace LeanProofs.IPRA.Geometry.KerrNewmanConnection

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Geometry.KerrNewmanBase (δr δx δr_0 δr_1 δr_2 δr_3 δr_4 δr_5 δx_0 δx_1 δx_2
  δx_3 δx_4 δx_5 Sg sx)
open ZExp

local notation "r" => (ZExp.var 0 : ZExp 6)
local notation "x" => (ZExp.var 1 : ZExp 6)
local notation "a" => (ZExp.var 2 : ZExp 6)
local notation "d" => (ZExp.var 3 : ZExp 6)
local notation "v" => (ZExp.var 4 : ZExp 6)
local notation "w" => (ZExp.var 5 : ZExp 6)

/-- `P = r² + a²`. -/
def Pp : ZExp 6 := r ^ 2 + a ^ 2

/-! ## The metric `eq:master` with `Δ` replaced by `d`, and `eq:ginv` -/

/-- `g_tt = (−d + a² s)/Σ`. -/
def gtt : Frac 6 := ⟨-d + a ^ 2 * sx, Sg⟩
/-- `g_tφ = −a s (P − d)/Σ`. -/
def gtp : Frac 6 := ⟨-(a * sx * (Pp - d)), Sg⟩
/-- `g_φφ = s (P² − a² d s)/Σ`. -/
def gpp : Frac 6 := ⟨sx * (Pp ^ 2 - a ^ 2 * d * sx), Sg⟩
/-- `g_rr = Σ/d`. -/
def grr : Frac 6 := ⟨Sg, d⟩
/-- `g_xx = Σ/s`. -/
def gxx : Frac 6 := ⟨Sg, sx⟩
/-- `g^tt = −(P² − a² d s)/(dΣ)`. -/
def itt : Frac 6 := ⟨-(Pp ^ 2 - a ^ 2 * d * sx), d * Sg⟩
/-- `g^tφ = −a (P − d)/(dΣ)`. -/
def itp : Frac 6 := ⟨-(a * (Pp - d)), d * Sg⟩
/-- `g^φφ = (d − a² s)/(d s Σ)`. -/
def ipp : Frac 6 := ⟨d - a ^ 2 * sx, d * sx * Sg⟩
/-- `g^rr = d/Σ`. -/
def irr : Frac 6 := ⟨d, Sg⟩
/-- `g^xx = s/Σ`. -/
def ixx : Frac 6 := ⟨sx, Sg⟩

/-! ## The inverse -/

/-- `(g g⁻¹)_t^t = 1`. -/
theorem inverse_tt :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (gtt * itt + gtp * itp) (Frac.ofZ 1))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, δr_0, δr_1,
        δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `(g g⁻¹)_t^p = 0`. -/
theorem inverse_tp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (gtt * itp + gtp * ipp) (Frac.ofZ 0))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, δr_0, δr_1,
        δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `(g g⁻¹)_p^t = 0`. -/
theorem inverse_pt :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (gtp * itt + gpp * itp) (Frac.ofZ 0))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, δr_0, δr_1,
        δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `(g g⁻¹)_p^p = 1`. -/
theorem inverse_pp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (gtp * itp + gpp * ipp) (Frac.ofZ 1))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, δr_0, δr_1,
        δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `(g g⁻¹)_r^r = 1`. -/
theorem inverse_rr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (grr * irr) (Frac.ofZ 1))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, δr_0, δr_1,
        δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `(g g⁻¹)_x^x = 1`. -/
theorem inverse_xx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (gxx * ixx) (Frac.ofZ 1))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, δr_0, δr_1,
        δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ## The connection coefficients `eq:gamma` -/

/-! ### `Γ^t_{tr}` -/

/-- The common denominator of the terms of `Γ^t_{tr}`. -/
def Gt_tr_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3
/-- `Γ^t_{tr}`, reduced. -/
def Gt_tr : Frac 6 := ⟨-(a ^ 2 + r ^ 2) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v *
    x ^ 2 + 2 * d * r - r ^ 2 * v), 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2⟩

/-- The numerator of `½ g^{tt} ∂_r g_{tt}` over the common denominator. -/
def Gt_tr_n1 : ZExp 6 := -(a ^ 4 + a ^ 2 * d * x ^ 2 - a ^ 2 * d + 2 * a ^ 2 * r ^ 2 + r ^ 4) *
    (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `½ g^{tt} ∂_r g_{tt}`, reduced to the common denominator. -/
theorem Gt_tr_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.half (itt * Frac.d δr gtt)) (⟨Gt_tr_n1, Gt_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Gt_tr_n1,
        Gt_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `½ g^{tp} ∂_r g_{pt}` over the common denominator. -/
def Gt_tr_n2 : ZExp 6 := -a ^ 2 * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) * (2 * a ^ 2 * r *
    x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `½ g^{tp} ∂_r g_{pt}`, reduced to the common denominator. -/
theorem Gt_tr_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.half (itp * Frac.d δr gtp)) (⟨Gt_tr_n2, Gt_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Gt_tr_n2,
        Gt_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `Γ^t_{tr}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_t_tr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Gt_tr_n1 + Gt_tr_n2, Gt_tr_cd⟩) (Gt_tr))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tr_n1, Gt_tr_n2, Gt_tr_cd, Gt_tr, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `Γ^t_{tx}` -/

/-- The common denominator of the terms of `Γ^t_{tx}`. -/
def Gt_tx_cd : ZExp 6 := d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3
/-- `Γ^t_{tx}`, reduced. -/
def Gt_tx : Frac 6 := ⟨a ^ 2 * x * (a ^ 2 - d + r ^ 2), (a ^ 2 * x ^ 2 + r ^ 2) ^ 2⟩

/-- The numerator of `½ g^{tt} ∂_x g_{tt}` over the common denominator. -/
def Gt_tx_n1 : ZExp 6 := a ^ 2 * x * (a ^ 2 - d + r ^ 2) * (a ^ 4 + a ^ 2 * d * x ^ 2 - a ^ 2 *
    d + 2 * a ^ 2 * r ^ 2 + r ^ 4)
/-- `½ g^{tt} ∂_x g_{tt}`, reduced to the common denominator. -/
theorem Gt_tx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.half (itt * Frac.d δx gtt)) (⟨Gt_tx_n1, Gt_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Gt_tx_n1,
        Gt_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `½ g^{tp} ∂_x g_{pt}` over the common denominator. -/
def Gt_tx_n2 : ZExp 6 := -a ^ 2 * x * (a ^ 2 + r ^ 2) * (a ^ 2 - d + r ^ 2) ^ 2
/-- `½ g^{tp} ∂_x g_{pt}`, reduced to the common denominator. -/
theorem Gt_tx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.half (itp * Frac.d δx gtp)) (⟨Gt_tx_n2, Gt_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Gt_tx_n2,
        Gt_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `Γ^t_{tx}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_t_tx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Gt_tx_n1 + Gt_tx_n2, Gt_tx_cd⟩) (Gt_tx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tx_n1, Gt_tx_n2, Gt_tx_cd, Gt_tx, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `Γ^t_{rp}` -/

/-- The common denominator of the terms of `Γ^t_{rp}`. -/
def Gt_rp_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3
/-- `Γ^t_{rp}`, reduced. -/
def Gt_rp : Frac 6 := ⟨a * (x - 1) * (x + 1) * (2 * a ^ 4 * r + a ^ 4 * v * x ^ 2 - 2 * a ^ 2 *
    d * r * x ^ 2 - 2 * a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 + a ^ 2 * r ^ 2 * v * x ^ 2 + a ^ 2 *
    r ^ 2 * v - 4 * d * r ^ 3 + 2 * r ^ 5 + r ^ 4 * v), 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2⟩

/-- The numerator of `½ g^{tt} ∂_r g_{tp}` over the common denominator. -/
def Gt_rp_n1 : ZExp 6 := -a * (x - 1) * (x + 1) * (a ^ 4 + a ^ 2 * d * x ^ 2 - a ^ 2 * d + 2 *
    a ^ 2 * r ^ 2 + r ^ 4) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d *
    r - r ^ 2 * v)
/-- `½ g^{tt} ∂_r g_{tp}`, reduced to the common denominator. -/
theorem Gt_rp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.half (itt * Frac.d δr gtp)) (⟨Gt_rp_n1, Gt_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Gt_rp_n1,
        Gt_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `½ g^{tp} ∂_r g_{pp}` over the common denominator. -/
def Gt_rp_n2 : ZExp 6 := a * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) * (4 * a ^ 4 * r * x ^ 2 -
    2 * a ^ 4 * r + a ^ 4 * v * x ^ 4 - a ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d * r * x ^ 2 + 2 *
    a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 * x ^ 2 + a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 * v +
    2 * r ^ 5)
/-- `½ g^{tp} ∂_r g_{pp}`, reduced to the common denominator. -/
theorem Gt_rp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.half (itp * Frac.d δr gpp)) (⟨Gt_rp_n2, Gt_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Gt_rp_n2,
        Gt_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `Γ^t_{rp}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_t_rp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Gt_rp_n1 + Gt_rp_n2, Gt_rp_cd⟩) (Gt_rp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_rp_n1, Gt_rp_n2, Gt_rp_cd, Gt_rp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `Γ^t_{xp}` -/

/-- The common denominator of the terms of `Γ^t_{xp}`. -/
def Gt_xp_cd : ZExp 6 := d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3
/-- `Γ^t_{xp}`, reduced. -/
def Gt_xp : Frac 6 := ⟨a ^ 3 * x * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2), (a ^ 2 * x ^ 2 +
    r ^ 2) ^ 2⟩

/-- The numerator of `½ g^{tt} ∂_x g_{tp}` over the common denominator. -/
def Gt_xp_n1 : ZExp 6 := -a * x * (a ^ 2 + r ^ 2) * (a ^ 2 - d + r ^ 2) * (a ^ 4 + a ^ 2 * d *
    x ^ 2 - a ^ 2 * d + 2 * a ^ 2 * r ^ 2 + r ^ 4)
/-- `½ g^{tt} ∂_x g_{tp}`, reduced to the common denominator. -/
theorem Gt_xp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.half (itt * Frac.d δx gtp)) (⟨Gt_xp_n1, Gt_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Gt_xp_n1,
        Gt_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `½ g^{tp} ∂_x g_{pp}` over the common denominator. -/
def Gt_xp_n2 : ZExp 6 := a * x * (a ^ 2 - d + r ^ 2) * (a ^ 6 + a ^ 4 * d * x ^ 4 - a ^ 4 * d +
    3 * a ^ 4 * r ^ 2 + 2 * a ^ 2 * d * r ^ 2 * x ^ 2 - 2 * a ^ 2 * d * r ^ 2 + 3 * a ^ 2 *
    r ^ 4 + r ^ 6)
/-- `½ g^{tp} ∂_x g_{pp}`, reduced to the common denominator. -/
theorem Gt_xp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.half (itp * Frac.d δx gpp)) (⟨Gt_xp_n2, Gt_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Gt_xp_n2,
        Gt_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `Γ^t_{xp}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_t_xp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Gt_xp_n1 + Gt_xp_n2, Gt_xp_cd⟩) (Gt_xp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_xp_n1, Gt_xp_n2, Gt_xp_cd, Gt_xp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `Γ^r_{tt}` -/

/-- The common denominator of the terms of `Γ^r_{tt}`. -/
def Gr_tt_cd : ZExp 6 := 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3
/-- `Γ^r_{tt}`, reduced. -/
def Gr_tt : Frac 6 := ⟨-d * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d *
    r - r ^ 2 * v), 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- The numerator of `½ g^{rr} ∂_r g_{tt}` over the common denominator. -/
def Gr_tt_n1 : ZExp 6 := d * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d *
    r - r ^ 2 * v)
/-- `½ g^{rr} ∂_r g_{tt}`, reduced to the common denominator. -/
theorem Gr_tt_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.half (irr * Frac.d δr gtt)) (⟨Gr_tt_n1, Gr_tt_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Gr_tt_n1,
        Gr_tt_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `Γ^r_{tt}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_r_tt :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨0 - Gr_tt_n1, Gr_tt_cd⟩) (Gr_tt))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_tt_n1, Gr_tt_cd, Gr_tt, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1,
        δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `Γ^r_{tp}` -/

/-- The common denominator of the terms of `Γ^r_{tp}`. -/
def Gr_tp_cd : ZExp 6 := 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3
/-- `Γ^r_{tp}`, reduced. -/
def Gr_tp : Frac 6 := ⟨-a * d * (x - 1) * (x + 1) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r -
    a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v), 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- The numerator of `½ g^{rr} ∂_r g_{tp}` over the common denominator. -/
def Gr_tp_n1 : ZExp 6 := a * d * (x - 1) * (x + 1) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r -
    a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `½ g^{rr} ∂_r g_{tp}`, reduced to the common denominator. -/
theorem Gr_tp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.half (irr * Frac.d δr gtp)) (⟨Gr_tp_n1, Gr_tp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Gr_tp_n1,
        Gr_tp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `Γ^r_{tp}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_r_tp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨0 - Gr_tp_n1, Gr_tp_cd⟩) (Gr_tp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_tp_n1, Gr_tp_cd, Gr_tp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1,
        δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `Γ^r_{rr}` -/

/-- The common denominator of the terms of `Γ^r_{rr}`. -/
def Gr_rr_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2)
/-- `Γ^r_{rr}`, reduced. -/
def Gr_rr : Frac 6 := ⟨-a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v, 2 * d * (a ^ 2 * x ^ 2 + r ^ 2)⟩

/-- The numerator of `½ g^{rr} ∂_r g_{rr}` over the common denominator. -/
def Gr_rr_n1 : ZExp 6 := -a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v
/-- `½ g^{rr} ∂_r g_{rr}`, reduced to the common denominator. -/
theorem Gr_rr_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.half (irr * Frac.d δr grr)) (⟨Gr_rr_n1, Gr_rr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Gr_rr_n1,
        Gr_rr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `½ g^{rr} ∂_r g_{rr}` over the common denominator. -/
def Gr_rr_n2 : ZExp 6 := -a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v
/-- `½ g^{rr} ∂_r g_{rr}`, reduced to the common denominator. -/
theorem Gr_rr_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.half (irr * Frac.d δr grr)) (⟨Gr_rr_n2, Gr_rr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Gr_rr_n2,
        Gr_rr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `½ g^{rr} ∂_r g_{rr}` over the common denominator. -/
def Gr_rr_n3 : ZExp 6 := -a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v
/-- `½ g^{rr} ∂_r g_{rr}`, reduced to the common denominator. -/
theorem Gr_rr_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.half (irr * Frac.d δr grr)) (⟨Gr_rr_n3, Gr_rr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Gr_rr_n3,
        Gr_rr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `Γ^r_{rr}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_r_rr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Gr_rr_n1 + Gr_rr_n2 - Gr_rr_n3, Gr_rr_cd⟩) (Gr_rr))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rr_n1, Gr_rr_n2, Gr_rr_n3, Gr_rr_cd, Gr_rr, δr_0, δr_1, δr_2, δr_3, δr_4,
        δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `Γ^r_{rx}` -/

/-- The common denominator of the terms of `Γ^r_{rx}`. -/
def Gr_rx_cd : ZExp 6 := a ^ 2 * x ^ 2 + r ^ 2
/-- `Γ^r_{rx}`, reduced. -/
def Gr_rx : Frac 6 := ⟨a ^ 2 * x, a ^ 2 * x ^ 2 + r ^ 2⟩

/-- The numerator of `½ g^{rr} ∂_x g_{rr}` over the common denominator. -/
def Gr_rx_n1 : ZExp 6 := a ^ 2 * x
/-- `½ g^{rr} ∂_x g_{rr}`, reduced to the common denominator. -/
theorem Gr_rx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.half (irr * Frac.d δx grr)) (⟨Gr_rx_n1, Gr_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Gr_rx_n1,
        Gr_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `Γ^r_{rx}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_r_rx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Gr_rx_n1, Gr_rx_cd⟩) (Gr_rx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx_n1, Gr_rx_cd, Gr_rx, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1,
        δx_2, δx_3, δx_4, δx_5])

/-! ### `Γ^r_{xx}` -/

/-- The common denominator of the terms of `Γ^r_{xx}`. -/
def Gr_xx_cd : ZExp 6 := (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2)
/-- `Γ^r_{xx}`, reduced. -/
def Gr_xx : Frac 6 := ⟨d * r, (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2)⟩

/-- The numerator of `½ g^{rr} ∂_r g_{xx}` over the common denominator. -/
def Gr_xx_n1 : ZExp 6 := -d * r
/-- `½ g^{rr} ∂_r g_{xx}`, reduced to the common denominator. -/
theorem Gr_xx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.half (irr * Frac.d δr gxx)) (⟨Gr_xx_n1, Gr_xx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Gr_xx_n1,
        Gr_xx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `Γ^r_{xx}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_r_xx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨0 - Gr_xx_n1, Gr_xx_cd⟩) (Gr_xx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_xx_n1, Gr_xx_cd, Gr_xx, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1,
        δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `Γ^r_{pp}` -/

/-- The common denominator of the terms of `Γ^r_{pp}`. -/
def Gr_pp_cd : ZExp 6 := 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3
/-- `Γ^r_{pp}`, reduced. -/
def Gr_pp : Frac 6 := ⟨d * (x - 1) * (x + 1) * (4 * a ^ 4 * r * x ^ 2 - 2 * a ^ 4 * r + a ^ 4 *
    v * x ^ 4 - a ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d * r * x ^ 2 + 2 * a ^ 2 * d * r + 4 * a ^ 2 *
    r ^ 3 * x ^ 2 + a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 * v + 2 * r ^ 5), 2 * (a ^ 2 *
    x ^ 2 + r ^ 2) ^ 3⟩

/-- The numerator of `½ g^{rr} ∂_r g_{pp}` over the common denominator. -/
def Gr_pp_n1 : ZExp 6 := -d * (x - 1) * (x + 1) * (4 * a ^ 4 * r * x ^ 2 - 2 * a ^ 4 * r +
    a ^ 4 * v * x ^ 4 - a ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d * r * x ^ 2 + 2 * a ^ 2 * d * r + 4 *
    a ^ 2 * r ^ 3 * x ^ 2 + a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 * v + 2 * r ^ 5)
/-- `½ g^{rr} ∂_r g_{pp}`, reduced to the common denominator. -/
theorem Gr_pp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.half (irr * Frac.d δr gpp)) (⟨Gr_pp_n1, Gr_pp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Gr_pp_n1,
        Gr_pp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `Γ^r_{pp}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_r_pp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨0 - Gr_pp_n1, Gr_pp_cd⟩) (Gr_pp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_pp_n1, Gr_pp_cd, Gr_pp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1,
        δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `Γ^x_{tt}` -/

/-- The common denominator of the terms of `Γ^x_{tt}`. -/
def Gx_tt_cd : ZExp 6 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 3
/-- `Γ^x_{tt}`, reduced. -/
def Gx_tt : Frac 6 := ⟨-a ^ 2 * x * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2), (a ^ 2 * x ^ 2 +
    r ^ 2) ^ 3⟩

/-- The numerator of `½ g^{xx} ∂_x g_{tt}` over the common denominator. -/
def Gx_tt_n1 : ZExp 6 := a ^ 2 * x * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2)
/-- `½ g^{xx} ∂_x g_{tt}`, reduced to the common denominator. -/
theorem Gx_tt_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.half (ixx * Frac.d δx gtt)) (⟨Gx_tt_n1, Gx_tt_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Gx_tt_n1,
        Gx_tt_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `Γ^x_{tt}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_x_tt :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨0 - Gx_tt_n1, Gx_tt_cd⟩) (Gx_tt))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_tt_n1, Gx_tt_cd, Gx_tt, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1,
        δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `Γ^x_{tp}` -/

/-- The common denominator of the terms of `Γ^x_{tp}`. -/
def Gx_tp_cd : ZExp 6 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 3
/-- `Γ^x_{tp}`, reduced. -/
def Gx_tp : Frac 6 := ⟨a * x * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2),
    (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- The numerator of `½ g^{xx} ∂_x g_{tp}` over the common denominator. -/
def Gx_tp_n1 : ZExp 6 := -a * x * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2)
/-- `½ g^{xx} ∂_x g_{tp}`, reduced to the common denominator. -/
theorem Gx_tp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.half (ixx * Frac.d δx gtp)) (⟨Gx_tp_n1, Gx_tp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Gx_tp_n1,
        Gx_tp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `Γ^x_{tp}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_x_tp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨0 - Gx_tp_n1, Gx_tp_cd⟩) (Gx_tp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_tp_n1, Gx_tp_cd, Gx_tp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1,
        δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `Γ^x_{rr}` -/

/-- The common denominator of the terms of `Γ^x_{rr}`. -/
def Gx_rr_cd : ZExp 6 := d * (a ^ 2 * x ^ 2 + r ^ 2)
/-- `Γ^x_{rr}`, reduced. -/
def Gx_rr : Frac 6 := ⟨a ^ 2 * x * (x - 1) * (x + 1), d * (a ^ 2 * x ^ 2 + r ^ 2)⟩

/-- The numerator of `½ g^{xx} ∂_x g_{rr}` over the common denominator. -/
def Gx_rr_n1 : ZExp 6 := -a ^ 2 * x * (x - 1) * (x + 1)
/-- `½ g^{xx} ∂_x g_{rr}`, reduced to the common denominator. -/
theorem Gx_rr_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.half (ixx * Frac.d δx grr)) (⟨Gx_rr_n1, Gx_rr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Gx_rr_n1,
        Gx_rr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `Γ^x_{rr}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_x_rr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨0 - Gx_rr_n1, Gx_rr_cd⟩) (Gx_rr))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rr_n1, Gx_rr_cd, Gx_rr, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1,
        δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `Γ^x_{rx}` -/

/-- The common denominator of the terms of `Γ^x_{rx}`. -/
def Gx_rx_cd : ZExp 6 := a ^ 2 * x ^ 2 + r ^ 2
/-- `Γ^x_{rx}`, reduced. -/
def Gx_rx : Frac 6 := ⟨r, a ^ 2 * x ^ 2 + r ^ 2⟩

/-- The numerator of `½ g^{xx} ∂_r g_{xx}` over the common denominator. -/
def Gx_rx_n1 : ZExp 6 := r
/-- `½ g^{xx} ∂_r g_{xx}`, reduced to the common denominator. -/
theorem Gx_rx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.half (ixx * Frac.d δr gxx)) (⟨Gx_rx_n1, Gx_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Gx_rx_n1,
        Gx_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `Γ^x_{rx}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_x_rx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Gx_rx_n1, Gx_rx_cd⟩) (Gx_rx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rx_n1, Gx_rx_cd, Gx_rx, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1,
        δx_2, δx_3, δx_4, δx_5])

/-! ### `Γ^x_{xx}` -/

/-- The common denominator of the terms of `Γ^x_{xx}`. -/
def Gx_xx_cd : ZExp 6 := (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2)
/-- `Γ^x_{xx}`, reduced. -/
def Gx_xx : Frac 6 := ⟨-x * (a ^ 2 + r ^ 2), (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2)⟩

/-- The numerator of `½ g^{xx} ∂_x g_{xx}` over the common denominator. -/
def Gx_xx_n1 : ZExp 6 := -x * (a ^ 2 + r ^ 2)
/-- `½ g^{xx} ∂_x g_{xx}`, reduced to the common denominator. -/
theorem Gx_xx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.half (ixx * Frac.d δx gxx)) (⟨Gx_xx_n1, Gx_xx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Gx_xx_n1,
        Gx_xx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `½ g^{xx} ∂_x g_{xx}` over the common denominator. -/
def Gx_xx_n2 : ZExp 6 := -x * (a ^ 2 + r ^ 2)
/-- `½ g^{xx} ∂_x g_{xx}`, reduced to the common denominator. -/
theorem Gx_xx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.half (ixx * Frac.d δx gxx)) (⟨Gx_xx_n2, Gx_xx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Gx_xx_n2,
        Gx_xx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `½ g^{xx} ∂_x g_{xx}` over the common denominator. -/
def Gx_xx_n3 : ZExp 6 := -x * (a ^ 2 + r ^ 2)
/-- `½ g^{xx} ∂_x g_{xx}`, reduced to the common denominator. -/
theorem Gx_xx_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.half (ixx * Frac.d δx gxx)) (⟨Gx_xx_n3, Gx_xx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Gx_xx_n3,
        Gx_xx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `Γ^x_{xx}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_x_xx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Gx_xx_n1 + Gx_xx_n2 - Gx_xx_n3, Gx_xx_cd⟩) (Gx_xx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_xx_n1, Gx_xx_n2, Gx_xx_n3, Gx_xx_cd, Gx_xx, δr_0, δr_1, δr_2, δr_3, δr_4,
        δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `Γ^x_{pp}` -/

/-- The common denominator of the terms of `Γ^x_{pp}`. -/
def Gx_pp_cd : ZExp 6 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 3
/-- `Γ^x_{pp}`, reduced. -/
def Gx_pp : Frac 6 := ⟨-x * (x - 1) * (x + 1) * (a ^ 6 + a ^ 4 * d * x ^ 4 - a ^ 4 * d + 3 *
    a ^ 4 * r ^ 2 + 2 * a ^ 2 * d * r ^ 2 * x ^ 2 - 2 * a ^ 2 * d * r ^ 2 + 3 * a ^ 2 * r ^ 4 +
    r ^ 6), (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- The numerator of `½ g^{xx} ∂_x g_{pp}` over the common denominator. -/
def Gx_pp_n1 : ZExp 6 := x * (x - 1) * (x + 1) * (a ^ 6 + a ^ 4 * d * x ^ 4 - a ^ 4 * d + 3 *
    a ^ 4 * r ^ 2 + 2 * a ^ 2 * d * r ^ 2 * x ^ 2 - 2 * a ^ 2 * d * r ^ 2 + 3 * a ^ 2 * r ^ 4 +
    r ^ 6)
/-- `½ g^{xx} ∂_x g_{pp}`, reduced to the common denominator. -/
theorem Gx_pp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.half (ixx * Frac.d δx gpp)) (⟨Gx_pp_n1, Gx_pp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Gx_pp_n1,
        Gx_pp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `Γ^x_{pp}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_x_pp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨0 - Gx_pp_n1, Gx_pp_cd⟩) (Gx_pp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_pp_n1, Gx_pp_cd, Gx_pp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1,
        δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `Γ^p_{tr}` -/

/-- The common denominator of the terms of `Γ^p_{tr}`. -/
def Gp_tr_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3
/-- `Γ^p_{tr}`, reduced. -/
def Gp_tr : Frac 6 := ⟨-a * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d *
    r - r ^ 2 * v), 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2⟩

/-- The numerator of `½ g^{pt} ∂_r g_{tt}` over the common denominator. -/
def Gp_tr_n1 : ZExp 6 := -a * (a ^ 2 - d + r ^ 2) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r -
    a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `½ g^{pt} ∂_r g_{tt}`, reduced to the common denominator. -/
theorem Gp_tr_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.half (itp * Frac.d δr gtt)) (⟨Gp_tr_n1, Gp_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Gp_tr_n1,
        Gp_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `½ g^{pp} ∂_r g_{pt}` over the common denominator. -/
def Gp_tr_n2 : ZExp 6 := -a * (a ^ 2 * x ^ 2 - a ^ 2 + d) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 *
    r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `½ g^{pp} ∂_r g_{pt}`, reduced to the common denominator. -/
theorem Gp_tr_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.half (ipp * Frac.d δr gtp)) (⟨Gp_tr_n2, Gp_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Gp_tr_n2,
        Gp_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `Γ^p_{tr}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_p_tr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Gp_tr_n1 + Gp_tr_n2, Gp_tr_cd⟩) (Gp_tr))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_tr_n1, Gp_tr_n2, Gp_tr_cd, Gp_tr, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `Γ^p_{tx}` -/

/-- The common denominator of the terms of `Γ^p_{tx}`. -/
def Gp_tx_cd : ZExp 6 := d * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3
/-- `Γ^p_{tx}`, reduced. -/
def Gp_tx : Frac 6 := ⟨-a * x * (a ^ 2 - d + r ^ 2), (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 +
    r ^ 2) ^ 2⟩

/-- The numerator of `½ g^{pt} ∂_x g_{tt}` over the common denominator. -/
def Gp_tx_n1 : ZExp 6 := a ^ 3 * x * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) ^ 2
/-- `½ g^{pt} ∂_x g_{tt}`, reduced to the common denominator. -/
theorem Gp_tx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.half (itp * Frac.d δx gtt)) (⟨Gp_tx_n1, Gp_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Gp_tx_n1,
        Gp_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `½ g^{pp} ∂_x g_{pt}` over the common denominator. -/
def Gp_tx_n2 : ZExp 6 := -a * x * (a ^ 2 + r ^ 2) * (a ^ 2 - d + r ^ 2) * (a ^ 2 * x ^ 2 -
    a ^ 2 + d)
/-- `½ g^{pp} ∂_x g_{pt}`, reduced to the common denominator. -/
theorem Gp_tx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.half (ipp * Frac.d δx gtp)) (⟨Gp_tx_n2, Gp_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Gp_tx_n2,
        Gp_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `Γ^p_{tx}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_p_tx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Gp_tx_n1 + Gp_tx_n2, Gp_tx_cd⟩) (Gp_tx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_tx_n1, Gp_tx_n2, Gp_tx_cd, Gp_tx, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `Γ^p_{rp}` -/

/-- The common denominator of the terms of `Γ^p_{rp}`. -/
def Gp_rp_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3
/-- `Γ^p_{rp}`, reduced. -/
def Gp_rp : Frac 6 := ⟨2 * a ^ 4 * r * x ^ 2 - 2 * a ^ 4 * r + a ^ 4 * v * x ^ 4 - a ^ 4 * v *
    x ^ 2 + 2 * a ^ 2 * d * r + 2 * a ^ 2 * r ^ 3 * x ^ 2 - 2 * a ^ 2 * r ^ 3 + a ^ 2 * r ^ 2 *
    v * x ^ 2 - a ^ 2 * r ^ 2 * v + 2 * d * r ^ 3, 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2⟩

/-- The numerator of `½ g^{pt} ∂_r g_{tp}` over the common denominator. -/
def Gp_rp_n1 : ZExp 6 := -a ^ 2 * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) * (2 * a ^ 2 * r *
    x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `½ g^{pt} ∂_r g_{tp}`, reduced to the common denominator. -/
theorem Gp_rp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.half (itp * Frac.d δr gtp)) (⟨Gp_rp_n1, Gp_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Gp_rp_n1,
        Gp_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `½ g^{pp} ∂_r g_{pp}` over the common denominator. -/
def Gp_rp_n2 : ZExp 6 := (a ^ 2 * x ^ 2 - a ^ 2 + d) * (4 * a ^ 4 * r * x ^ 2 - 2 * a ^ 4 * r +
    a ^ 4 * v * x ^ 4 - a ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d * r * x ^ 2 + 2 * a ^ 2 * d * r + 4 *
    a ^ 2 * r ^ 3 * x ^ 2 + a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 * v + 2 * r ^ 5)
/-- `½ g^{pp} ∂_r g_{pp}`, reduced to the common denominator. -/
theorem Gp_rp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.half (ipp * Frac.d δr gpp)) (⟨Gp_rp_n2, Gp_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Gp_rp_n2,
        Gp_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `Γ^p_{rp}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_p_rp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Gp_rp_n1 + Gp_rp_n2, Gp_rp_cd⟩) (Gp_rp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rp_n1, Gp_rp_n2, Gp_rp_cd, Gp_rp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `Γ^p_{xp}` -/

/-- The common denominator of the terms of `Γ^p_{xp}`. -/
def Gp_xp_cd : ZExp 6 := d * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3
/-- `Γ^p_{xp}`, reduced. -/
def Gp_xp : Frac 6 := ⟨x * (a ^ 4 * x ^ 4 - a ^ 4 * x ^ 2 + a ^ 4 + a ^ 2 * d * x ^ 2 - a ^ 2 *
    d + a ^ 2 * r ^ 2 * x ^ 2 + a ^ 2 * r ^ 2 + r ^ 4), (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 +
    r ^ 2) ^ 2⟩

/-- The numerator of `½ g^{pt} ∂_x g_{tp}` over the common denominator. -/
def Gp_xp_n1 : ZExp 6 := -a ^ 2 * x * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) ^ 2
/-- `½ g^{pt} ∂_x g_{tp}`, reduced to the common denominator. -/
theorem Gp_xp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.half (itp * Frac.d δx gtp)) (⟨Gp_xp_n1, Gp_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Gp_xp_n1,
        Gp_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `½ g^{pp} ∂_x g_{pp}` over the common denominator. -/
def Gp_xp_n2 : ZExp 6 := x * (a ^ 2 * x ^ 2 - a ^ 2 + d) * (a ^ 6 + a ^ 4 * d * x ^ 4 - a ^ 4 *
    d + 3 * a ^ 4 * r ^ 2 + 2 * a ^ 2 * d * r ^ 2 * x ^ 2 - 2 * a ^ 2 * d * r ^ 2 + 3 * a ^ 2 *
    r ^ 4 + r ^ 6)
/-- `½ g^{pp} ∂_x g_{pp}`, reduced to the common denominator. -/
theorem Gp_xp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.half (ipp * Frac.d δx gpp)) (⟨Gp_xp_n2, Gp_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Gp_xp_n2,
        Gp_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `Γ^p_{xp}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_p_xp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Gp_xp_n1 + Gp_xp_n2, Gp_xp_cd⟩) (Gp_xp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_xp_n1, Gp_xp_n2, Gp_xp_cd, Gp_xp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)


end LeanProofs.IPRA.Geometry.KerrNewmanConnection
