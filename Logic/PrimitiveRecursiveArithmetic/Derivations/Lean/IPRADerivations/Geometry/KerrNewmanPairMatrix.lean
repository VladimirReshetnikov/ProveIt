import IPRADerivations.Geometry.KerrNewmanRiemannT
import IPRADerivations.Geometry.KerrNewmanRiemannR
import IPRADerivations.Geometry.KerrNewmanRiemannX
import IPRADerivations.Geometry.KerrNewmanRiemannP

/-!
# The pair matrix of the Riemann tensor and the pair inverse (`four_metrics_ipra`)

Packet: `geometry/four_metrics_ipra_2026-11-15`, `eq:paircontract`: "Order the six pairs `I = (i,
    j)` with
`i < j`. Let `C_{IJ} = R_{ijkℓ}` for `J = (k, ℓ)` and let `J_{(i,j),(k,ℓ)} = g^{ik} g^{jℓ} − g^{iℓ}
    g^{jk}`."

* `lower_ij_kl` with `C_ij_kl_tn`: `C_{IJ} = R_{ijkℓ} = Σ_h g_{ih} R^h_{jkℓ}` from the Riemann
    tensor of
  `Geometry/KerrNewmanRiemannT`, `…R`, `…X`, `…P` (radial function `d`, Boyer–Lindquist coordinates,
  index `p` for `φ`), each term reduced over a common denominator, the sum equal to the reduced
  fraction `C_ij_kl` or `0`;
* `pairinv_ij_kl`: the nonzero entries `J_ij_kl` of the pair inverse.

The product `M = C J` is `Geometry/KerrNewmanPairProduct`, the trace
    `Geometry/KerrNewmanKretschmann`.

The reduced fractions and numerators were proposed by a computer algebra script; every identity
is checked by Lean as an identity of fractions cleared of denominators, a closed sentence of iPRA
certified in every commutative ring.
-/

namespace LeanProofs.IPRA.Geometry.KerrNewmanPairMatrix

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Geometry.KerrNewmanBase (δr δx δr_0 δr_1 δr_2 δr_3 δr_4 δr_5 δx_0 δx_1 δx_2
  δx_3 δx_4 δx_5 Sg sx)
open LeanProofs.IPRA.Geometry.KerrNewmanConnection
open LeanProofs.IPRA.Geometry.KerrNewmanRiemannT
open LeanProofs.IPRA.Geometry.KerrNewmanRiemannR
open LeanProofs.IPRA.Geometry.KerrNewmanRiemannX
open LeanProofs.IPRA.Geometry.KerrNewmanRiemannP
open ZExp

local notation "r" => (ZExp.var 0 : ZExp 6)
local notation "x" => (ZExp.var 1 : ZExp 6)
local notation "a" => (ZExp.var 2 : ZExp 6)
local notation "d" => (ZExp.var 3 : ZExp 6)
local notation "v" => (ZExp.var 4 : ZExp 6)
local notation "w" => (ZExp.var 5 : ZExp 6)

/-! ## The lowered pair matrix `C_{IJ} = R_{ijkl}` -/

/-! ### `R_{trtr}` -/

/-- `R_{trtr}`, reduced. -/
def C_tr_tr : Frac 6 := ⟨-2 * a ^ 6 * x ^ 4 + 2 * a ^ 6 * x ^ 2 + a ^ 4 * d * w * x ^ 4 - 4 * a ^ 4
    * r ^ 2 * x ^ 4 + 6 * a ^ 4 * r ^ 2 * x ^ 2 - 2 * a ^ 4 * r ^ 2 + a ^ 4 * r * v * x ^ 4 - a ^ 4
    * r * v * x ^ 2 - 2 * a ^ 2 * d ^ 2 * x ^ 2 + 2 * a ^ 2 * d * r ^ 2 * w * x ^ 2 + 4 * a ^ 2 * d
    * r ^ 2 * x ^ 2 - 4 * a ^ 2 * d * r ^ 2 - 4 * a ^ 2 * d * r * v * x ^ 2 + a ^ 2 * r ^ 3 * v * x
    ^ 2 - a ^ 2 * r ^ 3 * v + 6 * d ^ 2 * r ^ 2 + d * r ^ 4 * w - 4 * d * r ^ 3 * v, 2 * d * (a ^ 2
    * x ^ 2 + r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `R_{trtr}`. -/
def C_tr_tr_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4

/-- The numerator of `g_{tt} R^t_{rtr}` over the common denominator. -/
def C_tr_tr_n1 : ZExp 6 := (a ^ 2 * x ^ 2 - a ^ 2 + d) * (a ^ 6 * w * x ^ 4 - 4 * a ^ 6 * x ^ 4 + 4
    * a ^ 6 * x ^ 2 + 2 * a ^ 4 * d * x ^ 4 - 4 * a ^ 4 * d * x ^ 2 + a ^ 4 * r ^ 2 * w * x ^ 4 + 2
    * a ^ 4 * r ^ 2 * w * x ^ 2 - 6 * a ^ 4 * r ^ 2 * x ^ 4 + 14 * a ^ 4 * r ^ 2 * x ^ 2 - 8 * a ^
    4 * r ^ 2 + a ^ 4 * r * v * x ^ 4 - 5 * a ^ 4 * r * v * x ^ 2 - 4 * a ^ 2 * d * r ^ 2 * x ^ 2 +
    8 * a ^ 2 * d * r ^ 2 + 2 * a ^ 2 * r ^ 4 * w * x ^ 2 + a ^ 2 * r ^ 4 * w + 6 * a ^ 2 * r ^ 4 *
    x ^ 2 - 6 * a ^ 2 * r ^ 4 - 3 * a ^ 2 * r ^ 3 * v * x ^ 2 - 5 * a ^ 2 * r ^ 3 * v + 6 * d * r ^
    4 + r ^ 6 * w - 4 * r ^ 5 * v)
/-- `g_{tt} R^t_{rtr}`, reduced to the common denominator. -/
theorem C_tr_tr_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (gtt * Qt_r_tr) (⟨C_tr_tr_n1, C_tr_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Qt_r_tr,
        C_tr_tr_n1, C_tr_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4,
        δx_5]
    ring)

/-- The numerator of `g_{tp} R^p_{rtr}` over the common denominator. -/
def C_tr_tr_n2 : ZExp 6 := -a ^ 2 * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) * (a ^ 4 * w * x ^ 4 -
    2 * a ^ 4 * x ^ 4 + 4 * a ^ 4 * x ^ 2 - 4 * a ^ 2 * d * x ^ 2 + 2 * a ^ 2 * r ^ 2 * w * x ^ 2 +
    10 * a ^ 2 * r ^ 2 * x ^ 2 - 8 * a ^ 2 * r ^ 2 - 5 * a ^ 2 * r * v * x ^ 2 + 8 * d * r ^ 2 + r
    ^ 4 * w - 5 * r ^ 3 * v)
/-- `g_{tp} R^p_{rtr}`, reduced to the common denominator. -/
theorem C_tr_tr_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (gtp * Qp_r_tr) (⟨C_tr_tr_n2, C_tr_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Qp_r_tr,
        C_tr_tr_n2, C_tr_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4,
        δx_5]
    ring)

/-- `R_{trtr} = Σ_h g_{th} R^h_{rtr}`: the reduced fraction. -/
theorem lower_tr_tr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨C_tr_tr_n1 + C_tr_tr_n2, C_tr_tr_cd⟩) (C_tr_tr))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_tr_tr_n1, C_tr_tr_n2, C_tr_tr_cd, C_tr_tr, δr_0, δr_1, δr_2, δr_3, δr_4,
        δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R_{trtx}` -/

/-- `R_{trtx}`, reduced. -/
def C_tr_tx : Frac 6 := ⟨3 * a ^ 2 * x * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2
    + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v), 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `R_{trtx}`. -/
def C_tr_tx_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4

/-- The numerator of `g_{tt} R^t_{rtx}` over the common denominator. -/
def C_tr_tx_n1 : ZExp 6 := a ^ 2 * x * (2 * a ^ 2 + d + 2 * r ^ 2) * (a ^ 2 * x ^ 2 - a ^ 2 + d) *
    (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v)
/-- `g_{tt} R^t_{rtx}`, reduced to the common denominator. -/
theorem C_tr_tx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (gtt * Qt_r_tx) (⟨C_tr_tx_n1, C_tr_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Qt_r_tx,
        C_tr_tx_n1, C_tr_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4,
        δx_5]
    ring)

/-- The numerator of `g_{tp} R^p_{rtx}` over the common denominator. -/
def C_tr_tx_n2 : ZExp 6 := -a ^ 2 * x * (a ^ 2 - d + r ^ 2) * (2 * a ^ 2 * x ^ 2 - 2 * a ^ 2 - d) *
    (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v)
/-- `g_{tp} R^p_{rtx}`, reduced to the common denominator. -/
theorem C_tr_tx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (gtp * Qp_r_tx) (⟨C_tr_tx_n2, C_tr_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Qp_r_tx,
        C_tr_tx_n2, C_tr_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4,
        δx_5]
    ring)

/-- `R_{trtx} = Σ_h g_{th} R^h_{rtx}`: the reduced fraction. -/
theorem lower_tr_tx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨C_tr_tx_n1 + C_tr_tx_n2, C_tr_tx_cd⟩) (C_tr_tx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_tr_tx_n1, C_tr_tx_n2, C_tr_tx_cd, C_tr_tx, δr_0, δr_1, δr_2, δr_3, δr_4,
        δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R_{trrp}` -/

/-- `R_{trrp}`, reduced. -/
def C_tr_rp : Frac 6 := ⟨-a * (x - 1) * (x + 1) * (2 * a ^ 6 * x ^ 2 + a ^ 4 * d * w * x ^ 4 - 2 *
    a ^ 4 * d * x ^ 4 + 6 * a ^ 4 * r ^ 2 * x ^ 2 - 2 * a ^ 4 * r ^ 2 - a ^ 4 * r * v * x ^ 2 - 2 *
    a ^ 2 * d ^ 2 * x ^ 2 + 2 * a ^ 2 * d * r ^ 2 * w * x ^ 2 + 4 * a ^ 2 * d * r ^ 2 * x ^ 2 - 4 *
    a ^ 2 * d * r ^ 2 - 4 * a ^ 2 * d * r * v * x ^ 2 + 4 * a ^ 2 * r ^ 4 * x ^ 2 - 2 * a ^ 2 * r ^
    4 - a ^ 2 * r ^ 3 * v * x ^ 2 - a ^ 2 * r ^ 3 * v + 6 * d ^ 2 * r ^ 2 + d * r ^ 4 * w + 2 * d *
    r ^ 4 - 4 * d * r ^ 3 * v - r ^ 5 * v), 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `R_{trrp}`. -/
def C_tr_rp_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4

/-- The numerator of `g_{tt} R^t_{rrp}` over the common denominator. -/
def C_tr_rp_n1 : ZExp 6 := -a * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 - a ^ 2 + d) *
    (a ^ 4 * w * x ^ 4 - 2 * a ^ 4 * x ^ 4 + 4 * a ^ 4 * x ^ 2 - 4 * a ^ 2 * d * x ^ 2 + 2 * a ^ 2
    * r ^ 2 * w * x ^ 2 + 10 * a ^ 2 * r ^ 2 * x ^ 2 - 8 * a ^ 2 * r ^ 2 - 5 * a ^ 2 * r * v * x ^
    2 + 8 * d * r ^ 2 + r ^ 4 * w - 5 * r ^ 3 * v)
/-- `g_{tt} R^t_{rrp}`, reduced to the common denominator. -/
theorem C_tr_rp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (gtt * Qt_r_rp) (⟨C_tr_rp_n1, C_tr_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Qt_r_rp,
        C_tr_rp_n1, C_tr_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4,
        δx_5]
    ring)

/-- The numerator of `g_{tp} R^p_{rrp}` over the common denominator. -/
def C_tr_rp_n2 : ZExp 6 := a * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) * (a ^ 6 * w * x ^ 6 - a ^ 6
    * w * x ^ 4 - 2 * a ^ 6 * x ^ 6 + 4 * a ^ 6 * x ^ 4 - 4 * a ^ 6 * x ^ 2 - 2 * a ^ 4 * d * x ^ 4
    + 4 * a ^ 4 * d * x ^ 2 + 2 * a ^ 4 * r ^ 2 * w * x ^ 4 - 2 * a ^ 4 * r ^ 2 * w * x ^ 2 + 6 * a
    ^ 4 * r ^ 2 * x ^ 4 - 18 * a ^ 4 * r ^ 2 * x ^ 2 + 8 * a ^ 4 * r ^ 2 - 4 * a ^ 4 * r * v * x ^
    4 + 5 * a ^ 4 * r * v * x ^ 2 + 8 * a ^ 2 * d * r ^ 2 * x ^ 2 - 8 * a ^ 2 * d * r ^ 2 + a ^ 2 *
    r ^ 4 * w * x ^ 2 - a ^ 2 * r ^ 4 * w - 4 * a ^ 2 * r ^ 4 * x ^ 2 + 2 * a ^ 2 * r ^ 4 - 3 * a ^
    2 * r ^ 3 * v * x ^ 2 + 5 * a ^ 2 * r ^ 3 * v - 2 * d * r ^ 4 + r ^ 5 * v)
/-- `g_{tp} R^p_{rrp}`, reduced to the common denominator. -/
theorem C_tr_rp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (gtp * Qp_r_rp) (⟨C_tr_rp_n2, C_tr_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Qp_r_rp,
        C_tr_rp_n2, C_tr_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4,
        δx_5]
    ring)

/-- `R_{trrp} = Σ_h g_{th} R^h_{rrp}`: the reduced fraction. -/
theorem lower_tr_rp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨C_tr_rp_n1 + C_tr_rp_n2, C_tr_rp_cd⟩) (C_tr_rp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_tr_rp_n1, C_tr_rp_n2, C_tr_rp_cd, C_tr_rp, δr_0, δr_1, δr_2, δr_3, δr_4,
        δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R_{trxp}` -/

/-- `R_{trxp}`, reduced. -/
def C_tr_xp : Frac 6 := ⟨-a * x * (a ^ 2 * x ^ 2 - 3 * a ^ 2 - 2 * r ^ 2) * (2 * a ^ 2 * r * x ^ 2
    - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v), 2 * (a ^ 2 * x ^ 2 +
    r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `R_{trxp}`. -/
def C_tr_xp_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4

/-- The numerator of `g_{tt} R^t_{rxp}` over the common denominator. -/
def C_tr_xp_n1 : ZExp 6 := -a * x * (a ^ 2 * x ^ 2 - a ^ 2 + d) * (-2 * a ^ 4 + a ^ 2 * d * x ^ 2 -
    a ^ 2 * d - 4 * a ^ 2 * r ^ 2 - 2 * r ^ 4) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v
    * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v)
/-- `g_{tt} R^t_{rxp}`, reduced to the common denominator. -/
theorem C_tr_xp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (gtt * Qt_r_xp) (⟨C_tr_xp_n1, C_tr_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Qt_r_xp,
        C_tr_xp_n1, C_tr_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4,
        δx_5]
    ring)

/-- The numerator of `g_{tp} R^p_{rxp}` over the common denominator. -/
def C_tr_xp_n2 : ZExp 6 := -a ^ 3 * x * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) * (2 * a ^ 2 + d +
    2 * r ^ 2) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3
    - r ^ 2 * v)
/-- `g_{tp} R^p_{rxp}`, reduced to the common denominator. -/
theorem C_tr_xp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (gtp * Qp_r_xp) (⟨C_tr_xp_n2, C_tr_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Qp_r_xp,
        C_tr_xp_n2, C_tr_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4,
        δx_5]
    ring)

/-- `R_{trxp} = Σ_h g_{th} R^h_{rxp}`: the reduced fraction. -/
theorem lower_tr_xp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨C_tr_xp_n1 + C_tr_xp_n2, C_tr_xp_cd⟩) (C_tr_xp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_tr_xp_n1, C_tr_xp_n2, C_tr_xp_cd, C_tr_xp, δr_0, δr_1, δr_2, δr_3, δr_4,
        δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R_{txtr}` -/

/-- `R_{txtr}`, reduced. -/
def C_tx_tr : Frac 6 := ⟨3 * a ^ 2 * x * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2
    + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v), 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `R_{txtr}`. -/
def C_tx_tr_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4

/-- The numerator of `g_{tt} R^t_{xtr}` over the common denominator. -/
def C_tx_tr_n1 : ZExp 6 := a ^ 2 * x * (a ^ 2 + 2 * d + r ^ 2) * (a ^ 2 * x ^ 2 - a ^ 2 + d) * (2 *
    a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v)
/-- `g_{tt} R^t_{xtr}`, reduced to the common denominator. -/
theorem C_tx_tr_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (gtt * Qt_x_tr) (⟨C_tx_tr_n1, C_tx_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Qt_x_tr,
        C_tx_tr_n1, C_tx_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4,
        δx_5]
    ring)

/-- The numerator of `g_{tp} R^p_{xtr}` over the common denominator. -/
def C_tx_tr_n2 : ZExp 6 := -a ^ 2 * x * (a ^ 2 - d + r ^ 2) * (a ^ 2 * x ^ 2 - a ^ 2 - 2 * d) * (2
    * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v)
/-- `g_{tp} R^p_{xtr}`, reduced to the common denominator. -/
theorem C_tx_tr_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (gtp * Qp_x_tr) (⟨C_tx_tr_n2, C_tx_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Qp_x_tr,
        C_tx_tr_n2, C_tx_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4,
        δx_5]
    ring)

/-- `R_{txtr} = Σ_h g_{th} R^h_{xtr}`: the reduced fraction. -/
theorem lower_tx_tr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨C_tx_tr_n1 + C_tx_tr_n2, C_tx_tr_cd⟩) (C_tx_tr))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_tx_tr_n1, C_tx_tr_n2, C_tx_tr_cd, C_tx_tr, δr_0, δr_1, δr_2, δr_3, δr_4,
        δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R_{txtx}` -/

/-- `R_{txtx}`, reduced. -/
def C_tx_tx : Frac 6 := ⟨-6 * a ^ 6 * x ^ 4 + 6 * a ^ 6 * x ^ 2 + 6 * a ^ 4 * d * x ^ 4 - 4 * a ^ 4
    * d * x ^ 2 - 6 * a ^ 4 * r ^ 2 * x ^ 4 + 8 * a ^ 4 * r ^ 2 * x ^ 2 - 2 * a ^ 4 * r ^ 2 - 2 * a
    ^ 2 * d ^ 2 * x ^ 2 + 2 * a ^ 2 * d * r ^ 2 * x ^ 2 - a ^ 2 * d * r * v * x ^ 2 + 2 * a ^ 2 * r
    ^ 4 * x ^ 2 - 2 * a ^ 2 * r ^ 4 + 2 * d ^ 2 * r ^ 2 - d * r ^ 3 * v, 2 * (x - 1) * (x + 1) * (a
    ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `R_{txtx}`. -/
def C_tx_tx_cd : ZExp 6 := 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4

/-- The numerator of `g_{tt} R^t_{xtx}` over the common denominator. -/
def C_tx_tx_n1 : ZExp 6 := -(a ^ 2 * x ^ 2 - a ^ 2 + d) * (6 * a ^ 6 * x ^ 4 - 8 * a ^ 6 * x ^ 2 -
    6 * a ^ 4 * d * x ^ 4 + 8 * a ^ 4 * d * x ^ 2 + 6 * a ^ 4 * r ^ 2 * x ^ 4 - 14 * a ^ 4 * r ^ 2
    * x ^ 2 + 4 * a ^ 4 * r ^ 2 + a ^ 4 * r * v * x ^ 2 + 4 * a ^ 2 * d * r ^ 2 * x ^ 2 - 4 * a ^ 2
    * d * r ^ 2 - 6 * a ^ 2 * r ^ 4 * x ^ 2 + 4 * a ^ 2 * r ^ 4 + a ^ 2 * r ^ 3 * v * x ^ 2 + a ^ 2
    * r ^ 3 * v - 2 * d * r ^ 4 + r ^ 5 * v)
/-- `g_{tt} R^t_{xtx}`, reduced to the common denominator. -/
theorem C_tx_tx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (gtt * Qt_x_tx) (⟨C_tx_tx_n1, C_tx_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Qt_x_tx,
        C_tx_tx_n1, C_tx_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4,
        δx_5]
    ring)

/-- The numerator of `g_{tp} R^p_{xtx}` over the common denominator. -/
def C_tx_tx_n2 : ZExp 6 := -a ^ 2 * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) * (8 * a ^ 4 * x ^ 2 -
    8 * a ^ 2 * d * x ^ 2 + 10 * a ^ 2 * r ^ 2 * x ^ 2 - 4 * a ^ 2 * r ^ 2 - a ^ 2 * r * v * x ^ 2
    + 4 * d * r ^ 2 - 2 * r ^ 4 - r ^ 3 * v)
/-- `g_{tp} R^p_{xtx}`, reduced to the common denominator. -/
theorem C_tx_tx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (gtp * Qp_x_tx) (⟨C_tx_tx_n2, C_tx_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Qp_x_tx,
        C_tx_tx_n2, C_tx_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4,
        δx_5]
    ring)

/-- `R_{txtx} = Σ_h g_{th} R^h_{xtx}`: the reduced fraction. -/
theorem lower_tx_tx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨C_tx_tx_n1 + C_tx_tx_n2, C_tx_tx_cd⟩) (C_tx_tx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_tx_tx_n1, C_tx_tx_n2, C_tx_tx_cd, C_tx_tx, δr_0, δr_1, δr_2, δr_3, δr_4,
        δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R_{txrp}` -/

/-- `R_{txrp}`, reduced. -/
def C_tx_rp : Frac 6 := ⟨-a * x * (2 * a ^ 2 * x ^ 2 - 3 * a ^ 2 - r ^ 2) * (2 * a ^ 2 * r * x ^ 2
    - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v), 2 * (a ^ 2 * x ^ 2 +
    r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `R_{txrp}`. -/
def C_tx_rp_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4

/-- The numerator of `g_{tt} R^t_{xrp}` over the common denominator. -/
def C_tx_rp_n1 : ZExp 6 := -a * x * (a ^ 2 * x ^ 2 - a ^ 2 + d) * (-a ^ 4 + 2 * a ^ 2 * d * x ^ 2 -
    2 * a ^ 2 * d - 2 * a ^ 2 * r ^ 2 - r ^ 4) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v
    * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v)
/-- `g_{tt} R^t_{xrp}`, reduced to the common denominator. -/
theorem C_tx_rp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (gtt * Qt_x_rp) (⟨C_tx_rp_n1, C_tx_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Qt_x_rp,
        C_tx_rp_n1, C_tx_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4,
        δx_5]
    ring)

/-- The numerator of `g_{tp} R^p_{xrp}` over the common denominator. -/
def C_tx_rp_n2 : ZExp 6 := -a ^ 3 * x * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) * (a ^ 2 + 2 * d +
    r ^ 2) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r
    ^ 2 * v)
/-- `g_{tp} R^p_{xrp}`, reduced to the common denominator. -/
theorem C_tx_rp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (gtp * Qp_x_rp) (⟨C_tx_rp_n2, C_tx_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Qp_x_rp,
        C_tx_rp_n2, C_tx_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4,
        δx_5]
    ring)

/-- `R_{txrp} = Σ_h g_{th} R^h_{xrp}`: the reduced fraction. -/
theorem lower_tx_rp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨C_tx_rp_n1 + C_tx_rp_n2, C_tx_rp_cd⟩) (C_tx_rp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_tx_rp_n1, C_tx_rp_n2, C_tx_rp_cd, C_tx_rp, δr_0, δr_1, δr_2, δr_3, δr_4,
        δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R_{txxp}` -/

/-- `R_{txxp}`, reduced. -/
def C_tx_xp : Frac 6 := ⟨-a * (6 * a ^ 6 * x ^ 2 - 4 * a ^ 4 * d * x ^ 2 + 12 * a ^ 4 * r ^ 2 * x ^
    2 - 2 * a ^ 4 * r ^ 2 - 2 * a ^ 2 * d ^ 2 * x ^ 2 - 2 * a ^ 2 * d * r ^ 2 * x ^ 2 - a ^ 2 * d *
    r * v * x ^ 2 + 6 * a ^ 2 * r ^ 4 * x ^ 2 - 4 * a ^ 2 * r ^ 4 + 2 * d ^ 2 * r ^ 2 + 2 * d * r ^
    4 - d * r ^ 3 * v - 2 * r ^ 6), 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `R_{txxp}`. -/
def C_tx_xp_cd : ZExp 6 := 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4

/-- The numerator of `g_{tt} R^t_{xxp}` over the common denominator. -/
def C_tx_xp_n1 : ZExp 6 := -a * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 - a ^ 2 + d) * (8 * a ^ 4 * x ^ 2
    - 8 * a ^ 2 * d * x ^ 2 + 10 * a ^ 2 * r ^ 2 * x ^ 2 - 4 * a ^ 2 * r ^ 2 - a ^ 2 * r * v * x ^
    2 + 4 * d * r ^ 2 - 2 * r ^ 4 - r ^ 3 * v)
/-- `g_{tt} R^t_{xxp}`, reduced to the common denominator. -/
theorem C_tx_xp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (gtt * Qt_x_xp) (⟨C_tx_xp_n1, C_tx_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Qt_x_xp,
        C_tx_xp_n1, C_tx_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4,
        δx_5]
    ring)

/-- The numerator of `g_{tp} R^p_{xxp}` over the common denominator. -/
def C_tx_xp_n2 : ZExp 6 := a * (a ^ 2 - d + r ^ 2) * (2 * a ^ 6 * x ^ 4 - 8 * a ^ 6 * x ^ 2 - 2 * a
    ^ 4 * d * x ^ 4 + 8 * a ^ 4 * d * x ^ 2 + 4 * a ^ 4 * r ^ 2 * x ^ 4 - 18 * a ^ 4 * r ^ 2 * x ^
    2 + 4 * a ^ 4 * r ^ 2 - a ^ 4 * r * v * x ^ 4 + a ^ 4 * r * v * x ^ 2 + 8 * a ^ 2 * d * r ^ 2 *
    x ^ 2 - 4 * a ^ 2 * d * r ^ 2 - 6 * a ^ 2 * r ^ 4 * x ^ 2 + 4 * a ^ 2 * r ^ 4 - a ^ 2 * r ^ 3 *
    v * x ^ 2 + a ^ 2 * r ^ 3 * v - 2 * d * r ^ 4 + 2 * r ^ 6)
/-- `g_{tp} R^p_{xxp}`, reduced to the common denominator. -/
theorem C_tx_xp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (gtp * Qp_x_xp) (⟨C_tx_xp_n2, C_tx_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Qp_x_xp,
        C_tx_xp_n2, C_tx_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4,
        δx_5]
    ring)

/-- `R_{txxp} = Σ_h g_{th} R^h_{xxp}`: the reduced fraction. -/
theorem lower_tx_xp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨C_tx_xp_n1 + C_tx_xp_n2, C_tx_xp_cd⟩) (C_tx_xp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_tx_xp_n1, C_tx_xp_n2, C_tx_xp_cd, C_tx_xp, δr_0, δr_1, δr_2, δr_3, δr_4,
        δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R_{tptp}` -/

/-- `R_{tptp}`, reduced. -/
def C_tp_tp : Frac 6 := ⟨d * (x - 1) * (x + 1) * (2 * a ^ 4 * x ^ 2 - 2 * a ^ 2 * d * x ^ 2 + 4 * a
    ^ 2 * r ^ 2 * x ^ 2 - 2 * a ^ 2 * r ^ 2 - a ^ 2 * r * v * x ^ 2 + 2 * d * r ^ 2 - r ^ 3 * v), 2
    * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `R_{tptp}`. -/
def C_tp_tp_cd : ZExp 6 := 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `g_{tt} R^t_{ptp}` over the common denominator. -/
def C_tp_tp_n1 : ZExp 6 := (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 - a ^ 2 + d) * (a ^ 4 + a ^ 2 * d * x
    ^ 2 - a ^ 2 * d + 2 * a ^ 2 * r ^ 2 + r ^ 4) * (2 * a ^ 4 * x ^ 2 - 2 * a ^ 2 * d * x ^ 2 + 4 *
    a ^ 2 * r ^ 2 * x ^ 2 - 2 * a ^ 2 * r ^ 2 - a ^ 2 * r * v * x ^ 2 + 2 * d * r ^ 2 - r ^ 3 * v)
/-- `g_{tt} R^t_{ptp}`, reduced to the common denominator. -/
theorem C_tp_tp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (gtt * Qt_p_tp) (⟨C_tp_tp_n1, C_tp_tp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Qt_p_tp,
        C_tp_tp_n1, C_tp_tp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4,
        δx_5]
    ring)

/-- The numerator of `g_{tp} R^p_{ptp}` over the common denominator. -/
def C_tp_tp_n2 : ZExp 6 := -a ^ 2 * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 - d + r ^ 2) ^ 2 * (2 * a ^
    4 * x ^ 2 - 2 * a ^ 2 * d * x ^ 2 + 4 * a ^ 2 * r ^ 2 * x ^ 2 - 2 * a ^ 2 * r ^ 2 - a ^ 2 * r *
    v * x ^ 2 + 2 * d * r ^ 2 - r ^ 3 * v)
/-- `g_{tp} R^p_{ptp}`, reduced to the common denominator. -/
theorem C_tp_tp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (gtp * Qp_p_tp) (⟨C_tp_tp_n2, C_tp_tp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Qp_p_tp,
        C_tp_tp_n2, C_tp_tp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4,
        δx_5]
    ring)

/-- `R_{tptp} = Σ_h g_{th} R^h_{ptp}`: the reduced fraction. -/
theorem lower_tp_tp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨C_tp_tp_n1 + C_tp_tp_n2, C_tp_tp_cd⟩) (C_tp_tp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_tp_tp_n1, C_tp_tp_n2, C_tp_tp_cd, C_tp_tp, δr_0, δr_1, δr_2, δr_3, δr_4,
        δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R_{tprx}` -/

/-- `R_{tprx}`, reduced. -/
def C_tp_rx : Frac 6 := ⟨-a * x * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 *
    d * r - 2 * r ^ 3 - r ^ 2 * v), 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2⟩

/-- The common denominator of the terms of `R_{tprx}`. -/
def C_tp_rx_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4

/-- The numerator of `g_{tt} R^t_{prx}` over the common denominator. -/
def C_tp_rx_n1 : ZExp 6 := -a * x * (a ^ 2 * x ^ 2 - a ^ 2 + d) * (a ^ 4 + a ^ 2 * d * x ^ 2 - a ^
    2 * d + 2 * a ^ 2 * r ^ 2 + r ^ 4) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2
    + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v)
/-- `g_{tt} R^t_{prx}`, reduced to the common denominator. -/
theorem C_tp_rx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (gtt * Qt_p_rx) (⟨C_tp_rx_n1, C_tp_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Qt_p_rx,
        C_tp_rx_n1, C_tp_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4,
        δx_5]
    ring)

/-- The numerator of `g_{tp} R^p_{prx}` over the common denominator. -/
def C_tp_rx_n2 : ZExp 6 := a ^ 3 * x * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) ^ 2 * (2 * a ^ 2 * r
    * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v)
/-- `g_{tp} R^p_{prx}`, reduced to the common denominator. -/
theorem C_tp_rx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (gtp * Qp_p_rx) (⟨C_tp_rx_n2, C_tp_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Qp_p_rx,
        C_tp_rx_n2, C_tp_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4,
        δx_5]
    ring)

/-- `R_{tprx} = Σ_h g_{th} R^h_{prx}`: the reduced fraction. -/
theorem lower_tp_rx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨C_tp_rx_n1 + C_tp_rx_n2, C_tp_rx_cd⟩) (C_tp_rx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_tp_rx_n1, C_tp_rx_n2, C_tp_rx_cd, C_tp_rx, δr_0, δr_1, δr_2, δr_3, δr_4,
        δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R_{rxtp}` -/

/-- `R_{rxtp}`, reduced. -/
def C_rx_tp : Frac 6 := ⟨-a * x * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 *
    d * r - 2 * r ^ 3 - r ^ 2 * v), 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2⟩

/-- The common denominator of the terms of `R_{rxtp}`. -/
def C_rx_tp_cd : ZExp 6 := 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2

/-- The numerator of `g_{rr} R^r_{xtp}` over the common denominator. -/
def C_rx_tp_n1 : ZExp 6 := -a * x * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4
    * d * r - 2 * r ^ 3 - r ^ 2 * v)
/-- `g_{rr} R^r_{xtp}`, reduced to the common denominator. -/
theorem C_rx_tp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (grr * Qr_x_tp) (⟨C_rx_tp_n1, C_rx_tp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Qr_x_tp,
        C_rx_tp_n1, C_rx_tp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4,
        δx_5]
    ring)

/-- `R_{rxtp} = Σ_h g_{rh} R^h_{xtp}`: the reduced fraction. -/
theorem lower_rx_tp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨C_rx_tp_n1, C_rx_tp_cd⟩) (C_rx_tp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_rx_tp_n1, C_rx_tp_cd, C_rx_tp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5])

/-! ### `R_{rxrx}` -/

/-- `R_{rxrx}`, reduced. -/
def C_rx_rx : Frac 6 := ⟨-2 * a ^ 4 * x ^ 2 + 2 * a ^ 2 * d * x ^ 2 - 4 * a ^ 2 * r ^ 2 * x ^ 2 + 2
    * a ^ 2 * r ^ 2 + a ^ 2 * r * v * x ^ 2 - 2 * d * r ^ 2 + r ^ 3 * v, 2 * d * (x - 1) * (x + 1)
    * (a ^ 2 * x ^ 2 + r ^ 2)⟩

/-- The common denominator of the terms of `R_{rxrx}`. -/
def C_rx_rx_cd : ZExp 6 := 2 * d * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2)

/-- The numerator of `g_{rr} R^r_{xrx}` over the common denominator. -/
def C_rx_rx_n1 : ZExp 6 := -2 * a ^ 4 * x ^ 2 + 2 * a ^ 2 * d * x ^ 2 - 4 * a ^ 2 * r ^ 2 * x ^ 2 +
    2 * a ^ 2 * r ^ 2 + a ^ 2 * r * v * x ^ 2 - 2 * d * r ^ 2 + r ^ 3 * v
/-- `g_{rr} R^r_{xrx}`, reduced to the common denominator. -/
theorem C_rx_rx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (grr * Qr_x_rx) (⟨C_rx_rx_n1, C_rx_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Qr_x_rx,
        C_rx_rx_n1, C_rx_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4,
        δx_5]
    ring)

/-- `R_{rxrx} = Σ_h g_{rh} R^h_{xrx}`: the reduced fraction. -/
theorem lower_rx_rx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨C_rx_rx_n1, C_rx_rx_cd⟩) (C_rx_rx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_rx_rx_n1, C_rx_rx_cd, C_rx_rx, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5])

/-! ### `R_{rptr}` -/

/-- `R_{rptr}`, reduced. -/
def C_rp_tr : Frac 6 := ⟨-a * (x - 1) * (x + 1) * (2 * a ^ 6 * x ^ 2 + a ^ 4 * d * w * x ^ 4 - 2 *
    a ^ 4 * d * x ^ 4 + 6 * a ^ 4 * r ^ 2 * x ^ 2 - 2 * a ^ 4 * r ^ 2 - a ^ 4 * r * v * x ^ 2 - 2 *
    a ^ 2 * d ^ 2 * x ^ 2 + 2 * a ^ 2 * d * r ^ 2 * w * x ^ 2 + 4 * a ^ 2 * d * r ^ 2 * x ^ 2 - 4 *
    a ^ 2 * d * r ^ 2 - 4 * a ^ 2 * d * r * v * x ^ 2 + 4 * a ^ 2 * r ^ 4 * x ^ 2 - 2 * a ^ 2 * r ^
    4 - a ^ 2 * r ^ 3 * v * x ^ 2 - a ^ 2 * r ^ 3 * v + 6 * d ^ 2 * r ^ 2 + d * r ^ 4 * w + 2 * d *
    r ^ 4 - 4 * d * r ^ 3 * v - r ^ 5 * v), 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `R_{rptr}`. -/
def C_rp_tr_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3

/-- The numerator of `g_{rr} R^r_{ptr}` over the common denominator. -/
def C_rp_tr_n1 : ZExp 6 := -a * (x - 1) * (x + 1) * (2 * a ^ 6 * x ^ 2 + a ^ 4 * d * w * x ^ 4 - 2
    * a ^ 4 * d * x ^ 4 + 6 * a ^ 4 * r ^ 2 * x ^ 2 - 2 * a ^ 4 * r ^ 2 - a ^ 4 * r * v * x ^ 2 - 2
    * a ^ 2 * d ^ 2 * x ^ 2 + 2 * a ^ 2 * d * r ^ 2 * w * x ^ 2 + 4 * a ^ 2 * d * r ^ 2 * x ^ 2 - 4
    * a ^ 2 * d * r ^ 2 - 4 * a ^ 2 * d * r * v * x ^ 2 + 4 * a ^ 2 * r ^ 4 * x ^ 2 - 2 * a ^ 2 * r
    ^ 4 - a ^ 2 * r ^ 3 * v * x ^ 2 - a ^ 2 * r ^ 3 * v + 6 * d ^ 2 * r ^ 2 + d * r ^ 4 * w + 2 * d
    * r ^ 4 - 4 * d * r ^ 3 * v - r ^ 5 * v)
/-- `g_{rr} R^r_{ptr}`, reduced to the common denominator. -/
theorem C_rp_tr_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (grr * Qr_p_tr) (⟨C_rp_tr_n1, C_rp_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Qr_p_tr,
        C_rp_tr_n1, C_rp_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4,
        δx_5]
    ring)

/-- `R_{rptr} = Σ_h g_{rh} R^h_{ptr}`: the reduced fraction. -/
theorem lower_rp_tr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨C_rp_tr_n1, C_rp_tr_cd⟩) (C_rp_tr))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_rp_tr_n1, C_rp_tr_cd, C_rp_tr, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5])

/-! ### `R_{rptx}` -/

/-- `R_{rptx}`, reduced. -/
def C_rp_tx : Frac 6 := ⟨-a * x * (2 * a ^ 2 * x ^ 2 - 3 * a ^ 2 - r ^ 2) * (2 * a ^ 2 * r * x ^ 2
    - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v), 2 * (a ^ 2 * x ^ 2 +
    r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `R_{rptx}`. -/
def C_rp_tx_cd : ZExp 6 := 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3

/-- The numerator of `g_{rr} R^r_{ptx}` over the common denominator. -/
def C_rp_tx_n1 : ZExp 6 := -a * x * (2 * a ^ 2 * x ^ 2 - 3 * a ^ 2 - r ^ 2) * (2 * a ^ 2 * r * x ^
    2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v)
/-- `g_{rr} R^r_{ptx}`, reduced to the common denominator. -/
theorem C_rp_tx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (grr * Qr_p_tx) (⟨C_rp_tx_n1, C_rp_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Qr_p_tx,
        C_rp_tx_n1, C_rp_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4,
        δx_5]
    ring)

/-- `R_{rptx} = Σ_h g_{rh} R^h_{ptx}`: the reduced fraction. -/
theorem lower_rp_tx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨C_rp_tx_n1, C_rp_tx_cd⟩) (C_rp_tx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_rp_tx_n1, C_rp_tx_cd, C_rp_tx, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5])

/-! ### `R_{rprp}` -/

/-- `R_{rprp}`, reduced. -/
def C_rp_rp : Frac 6 := ⟨(x - 1) * (x + 1) * (-2 * a ^ 8 * x ^ 2 + a ^ 6 * d * w * x ^ 6 - a ^ 6 *
    d * w * x ^ 4 - 2 * a ^ 6 * d * x ^ 6 + 4 * a ^ 6 * d * x ^ 4 - 8 * a ^ 6 * r ^ 2 * x ^ 2 + 2 *
    a ^ 6 * r ^ 2 + a ^ 6 * r * v * x ^ 2 - 2 * a ^ 4 * d ^ 2 * x ^ 4 + 2 * a ^ 4 * d ^ 2 * x ^ 2 +
    2 * a ^ 4 * d * r ^ 2 * w * x ^ 4 - 2 * a ^ 4 * d * r ^ 2 * w * x ^ 2 + 6 * a ^ 4 * d * r ^ 2 *
    x ^ 4 - 8 * a ^ 4 * d * r ^ 2 * x ^ 2 + 4 * a ^ 4 * d * r ^ 2 - 4 * a ^ 4 * d * r * v * x ^ 4 +
    4 * a ^ 4 * d * r * v * x ^ 2 - 10 * a ^ 4 * r ^ 4 * x ^ 2 + 4 * a ^ 4 * r ^ 4 + 2 * a ^ 4 * r
    ^ 3 * v * x ^ 2 + a ^ 4 * r ^ 3 * v + 6 * a ^ 2 * d ^ 2 * r ^ 2 * x ^ 2 - 6 * a ^ 2 * d ^ 2 * r
    ^ 2 + a ^ 2 * d * r ^ 4 * w * x ^ 2 - a ^ 2 * d * r ^ 4 * w + 2 * a ^ 2 * d * r ^ 4 * x ^ 2 - 4
    * a ^ 2 * d * r ^ 4 - 4 * a ^ 2 * d * r ^ 3 * v * x ^ 2 + 4 * a ^ 2 * d * r ^ 3 * v - 4 * a ^ 2
    * r ^ 6 * x ^ 2 + 2 * a ^ 2 * r ^ 6 + a ^ 2 * r ^ 5 * v * x ^ 2 + 2 * a ^ 2 * r ^ 5 * v - 2 * d
    * r ^ 6 + r ^ 7 * v), 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `R_{rprp}`. -/
def C_rp_rp_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3

/-- The numerator of `g_{rr} R^r_{prp}` over the common denominator. -/
def C_rp_rp_n1 : ZExp 6 := (x - 1) * (x + 1) * (-2 * a ^ 8 * x ^ 2 + a ^ 6 * d * w * x ^ 6 - a ^ 6
    * d * w * x ^ 4 - 2 * a ^ 6 * d * x ^ 6 + 4 * a ^ 6 * d * x ^ 4 - 8 * a ^ 6 * r ^ 2 * x ^ 2 + 2
    * a ^ 6 * r ^ 2 + a ^ 6 * r * v * x ^ 2 - 2 * a ^ 4 * d ^ 2 * x ^ 4 + 2 * a ^ 4 * d ^ 2 * x ^ 2
    + 2 * a ^ 4 * d * r ^ 2 * w * x ^ 4 - 2 * a ^ 4 * d * r ^ 2 * w * x ^ 2 + 6 * a ^ 4 * d * r ^ 2
    * x ^ 4 - 8 * a ^ 4 * d * r ^ 2 * x ^ 2 + 4 * a ^ 4 * d * r ^ 2 - 4 * a ^ 4 * d * r * v * x ^ 4
    + 4 * a ^ 4 * d * r * v * x ^ 2 - 10 * a ^ 4 * r ^ 4 * x ^ 2 + 4 * a ^ 4 * r ^ 4 + 2 * a ^ 4 *
    r ^ 3 * v * x ^ 2 + a ^ 4 * r ^ 3 * v + 6 * a ^ 2 * d ^ 2 * r ^ 2 * x ^ 2 - 6 * a ^ 2 * d ^ 2 *
    r ^ 2 + a ^ 2 * d * r ^ 4 * w * x ^ 2 - a ^ 2 * d * r ^ 4 * w + 2 * a ^ 2 * d * r ^ 4 * x ^ 2 -
    4 * a ^ 2 * d * r ^ 4 - 4 * a ^ 2 * d * r ^ 3 * v * x ^ 2 + 4 * a ^ 2 * d * r ^ 3 * v - 4 * a ^
    2 * r ^ 6 * x ^ 2 + 2 * a ^ 2 * r ^ 6 + a ^ 2 * r ^ 5 * v * x ^ 2 + 2 * a ^ 2 * r ^ 5 * v - 2 *
    d * r ^ 6 + r ^ 7 * v)
/-- `g_{rr} R^r_{prp}`, reduced to the common denominator. -/
theorem C_rp_rp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (grr * Qr_p_rp) (⟨C_rp_rp_n1, C_rp_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Qr_p_rp,
        C_rp_rp_n1, C_rp_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4,
        δx_5]
    ring)

/-- `R_{rprp} = Σ_h g_{rh} R^h_{prp}`: the reduced fraction. -/
theorem lower_rp_rp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨C_rp_rp_n1, C_rp_rp_cd⟩) (C_rp_rp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_rp_rp_n1, C_rp_rp_cd, C_rp_rp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5])

/-! ### `R_{rpxp}` -/

/-- `R_{rpxp}`, reduced. -/
def C_rp_xp : Frac 6 := ⟨-3 * a ^ 2 * x * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (2 * a ^ 2 * r * x
    ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v), 2 * (a ^ 2 * x ^
    2 + r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `R_{rpxp}`. -/
def C_rp_xp_cd : ZExp 6 := 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3

/-- The numerator of `g_{rr} R^r_{pxp}` over the common denominator. -/
def C_rp_xp_n1 : ZExp 6 := -3 * a ^ 2 * x * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (2 * a ^ 2 * r *
    x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v)
/-- `g_{rr} R^r_{pxp}`, reduced to the common denominator. -/
theorem C_rp_xp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (grr * Qr_p_xp) (⟨C_rp_xp_n1, C_rp_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Qr_p_xp,
        C_rp_xp_n1, C_rp_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4,
        δx_5]
    ring)

/-- `R_{rpxp} = Σ_h g_{rh} R^h_{pxp}`: the reduced fraction. -/
theorem lower_rp_xp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨C_rp_xp_n1, C_rp_xp_cd⟩) (C_rp_xp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_rp_xp_n1, C_rp_xp_cd, C_rp_xp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5])

/-! ### `R_{xptr}` -/

/-- `R_{xptr}`, reduced. -/
def C_xp_tr : Frac 6 := ⟨-a * x * (a ^ 2 * x ^ 2 - 3 * a ^ 2 - 2 * r ^ 2) * (2 * a ^ 2 * r * x ^ 2
    - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v), 2 * (a ^ 2 * x ^ 2 +
    r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `R_{xptr}`. -/
def C_xp_tr_cd : ZExp 6 := 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3

/-- The numerator of `g_{xx} R^x_{ptr}` over the common denominator. -/
def C_xp_tr_n1 : ZExp 6 := -a * x * (a ^ 2 * x ^ 2 - 3 * a ^ 2 - 2 * r ^ 2) * (2 * a ^ 2 * r * x ^
    2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v)
/-- `g_{xx} R^x_{ptr}`, reduced to the common denominator. -/
theorem C_xp_tr_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (gxx * Qx_p_tr) (⟨C_xp_tr_n1, C_xp_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Qx_p_tr,
        C_xp_tr_n1, C_xp_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4,
        δx_5]
    ring)

/-- `R_{xptr} = Σ_h g_{xh} R^h_{ptr}`: the reduced fraction. -/
theorem lower_xp_tr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨C_xp_tr_n1, C_xp_tr_cd⟩) (C_xp_tr))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_xp_tr_n1, C_xp_tr_cd, C_xp_tr, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5])

/-! ### `R_{xptx}` -/

/-- `R_{xptx}`, reduced. -/
def C_xp_tx : Frac 6 := ⟨-a * (6 * a ^ 6 * x ^ 2 - 4 * a ^ 4 * d * x ^ 2 + 12 * a ^ 4 * r ^ 2 * x ^
    2 - 2 * a ^ 4 * r ^ 2 - 2 * a ^ 2 * d ^ 2 * x ^ 2 - 2 * a ^ 2 * d * r ^ 2 * x ^ 2 - a ^ 2 * d *
    r * v * x ^ 2 + 6 * a ^ 2 * r ^ 4 * x ^ 2 - 4 * a ^ 2 * r ^ 4 + 2 * d ^ 2 * r ^ 2 + 2 * d * r ^
    4 - d * r ^ 3 * v - 2 * r ^ 6), 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `R_{xptx}`. -/
def C_xp_tx_cd : ZExp 6 := 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3

/-- The numerator of `g_{xx} R^x_{ptx}` over the common denominator. -/
def C_xp_tx_n1 : ZExp 6 := -a * (6 * a ^ 6 * x ^ 2 - 4 * a ^ 4 * d * x ^ 2 + 12 * a ^ 4 * r ^ 2 * x
    ^ 2 - 2 * a ^ 4 * r ^ 2 - 2 * a ^ 2 * d ^ 2 * x ^ 2 - 2 * a ^ 2 * d * r ^ 2 * x ^ 2 - a ^ 2 * d
    * r * v * x ^ 2 + 6 * a ^ 2 * r ^ 4 * x ^ 2 - 4 * a ^ 2 * r ^ 4 + 2 * d ^ 2 * r ^ 2 + 2 * d * r
    ^ 4 - d * r ^ 3 * v - 2 * r ^ 6)
/-- `g_{xx} R^x_{ptx}`, reduced to the common denominator. -/
theorem C_xp_tx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (gxx * Qx_p_tx) (⟨C_xp_tx_n1, C_xp_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Qx_p_tx,
        C_xp_tx_n1, C_xp_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4,
        δx_5]
    ring)

/-- `R_{xptx} = Σ_h g_{xh} R^h_{ptx}`: the reduced fraction. -/
theorem lower_xp_tx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨C_xp_tx_n1, C_xp_tx_cd⟩) (C_xp_tx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_xp_tx_n1, C_xp_tx_cd, C_xp_tx, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5])

/-! ### `R_{xprp}` -/

/-- `R_{xprp}`, reduced. -/
def C_xp_rp : Frac 6 := ⟨-3 * a ^ 2 * x * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (2 * a ^ 2 * r * x
    ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v), 2 * (a ^ 2 * x ^
    2 + r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `R_{xprp}`. -/
def C_xp_rp_cd : ZExp 6 := 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3

/-- The numerator of `g_{xx} R^x_{prp}` over the common denominator. -/
def C_xp_rp_n1 : ZExp 6 := -3 * a ^ 2 * x * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (2 * a ^ 2 * r *
    x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v)
/-- `g_{xx} R^x_{prp}`, reduced to the common denominator. -/
theorem C_xp_rp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (gxx * Qx_p_rp) (⟨C_xp_rp_n1, C_xp_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Qx_p_rp,
        C_xp_rp_n1, C_xp_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4,
        δx_5]
    ring)

/-- `R_{xprp} = Σ_h g_{xh} R^h_{prp}`: the reduced fraction. -/
theorem lower_xp_rp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨C_xp_rp_n1, C_xp_rp_cd⟩) (C_xp_rp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_xp_rp_n1, C_xp_rp_cd, C_xp_rp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5])

/-! ### `R_{xpxp}` -/

/-- `R_{xpxp}`, reduced. -/
def C_xp_xp : Frac 6 := ⟨-6 * a ^ 8 * x ^ 2 + 2 * a ^ 6 * d * x ^ 4 + 4 * a ^ 6 * d * x ^ 2 - 18 *
    a ^ 6 * r ^ 2 * x ^ 2 + 2 * a ^ 6 * r ^ 2 - 2 * a ^ 4 * d ^ 2 * x ^ 4 + 2 * a ^ 4 * d ^ 2 * x ^
    2 + 4 * a ^ 4 * d * r ^ 2 * x ^ 4 + 6 * a ^ 4 * d * r ^ 2 * x ^ 2 - a ^ 4 * d * r * v * x ^ 4 +
    a ^ 4 * d * r * v * x ^ 2 - 18 * a ^ 4 * r ^ 4 * x ^ 2 + 6 * a ^ 4 * r ^ 4 + 2 * a ^ 2 * d ^ 2
    * r ^ 2 * x ^ 2 - 2 * a ^ 2 * d ^ 2 * r ^ 2 + 6 * a ^ 2 * d * r ^ 4 * x ^ 2 - 4 * a ^ 2 * d * r
    ^ 4 - a ^ 2 * d * r ^ 3 * v * x ^ 2 + a ^ 2 * d * r ^ 3 * v - 6 * a ^ 2 * r ^ 6 * x ^ 2 + 6 * a
    ^ 2 * r ^ 6 - 2 * d * r ^ 6 + 2 * r ^ 8, 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `R_{xpxp}`. -/
def C_xp_xp_cd : ZExp 6 := 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3

/-- The numerator of `g_{xx} R^x_{pxp}` over the common denominator. -/
def C_xp_xp_n1 : ZExp 6 := -6 * a ^ 8 * x ^ 2 + 2 * a ^ 6 * d * x ^ 4 + 4 * a ^ 6 * d * x ^ 2 - 18
    * a ^ 6 * r ^ 2 * x ^ 2 + 2 * a ^ 6 * r ^ 2 - 2 * a ^ 4 * d ^ 2 * x ^ 4 + 2 * a ^ 4 * d ^ 2 * x
    ^ 2 + 4 * a ^ 4 * d * r ^ 2 * x ^ 4 + 6 * a ^ 4 * d * r ^ 2 * x ^ 2 - a ^ 4 * d * r * v * x ^ 4
    + a ^ 4 * d * r * v * x ^ 2 - 18 * a ^ 4 * r ^ 4 * x ^ 2 + 6 * a ^ 4 * r ^ 4 + 2 * a ^ 2 * d ^
    2 * r ^ 2 * x ^ 2 - 2 * a ^ 2 * d ^ 2 * r ^ 2 + 6 * a ^ 2 * d * r ^ 4 * x ^ 2 - 4 * a ^ 2 * d *
    r ^ 4 - a ^ 2 * d * r ^ 3 * v * x ^ 2 + a ^ 2 * d * r ^ 3 * v - 6 * a ^ 2 * r ^ 6 * x ^ 2 + 6 *
    a ^ 2 * r ^ 6 - 2 * d * r ^ 6 + 2 * r ^ 8
/-- `g_{xx} R^x_{pxp}`, reduced to the common denominator. -/
theorem C_xp_xp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (gxx * Qx_p_xp) (⟨C_xp_xp_n1, C_xp_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, Qx_p_xp,
        C_xp_xp_n1, C_xp_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4,
        δx_5]
    ring)

/-- `R_{xpxp} = Σ_h g_{xh} R^h_{pxp}`: the reduced fraction. -/
theorem lower_xp_xp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨C_xp_xp_n1, C_xp_xp_cd⟩) (C_xp_xp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_xp_xp_n1, C_xp_xp_cd, C_xp_xp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5])

/-! ## The pair inverse `J_{IK} = g^{ik} g^{jl} − g^{il} g^{jk}` -/

/-- `J_{tr,tr}`, reduced. -/
def J_tr_tr : Frac 6 := ⟨-a ^ 4 - a ^ 2 * d * x ^ 2 + a ^ 2 * d - 2 * a ^ 2 * r ^ 2 - r ^ 4, (a ^ 2
    * x ^ 2 + r ^ 2) ^ 2⟩

/-- `J_{tr,tr} = g^{tt} g^{rr} − g^{tr} g^{rt}`. -/
theorem pairinv_tr_tr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (itt * irr - (Frac.ofZ 0) * (Frac.ofZ 0)) (J_tr_tr))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, J_tr_tr, δr_0,
        δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `J_{tr,rp}`, reduced. -/
def J_tr_rp : Frac 6 := ⟨a * (a ^ 2 - d + r ^ 2), (a ^ 2 * x ^ 2 + r ^ 2) ^ 2⟩

/-- `J_{tr,rp} = g^{tr} g^{rp} − g^{tp} g^{rr}`. -/
theorem pairinv_tr_rp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn ((Frac.ofZ 0) * (Frac.ofZ 0) - itp * irr) (J_tr_rp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, J_tr_rp, δr_0,
        δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `J_{tx,tx}`, reduced. -/
def J_tx_tx : Frac 6 := ⟨(x - 1) * (x + 1) * (a ^ 4 + a ^ 2 * d * x ^ 2 - a ^ 2 * d + 2 * a ^ 2 * r
    ^ 2 + r ^ 4), d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2⟩

/-- `J_{tx,tx} = g^{tt} g^{xx} − g^{tx} g^{xt}`. -/
theorem pairinv_tx_tx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (itt * ixx - (Frac.ofZ 0) * (Frac.ofZ 0)) (J_tx_tx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, J_tx_tx, δr_0,
        δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `J_{tx,xp}`, reduced. -/
def J_tx_xp : Frac 6 := ⟨-a * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2), d * (a ^ 2 * x ^ 2 + r ^ 2)
    ^ 2⟩

/-- `J_{tx,xp} = g^{tx} g^{xp} − g^{tp} g^{xx}`. -/
theorem pairinv_tx_xp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn ((Frac.ofZ 0) * (Frac.ofZ 0) - itp * ixx) (J_tx_xp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, J_tx_xp, δr_0,
        δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `J_{tp,tp}`, reduced. -/
def J_tp_tp : Frac 6 := ⟨1, d * (x - 1) * (x + 1)⟩

/-- `J_{tp,tp} = g^{tt} g^{pp} − g^{tp} g^{pt}`. -/
theorem pairinv_tp_tp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (itt * ipp - itp * itp) (J_tp_tp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, J_tp_tp, δr_0,
        δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `J_{rx,rx}`, reduced. -/
def J_rx_rx : Frac 6 := ⟨-d * (x - 1) * (x + 1), (a ^ 2 * x ^ 2 + r ^ 2) ^ 2⟩

/-- `J_{rx,rx} = g^{rr} g^{xx} − g^{rx} g^{xr}`. -/
theorem pairinv_rx_rx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (irr * ixx - (Frac.ofZ 0) * (Frac.ofZ 0)) (J_rx_rx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, J_rx_rx, δr_0,
        δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `J_{rp,tr}`, reduced. -/
def J_rp_tr : Frac 6 := ⟨a * (a ^ 2 - d + r ^ 2), (a ^ 2 * x ^ 2 + r ^ 2) ^ 2⟩

/-- `J_{rp,tr} = g^{rt} g^{pr} − g^{rr} g^{pt}`. -/
theorem pairinv_rp_tr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn ((Frac.ofZ 0) * (Frac.ofZ 0) - irr * itp) (J_rp_tr))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, J_rp_tr, δr_0,
        δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `J_{rp,rp}`, reduced. -/
def J_rp_rp : Frac 6 := ⟨-a ^ 2 * x ^ 2 + a ^ 2 - d, (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^
    2⟩

/-- `J_{rp,rp} = g^{rr} g^{pp} − g^{rp} g^{pr}`. -/
theorem pairinv_rp_rp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (irr * ipp - (Frac.ofZ 0) * (Frac.ofZ 0)) (J_rp_rp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, J_rp_rp, δr_0,
        δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `J_{xp,tx}`, reduced. -/
def J_xp_tx : Frac 6 := ⟨-a * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2), d * (a ^ 2 * x ^ 2 + r ^ 2)
    ^ 2⟩

/-- `J_{xp,tx} = g^{xt} g^{px} − g^{xx} g^{pt}`. -/
theorem pairinv_xp_tx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn ((Frac.ofZ 0) * (Frac.ofZ 0) - ixx * itp) (J_xp_tx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, J_xp_tx, δr_0,
        δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `J_{xp,xp}`, reduced. -/
def J_xp_xp : Frac 6 := ⟨a ^ 2 * x ^ 2 - a ^ 2 + d, d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2⟩

/-- `J_{xp,xp} = g^{xx} g^{pp} − g^{xp} g^{px}`. -/
theorem pairinv_xp_xp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (ixx * ipp - (Frac.ofZ 0) * (Frac.ofZ 0)) (J_xp_xp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gtt, gtp, gpp, grr, gxx, itt, itp, ipp, irr, ixx, Sg, sx, Pp, J_xp_xp, δr_0,
        δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

end LeanProofs.IPRA.Geometry.KerrNewmanPairMatrix
