import IPRADerivations.Geometry.KerrNewmanConnectionDerivatives

/-!
# The Riemann tensor of the radial-function metric, upper index `r` (`four_metrics_ipra`)

Packet: `geometry/four_metrics_ipra_2026-11-15`, `eq:Riemann`: `R^i_{jkℓ} = ∂_k Γ^i_{ℓj} − ∂_ℓ
    Γ^i_{kj} + Σ_h (Γ^i_{kh} Γ^h_{ℓj} − Γ^i_{ℓh} Γ^h_{kj})`, here for
`i = r`, with the connection of `Geometry/KerrNewmanConnection` and its reduced derivatives of
`Geometry/KerrNewmanConnectionDerivatives` (radial function `d`, `∂_r d = v`, `∂_r v = w`;
Boyer–Lindquist coordinates, index `p` for `φ`; `∂_t = ∂_φ = 0`).

For each component `R^r_{jkℓ}` with `k < ℓ` that has a term with nonzero factors:
`Qr_j_kl_tn` (each term reduced over a common denominator) and `riemann_r_j_kl` (their
signed sum is the reduced fraction `Qr_j_kl`, or `0`). The upper indices `t`, `r`, `x`, `φ` are
the four modules `Geometry/KerrNewmanRiemannT`, `…R`, `…X`, `…P`; the contraction is
`Geometry/KerrNewmanKretschmann`. The curvature symmetries and the contraction to the Ricci
tensor (`Geometry/KerrNewmanRicci`) are not restated.

The reduced fractions and numerators were proposed by a computer algebra script; every identity
is checked by Lean as an identity of fractions cleared of denominators, a closed sentence of iPRA
certified in every commutative ring.
-/

namespace LeanProofs.IPRA.Geometry.KerrNewmanRiemannR

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Geometry.KerrNewmanBase (δr δx δr_0 δr_1 δr_2 δr_3 δr_4 δr_5 δx_0 δx_1 δx_2
  δx_3 δx_4 δx_5 Sg sx)
open LeanProofs.IPRA.Geometry.KerrNewmanConnection
open LeanProofs.IPRA.Geometry.KerrNewmanConnectionDerivatives
open ZExp

local notation "r" => (ZExp.var 0 : ZExp 6)
local notation "x" => (ZExp.var 1 : ZExp 6)
local notation "a" => (ZExp.var 2 : ZExp 6)
local notation "d" => (ZExp.var 3 : ZExp 6)
local notation "v" => (ZExp.var 4 : ZExp 6)
local notation "w" => (ZExp.var 5 : ZExp 6)

/-! ### `R^r_{ttr}` -/

/-- `R^r_{ttr}`, reduced. -/
def Qr_t_tr : Frac 6 := ⟨2 * a ^ 6 * x ^ 4 - 2 * a ^ 6 * x ^ 2 - a ^ 4 * d * w * x ^ 4 + 4 * a ^ 4
    * r ^ 2 * x ^ 4 - 6 * a ^ 4 * r ^ 2 * x ^ 2 + 2 * a ^ 4 * r ^ 2 - a ^ 4 * r * v * x ^ 4 + a ^ 4
    * r * v * x ^ 2 + 2 * a ^ 2 * d ^ 2 * x ^ 2 - 2 * a ^ 2 * d * r ^ 2 * w * x ^ 2 - 4 * a ^ 2 * d
    * r ^ 2 * x ^ 2 + 4 * a ^ 2 * d * r ^ 2 + 4 * a ^ 2 * d * r * v * x ^ 2 - a ^ 2 * r ^ 3 * v * x
    ^ 2 + a ^ 2 * r ^ 3 * v - 6 * d ^ 2 * r ^ 2 - d * r ^ 4 * w + 4 * d * r ^ 3 * v, 2 * (a ^ 2 * x
    ^ 2 + r ^ 2) ^ 4⟩

/-- The common denominator of the terms of `R^r_{ttr}`. -/
def Qr_t_tr_cd : ZExp 6 := 4 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `∂_r Γ^r_{tt}` over the common denominator. -/
def Qr_t_tr_n1 : ZExp 6 := -2 * (a ^ 2 * x ^ 2 + r ^ 2) * (-a ^ 4 * d * w * x ^ 4 + 2 * a ^ 4 * d *
    x ^ 4 - 2 * a ^ 4 * d * x ^ 2 + 2 * a ^ 4 * r * v * x ^ 4 - 2 * a ^ 4 * r * v * x ^ 2 - a ^ 4 *
    v ^ 2 * x ^ 4 + 2 * a ^ 2 * d ^ 2 * x ^ 2 - 2 * a ^ 2 * d * r ^ 2 * w * x ^ 2 - 10 * a ^ 2 * d
    * r ^ 2 * x ^ 2 + 10 * a ^ 2 * d * r ^ 2 + 8 * a ^ 2 * d * r * v * x ^ 2 + 2 * a ^ 2 * r ^ 3 *
    v * x ^ 2 - 2 * a ^ 2 * r ^ 3 * v - 2 * a ^ 2 * r ^ 2 * v ^ 2 * x ^ 2 - 10 * d ^ 2 * r ^ 2 - d
    * r ^ 4 * w + 8 * d * r ^ 3 * v - r ^ 4 * v ^ 2)
/-- `∂_r Γ^r_{tt}`, reduced to the common denominator. -/
theorem Qr_t_tr_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (dr_Gr_tt) (⟨Qr_t_tr_n1, Qr_t_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [dr_Gr_tt, Qr_t_tr_n1, Qr_t_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{tt} Γ^t_{rt}` over the common denominator. -/
def Qr_t_tr_n2 : ZExp 6 := (a ^ 2 + r ^ 2) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x
    ^ 2 + 2 * d * r - r ^ 2 * v) ^ 2
/-- `Γ^r_{tt} Γ^t_{rt}`, reduced to the common denominator. -/
theorem Qr_t_tr_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_tt * Gt_tr) (⟨Qr_t_tr_n2, Qr_t_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_tt, Gt_tr, Qr_t_tr_n2, Qr_t_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{rr} Γ^r_{tt}` over the common denominator. -/
def Qr_t_tr_n3 : ZExp 6 := (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 * v * x ^ 2 - 2 * d * r + r ^ 2 * v) *
    (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^r_{rr} Γ^r_{tt}`, reduced to the common denominator. -/
theorem Qr_t_tr_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_rr * Gr_tt) (⟨Qr_t_tr_n3, Qr_t_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rr, Gr_tt, Qr_t_tr_n3, Qr_t_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{rx} Γ^x_{tt}` over the common denominator. -/
def Qr_t_tr_n4 : ZExp 6 := -4 * a ^ 4 * x ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^
    2 - d + r ^ 2)
/-- `Γ^r_{rx} Γ^x_{tt}`, reduced to the common denominator. -/
theorem Qr_t_tr_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_rx * Gx_tt) (⟨Qr_t_tr_n4, Qr_t_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Gx_tt, Qr_t_tr_n4, Qr_t_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{tp} Γ^p_{rt}` over the common denominator. -/
def Qr_t_tr_n5 : ZExp 6 := a ^ 2 * (x - 1) * (x + 1) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^
    2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v) ^ 2
/-- `Γ^r_{tp} Γ^p_{rt}`, reduced to the common denominator. -/
theorem Qr_t_tr_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_tp * Gp_tr) (⟨Qr_t_tr_n5, Qr_t_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_tp, Gp_tr, Qr_t_tr_n5, Qr_t_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R^r_{ttr}` (`eq:Riemann`): the signed sum of its terms is the reduced fraction. -/
theorem riemann_r_t_tr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨0 - Qr_t_tr_n1 + Qr_t_tr_n2 - Qr_t_tr_n3 - Qr_t_tr_n4 + Qr_t_tr_n5,
          Qr_t_tr_cd⟩) (Qr_t_tr))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Qr_t_tr_n1, Qr_t_tr_n2, Qr_t_tr_n3, Qr_t_tr_n4, Qr_t_tr_n5, Qr_t_tr_cd,
        Qr_t_tr, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R^r_{ttx}` -/

/-- `R^r_{ttx}`, reduced. -/
def Qr_t_tx : Frac 6 := ⟨-3 * a ^ 2 * d * x * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v *
    x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v), 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4⟩

/-- The common denominator of the terms of `R^r_{ttx}`. -/
def Qr_t_tx_cd : ZExp 6 := 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `∂_x Γ^r_{tt}` over the common denominator. -/
def Qr_t_tx_n1 : ZExp 6 := 4 * a ^ 2 * d * x * (a ^ 2 * x ^ 2 + r ^ 2) * (2 * a ^ 2 * r * x ^ 2 - 3
    * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 3 * d * r - r ^ 3 - r ^ 2 * v)
/-- `∂_x Γ^r_{tt}`, reduced to the common denominator. -/
theorem Qr_t_tx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (dx_Gr_tt) (⟨Qr_t_tx_n1, Qr_t_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [dx_Gr_tt, Qr_t_tx_n1, Qr_t_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{tt} Γ^t_{xt}` over the common denominator. -/
def Qr_t_tx_n2 : ZExp 6 := -a ^ 2 * d * x * (a ^ 2 - d + r ^ 2) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^
    2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^r_{tt} Γ^t_{xt}`, reduced to the common denominator. -/
theorem Qr_t_tx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_tt * Gt_tx) (⟨Qr_t_tx_n2, Qr_t_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_tt, Gt_tx, Qr_t_tx_n2, Qr_t_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{xr} Γ^r_{tt}` over the common denominator. -/
def Qr_t_tx_n3 : ZExp 6 := -a ^ 2 * d * x * (a ^ 2 * x ^ 2 + r ^ 2) * (2 * a ^ 2 * r * x ^ 2 - 2 *
    a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^r_{xr} Γ^r_{tt}`, reduced to the common denominator. -/
theorem Qr_t_tx_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_rx * Gr_tt) (⟨Qr_t_tx_n3, Qr_t_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Gr_tt, Qr_t_tx_n3, Qr_t_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{xx} Γ^x_{tt}` over the common denominator. -/
def Qr_t_tx_n4 : ZExp 6 := -2 * a ^ 2 * d * r * x * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 - d + r ^ 2)
/-- `Γ^r_{xx} Γ^x_{tt}`, reduced to the common denominator. -/
theorem Qr_t_tx_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_xx * Gx_tt) (⟨Qr_t_tx_n4, Qr_t_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_xx, Gx_tt, Qr_t_tx_n4, Qr_t_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{tp} Γ^p_{xt}` over the common denominator. -/
def Qr_t_tx_n5 : ZExp 6 := a ^ 2 * d * x * (a ^ 2 - d + r ^ 2) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2
    * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^r_{tp} Γ^p_{xt}`, reduced to the common denominator. -/
theorem Qr_t_tx_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_tp * Gp_tx) (⟨Qr_t_tx_n5, Qr_t_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_tp, Gp_tx, Qr_t_tx_n5, Qr_t_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R^r_{ttx}` (`eq:Riemann`): the signed sum of its terms is the reduced fraction. -/
theorem riemann_r_t_tx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨0 - Qr_t_tx_n1 + Qr_t_tx_n2 - Qr_t_tx_n3 - Qr_t_tx_n4 + Qr_t_tx_n5,
          Qr_t_tx_cd⟩) (Qr_t_tx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Qr_t_tx_n1, Qr_t_tx_n2, Qr_t_tx_n3, Qr_t_tx_n4, Qr_t_tx_n5, Qr_t_tx_cd,
        Qr_t_tx, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R^r_{trp}` -/

/-- `R^r_{trp}`, reduced. -/
def Qr_t_rp : Frac 6 := ⟨a * (x - 1) * (x + 1) * (2 * a ^ 6 * x ^ 2 + a ^ 4 * d * w * x ^ 4 - 2 * a
    ^ 4 * d * x ^ 4 + 6 * a ^ 4 * r ^ 2 * x ^ 2 - 2 * a ^ 4 * r ^ 2 - a ^ 4 * r * v * x ^ 2 - 2 * a
    ^ 2 * d ^ 2 * x ^ 2 + 2 * a ^ 2 * d * r ^ 2 * w * x ^ 2 + 4 * a ^ 2 * d * r ^ 2 * x ^ 2 - 4 * a
    ^ 2 * d * r ^ 2 - 4 * a ^ 2 * d * r * v * x ^ 2 + 4 * a ^ 2 * r ^ 4 * x ^ 2 - 2 * a ^ 2 * r ^ 4
    - a ^ 2 * r ^ 3 * v * x ^ 2 - a ^ 2 * r ^ 3 * v + 6 * d ^ 2 * r ^ 2 + d * r ^ 4 * w + 2 * d * r
    ^ 4 - 4 * d * r ^ 3 * v - r ^ 5 * v), 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4⟩

/-- The common denominator of the terms of `R^r_{trp}`. -/
def Qr_t_rp_cd : ZExp 6 := 4 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `∂_r Γ^r_{pt}` over the common denominator. -/
def Qr_t_rp_n1 : ZExp 6 := -2 * a * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (-a ^ 4 * d * w *
    x ^ 4 + 2 * a ^ 4 * d * x ^ 4 - 2 * a ^ 4 * d * x ^ 2 + 2 * a ^ 4 * r * v * x ^ 4 - 2 * a ^ 4 *
    r * v * x ^ 2 - a ^ 4 * v ^ 2 * x ^ 4 + 2 * a ^ 2 * d ^ 2 * x ^ 2 - 2 * a ^ 2 * d * r ^ 2 * w *
    x ^ 2 - 10 * a ^ 2 * d * r ^ 2 * x ^ 2 + 10 * a ^ 2 * d * r ^ 2 + 8 * a ^ 2 * d * r * v * x ^ 2
    + 2 * a ^ 2 * r ^ 3 * v * x ^ 2 - 2 * a ^ 2 * r ^ 3 * v - 2 * a ^ 2 * r ^ 2 * v ^ 2 * x ^ 2 -
    10 * d ^ 2 * r ^ 2 - d * r ^ 4 * w + 8 * d * r ^ 3 * v - r ^ 4 * v ^ 2)
/-- `∂_r Γ^r_{pt}`, reduced to the common denominator. -/
theorem Qr_t_rp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (dr_Gr_tp) (⟨Qr_t_rp_n1, Qr_t_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [dr_Gr_tp, Qr_t_rp_n1, Qr_t_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{pt} Γ^t_{rt}` over the common denominator. -/
def Qr_t_rp_n2 : ZExp 6 := a * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (2 * a ^ 2 * r * x ^ 2 - 2 * a
    ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v) ^ 2
/-- `Γ^r_{pt} Γ^t_{rt}`, reduced to the common denominator. -/
theorem Qr_t_rp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_tp * Gt_tr) (⟨Qr_t_rp_n2, Qr_t_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_tp, Gt_tr, Qr_t_rp_n2, Qr_t_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{rr} Γ^r_{pt}` over the common denominator. -/
def Qr_t_rp_n3 : ZExp 6 := a * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 * v * x ^ 2 - 2
    * d * r + r ^ 2 * v) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r -
    r ^ 2 * v)
/-- `Γ^r_{rr} Γ^r_{pt}`, reduced to the common denominator. -/
theorem Qr_t_rp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_rr * Gr_tp) (⟨Qr_t_rp_n3, Qr_t_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rr, Gr_tp, Qr_t_rp_n3, Qr_t_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{rx} Γ^x_{pt}` over the common denominator. -/
def Qr_t_rp_n4 : ZExp 6 := 4 * a ^ 3 * x ^ 2 * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2
    + r ^ 2) * (a ^ 2 - d + r ^ 2)
/-- `Γ^r_{rx} Γ^x_{pt}`, reduced to the common denominator. -/
theorem Qr_t_rp_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_rx * Gx_tp) (⟨Qr_t_rp_n4, Qr_t_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Gx_tp, Qr_t_rp_n4, Qr_t_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{pp} Γ^p_{rt}` over the common denominator. -/
def Qr_t_rp_n5 : ZExp 6 := -a * (x - 1) * (x + 1) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2
    * v * x ^ 2 + 2 * d * r - r ^ 2 * v) * (4 * a ^ 4 * r * x ^ 2 - 2 * a ^ 4 * r + a ^ 4 * v * x ^
    4 - a ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d * r * x ^ 2 + 2 * a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 * x ^
    2 + a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 * v + 2 * r ^ 5)
/-- `Γ^r_{pp} Γ^p_{rt}`, reduced to the common denominator. -/
theorem Qr_t_rp_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_pp * Gp_tr) (⟨Qr_t_rp_n5, Qr_t_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_pp, Gp_tr, Qr_t_rp_n5, Qr_t_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R^r_{trp}` (`eq:Riemann`): the signed sum of its terms is the reduced fraction. -/
theorem riemann_r_t_rp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Qr_t_rp_n1 - Qr_t_rp_n2 + Qr_t_rp_n3 + Qr_t_rp_n4 - Qr_t_rp_n5,
          Qr_t_rp_cd⟩) (Qr_t_rp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Qr_t_rp_n1, Qr_t_rp_n2, Qr_t_rp_n3, Qr_t_rp_n4, Qr_t_rp_n5, Qr_t_rp_cd,
        Qr_t_rp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R^r_{txp}` -/

/-- `R^r_{txp}`, reduced. -/
def Qr_t_xp : Frac 6 := ⟨a * d * x * (a ^ 2 * x ^ 2 - 3 * a ^ 2 - 2 * r ^ 2) * (2 * a ^ 2 * r * x ^
    2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v), 2 * (a ^ 2 * x ^ 2
    + r ^ 2) ^ 4⟩

/-- The common denominator of the terms of `R^r_{txp}`. -/
def Qr_t_xp_cd : ZExp 6 := 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `∂_x Γ^r_{pt}` over the common denominator. -/
def Qr_t_xp_n1 : ZExp 6 := 2 * a * d * x * (a ^ 2 * x ^ 2 + r ^ 2) * (2 * a ^ 4 * r * x ^ 4 - 8 * a
    ^ 4 * r * x ^ 2 + 6 * a ^ 4 * r - a ^ 4 * v * x ^ 4 + 2 * a ^ 4 * v * x ^ 2 + 4 * a ^ 2 * d * r
    * x ^ 2 - 6 * a ^ 2 * d * r - 4 * a ^ 2 * r ^ 3 * x ^ 2 + 4 * a ^ 2 * r ^ 3 + 2 * a ^ 2 * r ^ 2
    * v - 2 * d * r ^ 3 + r ^ 4 * v)
/-- `∂_x Γ^r_{pt}`, reduced to the common denominator. -/
theorem Qr_t_xp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (dx_Gr_tp) (⟨Qr_t_xp_n1, Qr_t_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [dx_Gr_tp, Qr_t_xp_n1, Qr_t_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{pt} Γ^t_{xt}` over the common denominator. -/
def Qr_t_xp_n2 : ZExp 6 := -a ^ 3 * d * x * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) * (2 * a ^ 2 *
    r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^r_{pt} Γ^t_{xt}`, reduced to the common denominator. -/
theorem Qr_t_xp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_tp * Gt_tx) (⟨Qr_t_xp_n2, Qr_t_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_tp, Gt_tx, Qr_t_xp_n2, Qr_t_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{xr} Γ^r_{pt}` over the common denominator. -/
def Qr_t_xp_n3 : ZExp 6 := -a ^ 3 * d * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (2 * a ^
    2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^r_{xr} Γ^r_{pt}`, reduced to the common denominator. -/
theorem Qr_t_xp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_rx * Gr_tp) (⟨Qr_t_xp_n3, Qr_t_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Gr_tp, Qr_t_xp_n3, Qr_t_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{xx} Γ^x_{pt}` over the common denominator. -/
def Qr_t_xp_n4 : ZExp 6 := 2 * a * d * r * x * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 -
    d + r ^ 2)
/-- `Γ^r_{xx} Γ^x_{pt}`, reduced to the common denominator. -/
theorem Qr_t_xp_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_xx * Gx_tp) (⟨Qr_t_xp_n4, Qr_t_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_xx, Gx_tp, Qr_t_xp_n4, Qr_t_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{pp} Γ^p_{xt}` over the common denominator. -/
def Qr_t_xp_n5 : ZExp 6 := -a * d * x * (a ^ 2 - d + r ^ 2) * (4 * a ^ 4 * r * x ^ 2 - 2 * a ^ 4 *
    r + a ^ 4 * v * x ^ 4 - a ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d * r * x ^ 2 + 2 * a ^ 2 * d * r + 4 *
    a ^ 2 * r ^ 3 * x ^ 2 + a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 * v + 2 * r ^ 5)
/-- `Γ^r_{pp} Γ^p_{xt}`, reduced to the common denominator. -/
theorem Qr_t_xp_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_pp * Gp_tx) (⟨Qr_t_xp_n5, Qr_t_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_pp, Gp_tx, Qr_t_xp_n5, Qr_t_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R^r_{txp}` (`eq:Riemann`): the signed sum of its terms is the reduced fraction. -/
theorem riemann_r_t_xp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Qr_t_xp_n1 - Qr_t_xp_n2 + Qr_t_xp_n3 + Qr_t_xp_n4 - Qr_t_xp_n5,
          Qr_t_xp_cd⟩) (Qr_t_xp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Qr_t_xp_n1, Qr_t_xp_n2, Qr_t_xp_n3, Qr_t_xp_n4, Qr_t_xp_n5, Qr_t_xp_cd,
        Qr_t_xp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R^r_{rtp}` -/

/-- The common denominator of the terms of `R^r_{rtp}`. -/
def Qr_r_tp_cd : ZExp 6 := 4 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `Γ^r_{tt} Γ^t_{pr}` over the common denominator. -/
def Qr_r_tp_n1 : ZExp 6 := -a * (x - 1) * (x + 1) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2
    * v * x ^ 2 + 2 * d * r - r ^ 2 * v) * (2 * a ^ 4 * r + a ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d * r *
    x ^ 2 - 2 * a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 + a ^ 2 * r ^ 2 * v * x ^ 2 + a ^ 2 * r ^ 2 * v -
    4 * d * r ^ 3 + 2 * r ^ 5 + r ^ 4 * v)
/-- `Γ^r_{tt} Γ^t_{pr}`, reduced to the common denominator. -/
theorem Qr_r_tp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_tt * Gt_rp) (⟨Qr_r_tp_n1, Qr_r_tp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_tt, Gt_rp, Qr_r_tp_n1, Qr_r_tp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{pt} Γ^t_{tr}` over the common denominator. -/
def Qr_r_tp_n2 : ZExp 6 := a * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (2 * a ^ 2 * r * x ^ 2 - 2 * a
    ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v) ^ 2
/-- `Γ^r_{pt} Γ^t_{tr}`, reduced to the common denominator. -/
theorem Qr_r_tp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_tp * Gt_tr) (⟨Qr_r_tp_n2, Qr_r_tp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_tp, Gt_tr, Qr_r_tp_n2, Qr_r_tp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{tp} Γ^p_{pr}` over the common denominator. -/
def Qr_r_tp_n3 : ZExp 6 := -a * (x - 1) * (x + 1) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2
    * v * x ^ 2 + 2 * d * r - r ^ 2 * v) * (2 * a ^ 4 * r * x ^ 2 - 2 * a ^ 4 * r + a ^ 4 * v * x ^
    4 - a ^ 4 * v * x ^ 2 + 2 * a ^ 2 * d * r + 2 * a ^ 2 * r ^ 3 * x ^ 2 - 2 * a ^ 2 * r ^ 3 + a ^
    2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 * v + 2 * d * r ^ 3)
/-- `Γ^r_{tp} Γ^p_{pr}`, reduced to the common denominator. -/
theorem Qr_r_tp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_tp * Gp_rp) (⟨Qr_r_tp_n3, Qr_r_tp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_tp, Gp_rp, Qr_r_tp_n3, Qr_r_tp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{pp} Γ^p_{tr}` over the common denominator. -/
def Qr_r_tp_n4 : ZExp 6 := -a * (x - 1) * (x + 1) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2
    * v * x ^ 2 + 2 * d * r - r ^ 2 * v) * (4 * a ^ 4 * r * x ^ 2 - 2 * a ^ 4 * r + a ^ 4 * v * x ^
    4 - a ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d * r * x ^ 2 + 2 * a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 * x ^
    2 + a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 * v + 2 * r ^ 5)
/-- `Γ^r_{pp} Γ^p_{tr}`, reduced to the common denominator. -/
theorem Qr_r_tp_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_pp * Gp_tr) (⟨Qr_r_tp_n4, Qr_r_tp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_pp, Gp_tr, Qr_r_tp_n4, Qr_r_tp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R^r_{rtp}` (`eq:Riemann`): the signed sum of its terms is `0`. -/
theorem riemann_r_r_tp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Qr_r_tp_n1 - Qr_r_tp_n2 + Qr_r_tp_n3 - Qr_r_tp_n4, Qr_r_tp_cd⟩) (Frac.ofZ
          0))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Qr_r_tp_n1, Qr_r_tp_n2, Qr_r_tp_n3, Qr_r_tp_n4, Qr_r_tp_cd, δr_0, δr_1, δr_2,
        δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R^r_{rrx}` -/

/-- The common denominator of the terms of `R^r_{rrx}`. -/
def Qr_r_rx_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2

/-- The numerator of `∂_r Γ^r_{xr}` over the common denominator. -/
def Qr_r_rx_n1 : ZExp 6 := -4 * a ^ 2 * d * r * x
/-- `∂_r Γ^r_{xr}`, reduced to the common denominator. -/
theorem Qr_r_rx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (dr_Gr_rx) (⟨Qr_r_rx_n1, Qr_r_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [dr_Gr_rx, Qr_r_rx_n1, Qr_r_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `∂_x Γ^r_{rr}` over the common denominator. -/
def Qr_r_rx_n2 : ZExp 6 := -4 * a ^ 2 * d * r * x
/-- `∂_x Γ^r_{rr}`, reduced to the common denominator. -/
theorem Qr_r_rx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (dx_Gr_rr) (⟨Qr_r_rx_n2, Qr_r_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [dx_Gr_rr, Qr_r_rx_n2, Qr_r_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{rr} Γ^r_{xr}` over the common denominator. -/
def Qr_r_rx_n3 : ZExp 6 := -a ^ 2 * x * (a ^ 2 * v * x ^ 2 - 2 * d * r + r ^ 2 * v)
/-- `Γ^r_{rr} Γ^r_{xr}`, reduced to the common denominator. -/
theorem Qr_r_rx_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_rr * Gr_rx) (⟨Qr_r_rx_n3, Qr_r_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rr, Gr_rx, Qr_r_rx_n3, Qr_r_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{xr} Γ^r_{rr}` over the common denominator. -/
def Qr_r_rx_n4 : ZExp 6 := -a ^ 2 * x * (a ^ 2 * v * x ^ 2 - 2 * d * r + r ^ 2 * v)
/-- `Γ^r_{xr} Γ^r_{rr}`, reduced to the common denominator. -/
theorem Qr_r_rx_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_rx * Gr_rr) (⟨Qr_r_rx_n4, Qr_r_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Gr_rr, Qr_r_rx_n4, Qr_r_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{rx} Γ^x_{xr}` over the common denominator. -/
def Qr_r_rx_n5 : ZExp 6 := 2 * a ^ 2 * d * r * x
/-- `Γ^r_{rx} Γ^x_{xr}`, reduced to the common denominator. -/
theorem Qr_r_rx_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_rx * Gx_rx) (⟨Qr_r_rx_n5, Qr_r_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Gx_rx, Qr_r_rx_n5, Qr_r_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{xx} Γ^x_{rr}` over the common denominator. -/
def Qr_r_rx_n6 : ZExp 6 := 2 * a ^ 2 * d * r * x
/-- `Γ^r_{xx} Γ^x_{rr}`, reduced to the common denominator. -/
theorem Qr_r_rx_t6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_xx * Gx_rr) (⟨Qr_r_rx_n6, Qr_r_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_xx, Gx_rr, Qr_r_rx_n6, Qr_r_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R^r_{rrx}` (`eq:Riemann`): the signed sum of its terms is `0`. -/
theorem riemann_r_r_rx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Qr_r_rx_n1 - Qr_r_rx_n2 + Qr_r_rx_n3 - Qr_r_rx_n4 + Qr_r_rx_n5 -
          Qr_r_rx_n6, Qr_r_rx_cd⟩) (Frac.ofZ 0))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Qr_r_rx_n1, Qr_r_rx_n2, Qr_r_rx_n3, Qr_r_rx_n4, Qr_r_rx_n5, Qr_r_rx_n6,
        Qr_r_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R^r_{xtp}` -/

/-- `R^r_{xtp}`, reduced. -/
def Qr_x_tp : Frac 6 := ⟨-a * d * x * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 +
    4 * d * r - 2 * r ^ 3 - r ^ 2 * v), 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `R^r_{xtp}`. -/
def Qr_x_tp_cd : ZExp 6 := 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `Γ^r_{tt} Γ^t_{px}` over the common denominator. -/
def Qr_x_tp_n1 : ZExp 6 := -a ^ 3 * d * x * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) * (2 * a ^ 2 *
    r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^r_{tt} Γ^t_{px}`, reduced to the common denominator. -/
theorem Qr_x_tp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_tt * Gt_xp) (⟨Qr_x_tp_n1, Qr_x_tp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_tt, Gt_xp, Qr_x_tp_n1, Qr_x_tp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{pt} Γ^t_{tx}` over the common denominator. -/
def Qr_x_tp_n2 : ZExp 6 := -a ^ 3 * d * x * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) * (2 * a ^ 2 *
    r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^r_{pt} Γ^t_{tx}`, reduced to the common denominator. -/
theorem Qr_x_tp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_tp * Gt_tx) (⟨Qr_x_tp_n2, Qr_x_tp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_tp, Gt_tx, Qr_x_tp_n2, Qr_x_tp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{tp} Γ^p_{px}` over the common denominator. -/
def Qr_x_tp_n3 : ZExp 6 := -a * d * x * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2
    + 2 * d * r - r ^ 2 * v) * (a ^ 4 * x ^ 4 - a ^ 4 * x ^ 2 + a ^ 4 + a ^ 2 * d * x ^ 2 - a ^ 2 *
    d + a ^ 2 * r ^ 2 * x ^ 2 + a ^ 2 * r ^ 2 + r ^ 4)
/-- `Γ^r_{tp} Γ^p_{px}`, reduced to the common denominator. -/
theorem Qr_x_tp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_tp * Gp_xp) (⟨Qr_x_tp_n3, Qr_x_tp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_tp, Gp_xp, Qr_x_tp_n3, Qr_x_tp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{pp} Γ^p_{tx}` over the common denominator. -/
def Qr_x_tp_n4 : ZExp 6 := -a * d * x * (a ^ 2 - d + r ^ 2) * (4 * a ^ 4 * r * x ^ 2 - 2 * a ^ 4 *
    r + a ^ 4 * v * x ^ 4 - a ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d * r * x ^ 2 + 2 * a ^ 2 * d * r + 4 *
    a ^ 2 * r ^ 3 * x ^ 2 + a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 * v + 2 * r ^ 5)
/-- `Γ^r_{pp} Γ^p_{tx}`, reduced to the common denominator. -/
theorem Qr_x_tp_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_pp * Gp_tx) (⟨Qr_x_tp_n4, Qr_x_tp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_pp, Gp_tx, Qr_x_tp_n4, Qr_x_tp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R^r_{xtp}` (`eq:Riemann`): the signed sum of its terms is the reduced fraction. -/
theorem riemann_r_x_tp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Qr_x_tp_n1 - Qr_x_tp_n2 + Qr_x_tp_n3 - Qr_x_tp_n4, Qr_x_tp_cd⟩)
          (Qr_x_tp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Qr_x_tp_n1, Qr_x_tp_n2, Qr_x_tp_n3, Qr_x_tp_n4, Qr_x_tp_cd, Qr_x_tp, δr_0,
        δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R^r_{xrx}` -/

/-- `R^r_{xrx}`, reduced. -/
def Qr_x_rx : Frac 6 := ⟨-2 * a ^ 4 * x ^ 2 + 2 * a ^ 2 * d * x ^ 2 - 4 * a ^ 2 * r ^ 2 * x ^ 2 + 2
    * a ^ 2 * r ^ 2 + a ^ 2 * r * v * x ^ 2 - 2 * d * r ^ 2 + r ^ 3 * v, 2 * (x - 1) * (x + 1) * (a
    ^ 2 * x ^ 2 + r ^ 2) ^ 2⟩

/-- The common denominator of the terms of `R^r_{xrx}`. -/
def Qr_x_rx_cd : ZExp 6 := 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2

/-- The numerator of `∂_r Γ^r_{xx}` over the common denominator. -/
def Qr_x_rx_n1 : ZExp 6 := 2 * (a ^ 2 * d * x ^ 2 + a ^ 2 * r * v * x ^ 2 - d * r ^ 2 + r ^ 3 * v)
/-- `∂_r Γ^r_{xx}`, reduced to the common denominator. -/
theorem Qr_x_rx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (dr_Gr_xx) (⟨Qr_x_rx_n1, Qr_x_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [dr_Gr_xx, Qr_x_rx_n1, Qr_x_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `∂_x Γ^r_{rx}` over the common denominator. -/
def Qr_x_rx_n2 : ZExp 6 := -2 * a ^ 2 * (x - 1) * (x + 1) * (a * x - r) * (a * x + r)
/-- `∂_x Γ^r_{rx}`, reduced to the common denominator. -/
theorem Qr_x_rx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (dx_Gr_rx) (⟨Qr_x_rx_n2, Qr_x_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [dx_Gr_rx, Qr_x_rx_n2, Qr_x_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{rr} Γ^r_{xx}` over the common denominator. -/
def Qr_x_rx_n3 : ZExp 6 := -r * (a ^ 2 * v * x ^ 2 - 2 * d * r + r ^ 2 * v)
/-- `Γ^r_{rr} Γ^r_{xx}`, reduced to the common denominator. -/
theorem Qr_x_rx_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_rr * Gr_xx) (⟨Qr_x_rx_n3, Qr_x_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rr, Gr_xx, Qr_x_rx_n3, Qr_x_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{xr} Γ^r_{rx}` over the common denominator. -/
def Qr_x_rx_n4 : ZExp 6 := 2 * a ^ 4 * x ^ 2 * (x - 1) * (x + 1)
/-- `Γ^r_{xr} Γ^r_{rx}`, reduced to the common denominator. -/
theorem Qr_x_rx_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_rx * Gr_rx) (⟨Qr_x_rx_n4, Qr_x_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Qr_x_rx_n4, Qr_x_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1,
        δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{rx} Γ^x_{xx}` over the common denominator. -/
def Qr_x_rx_n5 : ZExp 6 := -2 * a ^ 2 * x ^ 2 * (a ^ 2 + r ^ 2)
/-- `Γ^r_{rx} Γ^x_{xx}`, reduced to the common denominator. -/
theorem Qr_x_rx_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_rx * Gx_xx) (⟨Qr_x_rx_n5, Qr_x_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Gx_xx, Qr_x_rx_n5, Qr_x_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{xx} Γ^x_{rx}` over the common denominator. -/
def Qr_x_rx_n6 : ZExp 6 := 2 * d * r ^ 2
/-- `Γ^r_{xx} Γ^x_{rx}`, reduced to the common denominator. -/
theorem Qr_x_rx_t6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_xx * Gx_rx) (⟨Qr_x_rx_n6, Qr_x_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_xx, Gx_rx, Qr_x_rx_n6, Qr_x_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R^r_{xrx}` (`eq:Riemann`): the signed sum of its terms is the reduced fraction. -/
theorem riemann_r_x_rx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Qr_x_rx_n1 - Qr_x_rx_n2 + Qr_x_rx_n3 - Qr_x_rx_n4 + Qr_x_rx_n5 -
          Qr_x_rx_n6, Qr_x_rx_cd⟩) (Qr_x_rx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Qr_x_rx_n1, Qr_x_rx_n2, Qr_x_rx_n3, Qr_x_rx_n4, Qr_x_rx_n5, Qr_x_rx_n6,
        Qr_x_rx_cd, Qr_x_rx, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R^r_{ptr}` -/

/-- `R^r_{ptr}`, reduced. -/
def Qr_p_tr : Frac 6 := ⟨-a * (x - 1) * (x + 1) * (2 * a ^ 6 * x ^ 2 + a ^ 4 * d * w * x ^ 4 - 2 *
    a ^ 4 * d * x ^ 4 + 6 * a ^ 4 * r ^ 2 * x ^ 2 - 2 * a ^ 4 * r ^ 2 - a ^ 4 * r * v * x ^ 2 - 2 *
    a ^ 2 * d ^ 2 * x ^ 2 + 2 * a ^ 2 * d * r ^ 2 * w * x ^ 2 + 4 * a ^ 2 * d * r ^ 2 * x ^ 2 - 4 *
    a ^ 2 * d * r ^ 2 - 4 * a ^ 2 * d * r * v * x ^ 2 + 4 * a ^ 2 * r ^ 4 * x ^ 2 - 2 * a ^ 2 * r ^
    4 - a ^ 2 * r ^ 3 * v * x ^ 2 - a ^ 2 * r ^ 3 * v + 6 * d ^ 2 * r ^ 2 + d * r ^ 4 * w + 2 * d *
    r ^ 4 - 4 * d * r ^ 3 * v - r ^ 5 * v), 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4⟩

/-- The common denominator of the terms of `R^r_{ptr}`. -/
def Qr_p_tr_cd : ZExp 6 := 4 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `∂_r Γ^r_{tp}` over the common denominator. -/
def Qr_p_tr_n1 : ZExp 6 := -2 * a * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (-a ^ 4 * d * w *
    x ^ 4 + 2 * a ^ 4 * d * x ^ 4 - 2 * a ^ 4 * d * x ^ 2 + 2 * a ^ 4 * r * v * x ^ 4 - 2 * a ^ 4 *
    r * v * x ^ 2 - a ^ 4 * v ^ 2 * x ^ 4 + 2 * a ^ 2 * d ^ 2 * x ^ 2 - 2 * a ^ 2 * d * r ^ 2 * w *
    x ^ 2 - 10 * a ^ 2 * d * r ^ 2 * x ^ 2 + 10 * a ^ 2 * d * r ^ 2 + 8 * a ^ 2 * d * r * v * x ^ 2
    + 2 * a ^ 2 * r ^ 3 * v * x ^ 2 - 2 * a ^ 2 * r ^ 3 * v - 2 * a ^ 2 * r ^ 2 * v ^ 2 * x ^ 2 -
    10 * d ^ 2 * r ^ 2 - d * r ^ 4 * w + 8 * d * r ^ 3 * v - r ^ 4 * v ^ 2)
/-- `∂_r Γ^r_{tp}`, reduced to the common denominator. -/
theorem Qr_p_tr_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (dr_Gr_tp) (⟨Qr_p_tr_n1, Qr_p_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [dr_Gr_tp, Qr_p_tr_n1, Qr_p_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{tt} Γ^t_{rp}` over the common denominator. -/
def Qr_p_tr_n2 : ZExp 6 := -a * (x - 1) * (x + 1) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2
    * v * x ^ 2 + 2 * d * r - r ^ 2 * v) * (2 * a ^ 4 * r + a ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d * r *
    x ^ 2 - 2 * a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 + a ^ 2 * r ^ 2 * v * x ^ 2 + a ^ 2 * r ^ 2 * v -
    4 * d * r ^ 3 + 2 * r ^ 5 + r ^ 4 * v)
/-- `Γ^r_{tt} Γ^t_{rp}`, reduced to the common denominator. -/
theorem Qr_p_tr_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_tt * Gt_rp) (⟨Qr_p_tr_n2, Qr_p_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_tt, Gt_rp, Qr_p_tr_n2, Qr_p_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{rr} Γ^r_{tp}` over the common denominator. -/
def Qr_p_tr_n3 : ZExp 6 := a * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 * v * x ^ 2 - 2
    * d * r + r ^ 2 * v) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r -
    r ^ 2 * v)
/-- `Γ^r_{rr} Γ^r_{tp}`, reduced to the common denominator. -/
theorem Qr_p_tr_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_rr * Gr_tp) (⟨Qr_p_tr_n3, Qr_p_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rr, Gr_tp, Qr_p_tr_n3, Qr_p_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{rx} Γ^x_{tp}` over the common denominator. -/
def Qr_p_tr_n4 : ZExp 6 := 4 * a ^ 3 * x ^ 2 * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2
    + r ^ 2) * (a ^ 2 - d + r ^ 2)
/-- `Γ^r_{rx} Γ^x_{tp}`, reduced to the common denominator. -/
theorem Qr_p_tr_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_rx * Gx_tp) (⟨Qr_p_tr_n4, Qr_p_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Gx_tp, Qr_p_tr_n4, Qr_p_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{tp} Γ^p_{rp}` over the common denominator. -/
def Qr_p_tr_n5 : ZExp 6 := -a * (x - 1) * (x + 1) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2
    * v * x ^ 2 + 2 * d * r - r ^ 2 * v) * (2 * a ^ 4 * r * x ^ 2 - 2 * a ^ 4 * r + a ^ 4 * v * x ^
    4 - a ^ 4 * v * x ^ 2 + 2 * a ^ 2 * d * r + 2 * a ^ 2 * r ^ 3 * x ^ 2 - 2 * a ^ 2 * r ^ 3 + a ^
    2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 * v + 2 * d * r ^ 3)
/-- `Γ^r_{tp} Γ^p_{rp}`, reduced to the common denominator. -/
theorem Qr_p_tr_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_tp * Gp_rp) (⟨Qr_p_tr_n5, Qr_p_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_tp, Gp_rp, Qr_p_tr_n5, Qr_p_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R^r_{ptr}` (`eq:Riemann`): the signed sum of its terms is the reduced fraction. -/
theorem riemann_r_p_tr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨0 - Qr_p_tr_n1 + Qr_p_tr_n2 - Qr_p_tr_n3 - Qr_p_tr_n4 + Qr_p_tr_n5,
          Qr_p_tr_cd⟩) (Qr_p_tr))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Qr_p_tr_n1, Qr_p_tr_n2, Qr_p_tr_n3, Qr_p_tr_n4, Qr_p_tr_n5, Qr_p_tr_cd,
        Qr_p_tr, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R^r_{ptx}` -/

/-- `R^r_{ptx}`, reduced. -/
def Qr_p_tx : Frac 6 := ⟨-a * d * x * (2 * a ^ 2 * x ^ 2 - 3 * a ^ 2 - r ^ 2) * (2 * a ^ 2 * r * x
    ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v), 2 * (a ^ 2 * x ^
    2 + r ^ 2) ^ 4⟩

/-- The common denominator of the terms of `R^r_{ptx}`. -/
def Qr_p_tx_cd : ZExp 6 := 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `∂_x Γ^r_{tp}` over the common denominator. -/
def Qr_p_tx_n1 : ZExp 6 := 2 * a * d * x * (a ^ 2 * x ^ 2 + r ^ 2) * (2 * a ^ 4 * r * x ^ 4 - 8 * a
    ^ 4 * r * x ^ 2 + 6 * a ^ 4 * r - a ^ 4 * v * x ^ 4 + 2 * a ^ 4 * v * x ^ 2 + 4 * a ^ 2 * d * r
    * x ^ 2 - 6 * a ^ 2 * d * r - 4 * a ^ 2 * r ^ 3 * x ^ 2 + 4 * a ^ 2 * r ^ 3 + 2 * a ^ 2 * r ^ 2
    * v - 2 * d * r ^ 3 + r ^ 4 * v)
/-- `∂_x Γ^r_{tp}`, reduced to the common denominator. -/
theorem Qr_p_tx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (dx_Gr_tp) (⟨Qr_p_tx_n1, Qr_p_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [dx_Gr_tp, Qr_p_tx_n1, Qr_p_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{tt} Γ^t_{xp}` over the common denominator. -/
def Qr_p_tx_n2 : ZExp 6 := -a ^ 3 * d * x * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) * (2 * a ^ 2 *
    r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^r_{tt} Γ^t_{xp}`, reduced to the common denominator. -/
theorem Qr_p_tx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_tt * Gt_xp) (⟨Qr_p_tx_n2, Qr_p_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_tt, Gt_xp, Qr_p_tx_n2, Qr_p_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{xr} Γ^r_{tp}` over the common denominator. -/
def Qr_p_tx_n3 : ZExp 6 := -a ^ 3 * d * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (2 * a ^
    2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^r_{xr} Γ^r_{tp}`, reduced to the common denominator. -/
theorem Qr_p_tx_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_rx * Gr_tp) (⟨Qr_p_tx_n3, Qr_p_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Gr_tp, Qr_p_tx_n3, Qr_p_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{xx} Γ^x_{tp}` over the common denominator. -/
def Qr_p_tx_n4 : ZExp 6 := 2 * a * d * r * x * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 -
    d + r ^ 2)
/-- `Γ^r_{xx} Γ^x_{tp}`, reduced to the common denominator. -/
theorem Qr_p_tx_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_xx * Gx_tp) (⟨Qr_p_tx_n4, Qr_p_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_xx, Gx_tp, Qr_p_tx_n4, Qr_p_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{tp} Γ^p_{xp}` over the common denominator. -/
def Qr_p_tx_n5 : ZExp 6 := -a * d * x * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2
    + 2 * d * r - r ^ 2 * v) * (a ^ 4 * x ^ 4 - a ^ 4 * x ^ 2 + a ^ 4 + a ^ 2 * d * x ^ 2 - a ^ 2 *
    d + a ^ 2 * r ^ 2 * x ^ 2 + a ^ 2 * r ^ 2 + r ^ 4)
/-- `Γ^r_{tp} Γ^p_{xp}`, reduced to the common denominator. -/
theorem Qr_p_tx_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_tp * Gp_xp) (⟨Qr_p_tx_n5, Qr_p_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_tp, Gp_xp, Qr_p_tx_n5, Qr_p_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R^r_{ptx}` (`eq:Riemann`): the signed sum of its terms is the reduced fraction. -/
theorem riemann_r_p_tx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨0 - Qr_p_tx_n1 + Qr_p_tx_n2 - Qr_p_tx_n3 - Qr_p_tx_n4 + Qr_p_tx_n5,
          Qr_p_tx_cd⟩) (Qr_p_tx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Qr_p_tx_n1, Qr_p_tx_n2, Qr_p_tx_n3, Qr_p_tx_n4, Qr_p_tx_n5, Qr_p_tx_cd,
        Qr_p_tx, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R^r_{prp}` -/

/-- `R^r_{prp}`, reduced. -/
def Qr_p_rp : Frac 6 := ⟨(x - 1) * (x + 1) * (-2 * a ^ 8 * x ^ 2 + a ^ 6 * d * w * x ^ 6 - a ^ 6 *
    d * w * x ^ 4 - 2 * a ^ 6 * d * x ^ 6 + 4 * a ^ 6 * d * x ^ 4 - 8 * a ^ 6 * r ^ 2 * x ^ 2 + 2 *
    a ^ 6 * r ^ 2 + a ^ 6 * r * v * x ^ 2 - 2 * a ^ 4 * d ^ 2 * x ^ 4 + 2 * a ^ 4 * d ^ 2 * x ^ 2 +
    2 * a ^ 4 * d * r ^ 2 * w * x ^ 4 - 2 * a ^ 4 * d * r ^ 2 * w * x ^ 2 + 6 * a ^ 4 * d * r ^ 2 *
    x ^ 4 - 8 * a ^ 4 * d * r ^ 2 * x ^ 2 + 4 * a ^ 4 * d * r ^ 2 - 4 * a ^ 4 * d * r * v * x ^ 4 +
    4 * a ^ 4 * d * r * v * x ^ 2 - 10 * a ^ 4 * r ^ 4 * x ^ 2 + 4 * a ^ 4 * r ^ 4 + 2 * a ^ 4 * r
    ^ 3 * v * x ^ 2 + a ^ 4 * r ^ 3 * v + 6 * a ^ 2 * d ^ 2 * r ^ 2 * x ^ 2 - 6 * a ^ 2 * d ^ 2 * r
    ^ 2 + a ^ 2 * d * r ^ 4 * w * x ^ 2 - a ^ 2 * d * r ^ 4 * w + 2 * a ^ 2 * d * r ^ 4 * x ^ 2 - 4
    * a ^ 2 * d * r ^ 4 - 4 * a ^ 2 * d * r ^ 3 * v * x ^ 2 + 4 * a ^ 2 * d * r ^ 3 * v - 4 * a ^ 2
    * r ^ 6 * x ^ 2 + 2 * a ^ 2 * r ^ 6 + a ^ 2 * r ^ 5 * v * x ^ 2 + 2 * a ^ 2 * r ^ 5 * v - 2 * d
    * r ^ 6 + r ^ 7 * v), 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4⟩

/-- The common denominator of the terms of `R^r_{prp}`. -/
def Qr_p_rp_cd : ZExp 6 := 4 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `∂_r Γ^r_{pp}` over the common denominator. -/
def Qr_p_rp_n1 : ZExp 6 := 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 6 * d * w * x ^ 6
    - a ^ 6 * d * w * x ^ 4 + 4 * a ^ 6 * d * x ^ 4 - 2 * a ^ 6 * d * x ^ 2 + 4 * a ^ 6 * r * v * x
    ^ 4 - 2 * a ^ 6 * r * v * x ^ 2 + a ^ 6 * v ^ 2 * x ^ 6 - a ^ 6 * v ^ 2 * x ^ 4 - 2 * a ^ 4 * d
    ^ 2 * x ^ 4 + 2 * a ^ 4 * d ^ 2 * x ^ 2 + 2 * a ^ 4 * d * r ^ 2 * w * x ^ 4 - 2 * a ^ 4 * d * r
    ^ 2 * w * x ^ 2 + 12 * a ^ 4 * d * r ^ 2 * x ^ 4 - 20 * a ^ 4 * d * r ^ 2 * x ^ 2 + 10 * a ^ 4
    * d * r ^ 2 - 8 * a ^ 4 * d * r * v * x ^ 4 + 8 * a ^ 4 * d * r * v * x ^ 2 + 4 * a ^ 4 * r ^ 3
    * v * x ^ 4 + 4 * a ^ 4 * r ^ 3 * v * x ^ 2 - 2 * a ^ 4 * r ^ 3 * v + 2 * a ^ 4 * r ^ 2 * v ^ 2
    * x ^ 4 - 2 * a ^ 4 * r ^ 2 * v ^ 2 * x ^ 2 + 10 * a ^ 2 * d ^ 2 * r ^ 2 * x ^ 2 - 10 * a ^ 2 *
    d ^ 2 * r ^ 2 + a ^ 2 * d * r ^ 4 * w * x ^ 2 - a ^ 2 * d * r ^ 4 * w - 2 * a ^ 2 * d * r ^ 4 *
    x ^ 2 - 8 * a ^ 2 * d * r ^ 3 * v * x ^ 2 + 8 * a ^ 2 * d * r ^ 3 * v + 6 * a ^ 2 * r ^ 5 * v *
    x ^ 2 + a ^ 2 * r ^ 4 * v ^ 2 * x ^ 2 - a ^ 2 * r ^ 4 * v ^ 2 - 2 * d * r ^ 6 + 2 * r ^ 7 * v)
/-- `∂_r Γ^r_{pp}`, reduced to the common denominator. -/
theorem Qr_p_rp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (dr_Gr_pp) (⟨Qr_p_rp_n1, Qr_p_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [dr_Gr_pp, Qr_p_rp_n1, Qr_p_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{pt} Γ^t_{rp}` over the common denominator. -/
def Qr_p_rp_n2 : ZExp 6 := -a ^ 2 * (x - 1) ^ 2 * (x + 1) ^ 2 * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2
    * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v) * (2 * a ^ 4 * r + a ^ 4 * v * x ^ 2 - 2 * a ^
    2 * d * r * x ^ 2 - 2 * a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 + a ^ 2 * r ^ 2 * v * x ^ 2 + a ^ 2 *
    r ^ 2 * v - 4 * d * r ^ 3 + 2 * r ^ 5 + r ^ 4 * v)
/-- `Γ^r_{pt} Γ^t_{rp}`, reduced to the common denominator. -/
theorem Qr_p_rp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_tp * Gt_rp) (⟨Qr_p_rp_n2, Qr_p_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_tp, Gt_rp, Qr_p_rp_n2, Qr_p_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{rr} Γ^r_{pp}` over the common denominator. -/
def Qr_p_rp_n3 : ZExp 6 := -(x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 * v * x ^ 2 - 2 *
    d * r + r ^ 2 * v) * (4 * a ^ 4 * r * x ^ 2 - 2 * a ^ 4 * r + a ^ 4 * v * x ^ 4 - a ^ 4 * v * x
    ^ 2 - 2 * a ^ 2 * d * r * x ^ 2 + 2 * a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 * x ^ 2 + a ^ 2 * r ^ 2
    * v * x ^ 2 - a ^ 2 * r ^ 2 * v + 2 * r ^ 5)
/-- `Γ^r_{rr} Γ^r_{pp}`, reduced to the common denominator. -/
theorem Qr_p_rp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_rr * Gr_pp) (⟨Qr_p_rp_n3, Qr_p_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rr, Gr_pp, Qr_p_rp_n3, Qr_p_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{rx} Γ^x_{pp}` over the common denominator. -/
def Qr_p_rp_n4 : ZExp 6 := -4 * a ^ 2 * x ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^
    6 + a ^ 4 * d * x ^ 4 - a ^ 4 * d + 3 * a ^ 4 * r ^ 2 + 2 * a ^ 2 * d * r ^ 2 * x ^ 2 - 2 * a ^
    2 * d * r ^ 2 + 3 * a ^ 2 * r ^ 4 + r ^ 6)
/-- `Γ^r_{rx} Γ^x_{pp}`, reduced to the common denominator. -/
theorem Qr_p_rp_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_rx * Gx_pp) (⟨Qr_p_rp_n4, Qr_p_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Gx_pp, Qr_p_rp_n4, Qr_p_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{pp} Γ^p_{rp}` over the common denominator. -/
def Qr_p_rp_n5 : ZExp 6 := (x - 1) * (x + 1) * (2 * a ^ 4 * r * x ^ 2 - 2 * a ^ 4 * r + a ^ 4 * v *
    x ^ 4 - a ^ 4 * v * x ^ 2 + 2 * a ^ 2 * d * r + 2 * a ^ 2 * r ^ 3 * x ^ 2 - 2 * a ^ 2 * r ^ 3 +
    a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 * v + 2 * d * r ^ 3) * (4 * a ^ 4 * r * x ^ 2 - 2 * a
    ^ 4 * r + a ^ 4 * v * x ^ 4 - a ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d * r * x ^ 2 + 2 * a ^ 2 * d * r
    + 4 * a ^ 2 * r ^ 3 * x ^ 2 + a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 * v + 2 * r ^ 5)
/-- `Γ^r_{pp} Γ^p_{rp}`, reduced to the common denominator. -/
theorem Qr_p_rp_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_pp * Gp_rp) (⟨Qr_p_rp_n5, Qr_p_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_pp, Gp_rp, Qr_p_rp_n5, Qr_p_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R^r_{prp}` (`eq:Riemann`): the signed sum of its terms is the reduced fraction. -/
theorem riemann_r_p_rp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Qr_p_rp_n1 - Qr_p_rp_n2 + Qr_p_rp_n3 + Qr_p_rp_n4 - Qr_p_rp_n5,
          Qr_p_rp_cd⟩) (Qr_p_rp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Qr_p_rp_n1, Qr_p_rp_n2, Qr_p_rp_n3, Qr_p_rp_n4, Qr_p_rp_n5, Qr_p_rp_cd,
        Qr_p_rp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R^r_{pxp}` -/

/-- `R^r_{pxp}`, reduced. -/
def Qr_p_xp : Frac 6 := ⟨-3 * a ^ 2 * d * x * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (2 * a ^ 2 * r
    * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v), 2 * (a ^ 2 *
    x ^ 2 + r ^ 2) ^ 4⟩

/-- The common denominator of the terms of `R^r_{pxp}`. -/
def Qr_p_xp_cd : ZExp 6 := 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `∂_x Γ^r_{pp}` over the common denominator. -/
def Qr_p_xp_n1 : ZExp 6 := -4 * d * x * (a ^ 2 * x ^ 2 + r ^ 2) * (2 * a ^ 6 * r * x ^ 4 - 6 * a ^
    6 * r * x ^ 2 + 3 * a ^ 6 * r - a ^ 6 * v * x ^ 4 + a ^ 6 * v * x ^ 2 - a ^ 4 * d * r * x ^ 4 +
    4 * a ^ 4 * d * r * x ^ 2 - 3 * a ^ 4 * d * r + 2 * a ^ 4 * r ^ 3 * x ^ 4 - 8 * a ^ 4 * r ^ 3 *
    x ^ 2 + 3 * a ^ 4 * r ^ 3 - a ^ 4 * r ^ 2 * v * x ^ 4 + a ^ 4 * r ^ 2 * v + 2 * a ^ 2 * d * r ^
    3 * x ^ 2 - 2 * a ^ 2 * d * r ^ 3 - 2 * a ^ 2 * r ^ 5 * x ^ 2 - a ^ 2 * r ^ 5 - a ^ 2 * r ^ 4 *
    v * x ^ 2 + a ^ 2 * r ^ 4 * v - r ^ 7)
/-- `∂_x Γ^r_{pp}`, reduced to the common denominator. -/
theorem Qr_p_xp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (dx_Gr_pp) (⟨Qr_p_xp_n1, Qr_p_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [dx_Gr_pp, Qr_p_xp_n1, Qr_p_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{pt} Γ^t_{xp}` over the common denominator. -/
def Qr_p_xp_n2 : ZExp 6 := -a ^ 4 * d * x * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 - d + r ^ 2) * (2 *
    a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^r_{pt} Γ^t_{xp}`, reduced to the common denominator. -/
theorem Qr_p_xp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_tp * Gt_xp) (⟨Qr_p_xp_n2, Qr_p_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_tp, Gt_xp, Qr_p_xp_n2, Qr_p_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{xr} Γ^r_{pp}` over the common denominator. -/
def Qr_p_xp_n3 : ZExp 6 := a ^ 2 * d * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (4 * a ^ 4
    * r * x ^ 2 - 2 * a ^ 4 * r + a ^ 4 * v * x ^ 4 - a ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d * r * x ^ 2
    + 2 * a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 * x ^ 2 + a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 * v
    + 2 * r ^ 5)
/-- `Γ^r_{xr} Γ^r_{pp}`, reduced to the common denominator. -/
theorem Qr_p_xp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_rx * Gr_pp) (⟨Qr_p_xp_n3, Qr_p_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Gr_pp, Qr_p_xp_n3, Qr_p_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{xx} Γ^x_{pp}` over the common denominator. -/
def Qr_p_xp_n4 : ZExp 6 := -2 * d * r * x * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 6 + a ^ 4 * d * x ^ 4 -
    a ^ 4 * d + 3 * a ^ 4 * r ^ 2 + 2 * a ^ 2 * d * r ^ 2 * x ^ 2 - 2 * a ^ 2 * d * r ^ 2 + 3 * a ^
    2 * r ^ 4 + r ^ 6)
/-- `Γ^r_{xx} Γ^x_{pp}`, reduced to the common denominator. -/
theorem Qr_p_xp_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_xx * Gx_pp) (⟨Qr_p_xp_n4, Qr_p_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_xx, Gx_pp, Qr_p_xp_n4, Qr_p_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^r_{pp} Γ^p_{xp}` over the common denominator. -/
def Qr_p_xp_n5 : ZExp 6 := d * x * (a ^ 4 * x ^ 4 - a ^ 4 * x ^ 2 + a ^ 4 + a ^ 2 * d * x ^ 2 - a ^
    2 * d + a ^ 2 * r ^ 2 * x ^ 2 + a ^ 2 * r ^ 2 + r ^ 4) * (4 * a ^ 4 * r * x ^ 2 - 2 * a ^ 4 * r
    + a ^ 4 * v * x ^ 4 - a ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d * r * x ^ 2 + 2 * a ^ 2 * d * r + 4 * a
    ^ 2 * r ^ 3 * x ^ 2 + a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 * v + 2 * r ^ 5)
/-- `Γ^r_{pp} Γ^p_{xp}`, reduced to the common denominator. -/
theorem Qr_p_xp_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gr_pp * Gp_xp) (⟨Qr_p_xp_n5, Qr_p_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_pp, Gp_xp, Qr_p_xp_n5, Qr_p_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R^r_{pxp}` (`eq:Riemann`): the signed sum of its terms is the reduced fraction. -/
theorem riemann_r_p_xp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Qr_p_xp_n1 - Qr_p_xp_n2 + Qr_p_xp_n3 + Qr_p_xp_n4 - Qr_p_xp_n5,
          Qr_p_xp_cd⟩) (Qr_p_xp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Qr_p_xp_n1, Qr_p_xp_n2, Qr_p_xp_n3, Qr_p_xp_n4, Qr_p_xp_n5, Qr_p_xp_cd,
        Qr_p_xp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

end LeanProofs.IPRA.Geometry.KerrNewmanRiemannR
