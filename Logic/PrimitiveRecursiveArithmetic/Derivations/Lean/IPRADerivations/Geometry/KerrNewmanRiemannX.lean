import IPRADerivations.Geometry.KerrNewmanConnectionDerivatives

/-!
# The Riemann tensor of the radial-function metric, upper index `x` (`four_metrics_ipra`)

Packet: `geometry/four_metrics_ipra_2026-11-15`, `eq:Riemann`: `R^i_{jkℓ} = ∂_k Γ^i_{ℓj} − ∂_ℓ
    Γ^i_{kj} + Σ_h (Γ^i_{kh} Γ^h_{ℓj} − Γ^i_{ℓh} Γ^h_{kj})`, here for
`i = x`, with the connection of `Geometry/KerrNewmanConnection` and its reduced derivatives of
`Geometry/KerrNewmanConnectionDerivatives` (radial function `d`, `∂_r d = v`, `∂_r v = w`;
Boyer–Lindquist coordinates, index `p` for `φ`; `∂_t = ∂_φ = 0`).

For each component `R^x_{jkℓ}` with `k < ℓ` that has a term with nonzero factors:
`Qx_j_kl_tn` (each term reduced over a common denominator) and `riemann_x_j_kl` (their
signed sum is the reduced fraction `Qx_j_kl`, or `0`). The upper indices `t`, `r`, `x`, `φ` are
the four modules `Geometry/KerrNewmanRiemannT`, `…R`, `…X`, `…P`; the contraction is
`Geometry/KerrNewmanKretschmann`. The curvature symmetries and the contraction to the Ricci
tensor (`Geometry/KerrNewmanRicci`) are not restated.

The reduced fractions and numerators were proposed by a computer algebra script; every identity
is checked by Lean as an identity of fractions cleared of denominators, a closed sentence of iPRA
certified in every commutative ring.
-/

namespace LeanProofs.IPRA.Geometry.KerrNewmanRiemannX

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

/-! ### `R^x_{ttr}` -/

/-- `R^x_{ttr}`, reduced. -/
def Qx_t_tr : Frac 6 := ⟨3 * a ^ 2 * x * (x - 1) * (x + 1) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r
    - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v), 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4⟩

/-- The common denominator of the terms of `R^x_{ttr}`. -/
def Qx_t_tr_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `∂_r Γ^x_{tt}` over the common denominator. -/
def Qx_t_tr_n1 : ZExp 6 := -2 * a ^ 2 * d * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (2 *
    a ^ 2 * r * x ^ 2 - 6 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 6 * d * r - 4 * r ^ 3 - r ^ 2 * v)
/-- `∂_r Γ^x_{tt}`, reduced to the common denominator. -/
theorem Qx_t_tr_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (dr_Gx_tt) (⟨Qx_t_tr_n1, Qx_t_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [dr_Gx_tt, Qx_t_tr_n1, Qx_t_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{tt} Γ^t_{rt}` over the common denominator. -/
def Qx_t_tr_n2 : ZExp 6 := a ^ 2 * x * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) *
    (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^x_{tt} Γ^t_{rt}`, reduced to the common denominator. -/
theorem Qx_t_tr_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_tt * Gt_tr) (⟨Qx_t_tr_n2, Qx_t_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_tt, Gt_tr, Qx_t_tr_n2, Qx_t_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{rr} Γ^r_{tt}` over the common denominator. -/
def Qx_t_tr_n3 : ZExp 6 := -a ^ 2 * d * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (2 * a ^
    2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^x_{rr} Γ^r_{tt}`, reduced to the common denominator. -/
theorem Qx_t_tr_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_rr * Gr_tt) (⟨Qx_t_tr_n3, Qx_t_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rr, Gr_tt, Qx_t_tr_n3, Qx_t_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{rx} Γ^x_{tt}` over the common denominator. -/
def Qx_t_tr_n4 : ZExp 6 := -2 * a ^ 2 * d * r * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) *
    (a ^ 2 - d + r ^ 2)
/-- `Γ^x_{rx} Γ^x_{tt}`, reduced to the common denominator. -/
theorem Qx_t_tr_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_rx * Gx_tt) (⟨Qx_t_tr_n4, Qx_t_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rx, Gx_tt, Qx_t_tr_n4, Qx_t_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{tp} Γ^p_{rt}` over the common denominator. -/
def Qx_t_tr_n5 : ZExp 6 := -a ^ 2 * x * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) *
    (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^x_{tp} Γ^p_{rt}`, reduced to the common denominator. -/
theorem Qx_t_tr_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_tp * Gp_tr) (⟨Qx_t_tr_n5, Qx_t_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_tp, Gp_tr, Qx_t_tr_n5, Qx_t_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R^x_{ttr}` (`eq:Riemann`): the signed sum of its terms is the reduced fraction. -/
theorem riemann_x_t_tr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨0 - Qx_t_tr_n1 + Qx_t_tr_n2 - Qx_t_tr_n3 - Qx_t_tr_n4 + Qx_t_tr_n5,
          Qx_t_tr_cd⟩) (Qx_t_tr))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Qx_t_tr_n1, Qx_t_tr_n2, Qx_t_tr_n3, Qx_t_tr_n4, Qx_t_tr_n5, Qx_t_tr_cd,
        Qx_t_tr, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R^x_{ttx}` -/

/-- `R^x_{ttx}`, reduced. -/
def Qx_t_tx : Frac 6 := ⟨-6 * a ^ 6 * x ^ 4 + 6 * a ^ 6 * x ^ 2 + 6 * a ^ 4 * d * x ^ 4 - 4 * a ^ 4
    * d * x ^ 2 - 6 * a ^ 4 * r ^ 2 * x ^ 4 + 8 * a ^ 4 * r ^ 2 * x ^ 2 - 2 * a ^ 4 * r ^ 2 - 2 * a
    ^ 2 * d ^ 2 * x ^ 2 + 2 * a ^ 2 * d * r ^ 2 * x ^ 2 - a ^ 2 * d * r * v * x ^ 2 + 2 * a ^ 2 * r
    ^ 4 * x ^ 2 - 2 * a ^ 2 * r ^ 4 + 2 * d ^ 2 * r ^ 2 - d * r ^ 3 * v, 2 * (a ^ 2 * x ^ 2 + r ^
    2) ^ 4⟩

/-- The common denominator of the terms of `R^x_{ttx}`. -/
def Qx_t_tx_cd : ZExp 6 := 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `∂_x Γ^x_{tt}` over the common denominator. -/
def Qx_t_tx_n1 : ZExp 6 := 2 * a ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 - d + r ^ 2) * (3 * a ^ 2 *
    x ^ 4 - 5 * a ^ 2 * x ^ 2 - 3 * r ^ 2 * x ^ 2 + r ^ 2)
/-- `∂_x Γ^x_{tt}`, reduced to the common denominator. -/
theorem Qx_t_tx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (dx_Gx_tt) (⟨Qx_t_tx_n1, Qx_t_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [dx_Gx_tt, Qx_t_tx_n1, Qx_t_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{tt} Γ^t_{xt}` over the common denominator. -/
def Qx_t_tx_n2 : ZExp 6 := -2 * a ^ 4 * x ^ 2 * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) ^ 2
/-- `Γ^x_{tt} Γ^t_{xt}`, reduced to the common denominator. -/
theorem Qx_t_tx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_tt * Gt_tx) (⟨Qx_t_tx_n2, Qx_t_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_tt, Gt_tx, Qx_t_tx_n2, Qx_t_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{xr} Γ^r_{tt}` over the common denominator. -/
def Qx_t_tx_n3 : ZExp 6 := -d * r * (a ^ 2 * x ^ 2 + r ^ 2) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 *
    r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^x_{xr} Γ^r_{tt}`, reduced to the common denominator. -/
theorem Qx_t_tx_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_rx * Gr_tt) (⟨Qx_t_tx_n3, Qx_t_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rx, Gr_tt, Qx_t_tx_n3, Qx_t_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{xx} Γ^x_{tt}` over the common denominator. -/
def Qx_t_tx_n4 : ZExp 6 := 2 * a ^ 2 * x ^ 2 * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 -
    d + r ^ 2)
/-- `Γ^x_{xx} Γ^x_{tt}`, reduced to the common denominator. -/
theorem Qx_t_tx_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_xx * Gx_tt) (⟨Qx_t_tx_n4, Qx_t_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_xx, Gx_tt, Qx_t_tx_n4, Qx_t_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{tp} Γ^p_{xt}` over the common denominator. -/
def Qx_t_tx_n5 : ZExp 6 := -2 * a ^ 2 * x ^ 2 * (a ^ 2 + r ^ 2) * (a ^ 2 - d + r ^ 2) ^ 2
/-- `Γ^x_{tp} Γ^p_{xt}`, reduced to the common denominator. -/
theorem Qx_t_tx_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_tp * Gp_tx) (⟨Qx_t_tx_n5, Qx_t_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_tp, Gp_tx, Qx_t_tx_n5, Qx_t_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R^x_{ttx}` (`eq:Riemann`): the signed sum of its terms is the reduced fraction. -/
theorem riemann_x_t_tx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨0 - Qx_t_tx_n1 + Qx_t_tx_n2 - Qx_t_tx_n3 - Qx_t_tx_n4 + Qx_t_tx_n5,
          Qx_t_tx_cd⟩) (Qx_t_tx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Qx_t_tx_n1, Qx_t_tx_n2, Qx_t_tx_n3, Qx_t_tx_n4, Qx_t_tx_n5, Qx_t_tx_cd,
        Qx_t_tx, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R^x_{trp}` -/

/-- `R^x_{trp}`, reduced. -/
def Qx_t_rp : Frac 6 := ⟨-a * x * (x - 1) * (x + 1) * (2 * a ^ 2 * x ^ 2 - 3 * a ^ 2 - r ^ 2) * (2
    * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v), 2
    * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4⟩

/-- The common denominator of the terms of `R^x_{trp}`. -/
def Qx_t_rp_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `∂_r Γ^x_{pt}` over the common denominator. -/
def Qx_t_rp_n1 : ZExp 6 := 2 * a * d * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (4 * a ^ 4
    * r * x ^ 2 - 6 * a ^ 4 * r - a ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d * r * x ^ 2 + 6 * a ^ 2 * d * r
    + 4 * a ^ 2 * r ^ 3 * x ^ 2 - 8 * a ^ 2 * r ^ 3 - a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 * v
    + 4 * d * r ^ 3 - 2 * r ^ 5 - r ^ 4 * v)
/-- `∂_r Γ^x_{pt}`, reduced to the common denominator. -/
theorem Qx_t_rp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (dr_Gx_tp) (⟨Qx_t_rp_n1, Qx_t_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [dr_Gx_tp, Qx_t_rp_n1, Qx_t_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{pt} Γ^t_{rt}` over the common denominator. -/
def Qx_t_rp_n2 : ZExp 6 := -a * x * (a ^ 2 + r ^ 2) ^ 2 * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) *
    (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^x_{pt} Γ^t_{rt}`, reduced to the common denominator. -/
theorem Qx_t_rp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_tp * Gt_tr) (⟨Qx_t_rp_n2, Qx_t_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_tp, Gt_tr, Qx_t_rp_n2, Qx_t_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{rr} Γ^r_{pt}` over the common denominator. -/
def Qx_t_rp_n3 : ZExp 6 := -a ^ 3 * d * x * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) *
    (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^x_{rr} Γ^r_{pt}`, reduced to the common denominator. -/
theorem Qx_t_rp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_rr * Gr_tp) (⟨Qx_t_rp_n3, Qx_t_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rr, Gr_tp, Qx_t_rp_n3, Qx_t_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{rx} Γ^x_{pt}` over the common denominator. -/
def Qx_t_rp_n4 : ZExp 6 := 2 * a * d * r * x * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2
    + r ^ 2) * (a ^ 2 - d + r ^ 2)
/-- `Γ^x_{rx} Γ^x_{pt}`, reduced to the common denominator. -/
theorem Qx_t_rp_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_rx * Gx_tp) (⟨Qx_t_rp_n4, Qx_t_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rx, Gx_tp, Qx_t_rp_n4, Qx_t_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{pp} Γ^p_{rt}` over the common denominator. -/
def Qx_t_rp_n5 : ZExp 6 := a * x * (x - 1) * (x + 1) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^
    2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v) * (a ^ 6 + a ^ 4 * d * x ^ 4 - a ^ 4 * d + 3 * a ^ 4 * r
    ^ 2 + 2 * a ^ 2 * d * r ^ 2 * x ^ 2 - 2 * a ^ 2 * d * r ^ 2 + 3 * a ^ 2 * r ^ 4 + r ^ 6)
/-- `Γ^x_{pp} Γ^p_{rt}`, reduced to the common denominator. -/
theorem Qx_t_rp_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_pp * Gp_tr) (⟨Qx_t_rp_n5, Qx_t_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_pp, Gp_tr, Qx_t_rp_n5, Qx_t_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R^x_{trp}` (`eq:Riemann`): the signed sum of its terms is the reduced fraction. -/
theorem riemann_x_t_rp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Qx_t_rp_n1 - Qx_t_rp_n2 + Qx_t_rp_n3 + Qx_t_rp_n4 - Qx_t_rp_n5,
          Qx_t_rp_cd⟩) (Qx_t_rp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Qx_t_rp_n1, Qx_t_rp_n2, Qx_t_rp_n3, Qx_t_rp_n4, Qx_t_rp_n5, Qx_t_rp_cd,
        Qx_t_rp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R^x_{txp}` -/

/-- `R^x_{txp}`, reduced. -/
def Qx_t_xp : Frac 6 := ⟨-a * (x - 1) * (x + 1) * (6 * a ^ 6 * x ^ 2 - 4 * a ^ 4 * d * x ^ 2 + 12 *
    a ^ 4 * r ^ 2 * x ^ 2 - 2 * a ^ 4 * r ^ 2 - 2 * a ^ 2 * d ^ 2 * x ^ 2 - 2 * a ^ 2 * d * r ^ 2 *
    x ^ 2 - a ^ 2 * d * r * v * x ^ 2 + 6 * a ^ 2 * r ^ 4 * x ^ 2 - 4 * a ^ 2 * r ^ 4 + 2 * d ^ 2 *
    r ^ 2 + 2 * d * r ^ 4 - d * r ^ 3 * v - 2 * r ^ 6), 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4⟩

/-- The common denominator of the terms of `R^x_{txp}`. -/
def Qx_t_xp_cd : ZExp 6 := 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `∂_x Γ^x_{pt}` over the common denominator. -/
def Qx_t_xp_n1 : ZExp 6 := -2 * a * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 - d + r ^ 2)
    * (3 * a ^ 2 * x ^ 4 - 5 * a ^ 2 * x ^ 2 - 3 * r ^ 2 * x ^ 2 + r ^ 2)
/-- `∂_x Γ^x_{pt}`, reduced to the common denominator. -/
theorem Qx_t_xp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (dx_Gx_tp) (⟨Qx_t_xp_n1, Qx_t_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [dx_Gx_tp, Qx_t_xp_n1, Qx_t_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{pt} Γ^t_{xt}` over the common denominator. -/
def Qx_t_xp_n2 : ZExp 6 := 2 * a ^ 3 * x ^ 2 * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 - d + r
    ^ 2) ^ 2
/-- `Γ^x_{pt} Γ^t_{xt}`, reduced to the common denominator. -/
theorem Qx_t_xp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_tp * Gt_tx) (⟨Qx_t_xp_n2, Qx_t_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_tp, Gt_tx, Qx_t_xp_n2, Qx_t_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{xr} Γ^r_{pt}` over the common denominator. -/
def Qx_t_xp_n3 : ZExp 6 := -a * d * r * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (2 * a ^ 2 *
    r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^x_{xr} Γ^r_{pt}`, reduced to the common denominator. -/
theorem Qx_t_xp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_rx * Gr_tp) (⟨Qx_t_xp_n3, Qx_t_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rx, Gr_tp, Qx_t_xp_n3, Qx_t_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{xx} Γ^x_{pt}` over the common denominator. -/
def Qx_t_xp_n4 : ZExp 6 := -2 * a * x ^ 2 * (a ^ 2 + r ^ 2) ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2
    - d + r ^ 2)
/-- `Γ^x_{xx} Γ^x_{pt}`, reduced to the common denominator. -/
theorem Qx_t_xp_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_xx * Gx_tp) (⟨Qx_t_xp_n4, Qx_t_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_xx, Gx_tp, Qx_t_xp_n4, Qx_t_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{pp} Γ^p_{xt}` over the common denominator. -/
def Qx_t_xp_n5 : ZExp 6 := 2 * a * x ^ 2 * (a ^ 2 - d + r ^ 2) * (a ^ 6 + a ^ 4 * d * x ^ 4 - a ^ 4
    * d + 3 * a ^ 4 * r ^ 2 + 2 * a ^ 2 * d * r ^ 2 * x ^ 2 - 2 * a ^ 2 * d * r ^ 2 + 3 * a ^ 2 * r
    ^ 4 + r ^ 6)
/-- `Γ^x_{pp} Γ^p_{xt}`, reduced to the common denominator. -/
theorem Qx_t_xp_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_pp * Gp_tx) (⟨Qx_t_xp_n5, Qx_t_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_pp, Gp_tx, Qx_t_xp_n5, Qx_t_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R^x_{txp}` (`eq:Riemann`): the signed sum of its terms is the reduced fraction. -/
theorem riemann_x_t_xp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Qx_t_xp_n1 - Qx_t_xp_n2 + Qx_t_xp_n3 + Qx_t_xp_n4 - Qx_t_xp_n5,
          Qx_t_xp_cd⟩) (Qx_t_xp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Qx_t_xp_n1, Qx_t_xp_n2, Qx_t_xp_n3, Qx_t_xp_n4, Qx_t_xp_n5, Qx_t_xp_cd,
        Qx_t_xp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R^x_{rtp}` -/

/-- `R^x_{rtp}`, reduced. -/
def Qx_r_tp : Frac 6 := ⟨-a * x * (x - 1) * (x + 1) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^
    2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v), 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `R^x_{rtp}`. -/
def Qx_r_tp_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `Γ^x_{tt} Γ^t_{pr}` over the common denominator. -/
def Qx_r_tp_n1 : ZExp 6 := -a ^ 3 * x * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 - d + r ^ 2) * (2 * a ^
    4 * r + a ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d * r * x ^ 2 - 2 * a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 +
    a ^ 2 * r ^ 2 * v * x ^ 2 + a ^ 2 * r ^ 2 * v - 4 * d * r ^ 3 + 2 * r ^ 5 + r ^ 4 * v)
/-- `Γ^x_{tt} Γ^t_{pr}`, reduced to the common denominator. -/
theorem Qx_r_tp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_tt * Gt_rp) (⟨Qx_r_tp_n1, Qx_r_tp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_tt, Gt_rp, Qx_r_tp_n1, Qx_r_tp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{pt} Γ^t_{tr}` over the common denominator. -/
def Qx_r_tp_n2 : ZExp 6 := -a * x * (a ^ 2 + r ^ 2) ^ 2 * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) *
    (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^x_{pt} Γ^t_{tr}`, reduced to the common denominator. -/
theorem Qx_r_tp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_tp * Gt_tr) (⟨Qx_r_tp_n2, Qx_r_tp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_tp, Gt_tr, Qx_r_tp_n2, Qx_r_tp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{tp} Γ^p_{pr}` over the common denominator. -/
def Qx_r_tp_n3 : ZExp 6 := a * x * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) * (2 *
    a ^ 4 * r * x ^ 2 - 2 * a ^ 4 * r + a ^ 4 * v * x ^ 4 - a ^ 4 * v * x ^ 2 + 2 * a ^ 2 * d * r +
    2 * a ^ 2 * r ^ 3 * x ^ 2 - 2 * a ^ 2 * r ^ 3 + a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 * v +
    2 * d * r ^ 3)
/-- `Γ^x_{tp} Γ^p_{pr}`, reduced to the common denominator. -/
theorem Qx_r_tp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_tp * Gp_rp) (⟨Qx_r_tp_n3, Qx_r_tp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_tp, Gp_rp, Qx_r_tp_n3, Qx_r_tp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{pp} Γ^p_{tr}` over the common denominator. -/
def Qx_r_tp_n4 : ZExp 6 := a * x * (x - 1) * (x + 1) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^
    2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v) * (a ^ 6 + a ^ 4 * d * x ^ 4 - a ^ 4 * d + 3 * a ^ 4 * r
    ^ 2 + 2 * a ^ 2 * d * r ^ 2 * x ^ 2 - 2 * a ^ 2 * d * r ^ 2 + 3 * a ^ 2 * r ^ 4 + r ^ 6)
/-- `Γ^x_{pp} Γ^p_{tr}`, reduced to the common denominator. -/
theorem Qx_r_tp_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_pp * Gp_tr) (⟨Qx_r_tp_n4, Qx_r_tp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_pp, Gp_tr, Qx_r_tp_n4, Qx_r_tp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R^x_{rtp}` (`eq:Riemann`): the signed sum of its terms is the reduced fraction. -/
theorem riemann_x_r_tp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Qx_r_tp_n1 - Qx_r_tp_n2 + Qx_r_tp_n3 - Qx_r_tp_n4, Qx_r_tp_cd⟩)
          (Qx_r_tp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Qx_r_tp_n1, Qx_r_tp_n2, Qx_r_tp_n3, Qx_r_tp_n4, Qx_r_tp_cd, Qx_r_tp, δr_0,
        δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R^x_{rrx}` -/

/-- `R^x_{rrx}`, reduced. -/
def Qx_r_rx : Frac 6 := ⟨-2 * a ^ 4 * x ^ 2 + 2 * a ^ 2 * d * x ^ 2 - 4 * a ^ 2 * r ^ 2 * x ^ 2 + 2
    * a ^ 2 * r ^ 2 + a ^ 2 * r * v * x ^ 2 - 2 * d * r ^ 2 + r ^ 3 * v, 2 * d * (a ^ 2 * x ^ 2 + r
    ^ 2) ^ 2⟩

/-- The common denominator of the terms of `R^x_{rrx}`. -/
def Qx_r_rx_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2

/-- The numerator of `∂_r Γ^x_{xr}` over the common denominator. -/
def Qx_r_rx_n1 : ZExp 6 := 2 * d * (a * x - r) * (a * x + r)
/-- `∂_r Γ^x_{xr}`, reduced to the common denominator. -/
theorem Qx_r_rx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (dr_Gx_rx) (⟨Qx_r_rx_n1, Qx_r_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [dr_Gx_rx, Qx_r_rx_n1, Qx_r_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `∂_x Γ^x_{rr}` over the common denominator. -/
def Qx_r_rx_n2 : ZExp 6 := 2 * a ^ 2 * (a ^ 2 * x ^ 4 + a ^ 2 * x ^ 2 + 3 * r ^ 2 * x ^ 2 - r ^ 2)
/-- `∂_x Γ^x_{rr}`, reduced to the common denominator. -/
theorem Qx_r_rx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (dx_Gx_rr) (⟨Qx_r_rx_n2, Qx_r_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [dx_Gx_rr, Qx_r_rx_n2, Qx_r_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{rr} Γ^r_{xr}` over the common denominator. -/
def Qx_r_rx_n3 : ZExp 6 := 2 * a ^ 4 * x ^ 2 * (x - 1) * (x + 1)
/-- `Γ^x_{rr} Γ^r_{xr}`, reduced to the common denominator. -/
theorem Qx_r_rx_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_rr * Gr_rx) (⟨Qx_r_rx_n3, Qx_r_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rr, Gr_rx, Qx_r_rx_n3, Qx_r_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{xr} Γ^r_{rr}` over the common denominator. -/
def Qx_r_rx_n4 : ZExp 6 := -r * (a ^ 2 * v * x ^ 2 - 2 * d * r + r ^ 2 * v)
/-- `Γ^x_{xr} Γ^r_{rr}`, reduced to the common denominator. -/
theorem Qx_r_rx_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_rx * Gr_rr) (⟨Qx_r_rx_n4, Qx_r_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rx, Gr_rr, Qx_r_rx_n4, Qx_r_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{rx} Γ^x_{xr}` over the common denominator. -/
def Qx_r_rx_n5 : ZExp 6 := 2 * d * r ^ 2
/-- `Γ^x_{rx} Γ^x_{xr}`, reduced to the common denominator. -/
theorem Qx_r_rx_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_rx * Gx_rx) (⟨Qx_r_rx_n5, Qx_r_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rx, Qx_r_rx_n5, Qx_r_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1,
        δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{xx} Γ^x_{rr}` over the common denominator. -/
def Qx_r_rx_n6 : ZExp 6 := -2 * a ^ 2 * x ^ 2 * (a ^ 2 + r ^ 2)
/-- `Γ^x_{xx} Γ^x_{rr}`, reduced to the common denominator. -/
theorem Qx_r_rx_t6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_xx * Gx_rr) (⟨Qx_r_rx_n6, Qx_r_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_xx, Gx_rr, Qx_r_rx_n6, Qx_r_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R^x_{rrx}` (`eq:Riemann`): the signed sum of its terms is the reduced fraction. -/
theorem riemann_x_r_rx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Qx_r_rx_n1 - Qx_r_rx_n2 + Qx_r_rx_n3 - Qx_r_rx_n4 + Qx_r_rx_n5 -
          Qx_r_rx_n6, Qx_r_rx_cd⟩) (Qx_r_rx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Qx_r_rx_n1, Qx_r_rx_n2, Qx_r_rx_n3, Qx_r_rx_n4, Qx_r_rx_n5, Qx_r_rx_n6,
        Qx_r_rx_cd, Qx_r_rx, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R^x_{xtp}` -/

/-- The common denominator of the terms of `R^x_{xtp}`. -/
def Qx_x_tp_cd : ZExp 6 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `Γ^x_{tt} Γ^t_{px}` over the common denominator. -/
def Qx_x_tp_n1 : ZExp 6 := -a ^ 5 * x ^ 2 * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 - d + r ^ 2) ^ 2
/-- `Γ^x_{tt} Γ^t_{px}`, reduced to the common denominator. -/
theorem Qx_x_tp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_tt * Gt_xp) (⟨Qx_x_tp_n1, Qx_x_tp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_tt, Gt_xp, Qx_x_tp_n1, Qx_x_tp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{pt} Γ^t_{tx}` over the common denominator. -/
def Qx_x_tp_n2 : ZExp 6 := a ^ 3 * x ^ 2 * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 - d + r ^
    2) ^ 2
/-- `Γ^x_{pt} Γ^t_{tx}`, reduced to the common denominator. -/
theorem Qx_x_tp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_tp * Gt_tx) (⟨Qx_x_tp_n2, Qx_x_tp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_tp, Gt_tx, Qx_x_tp_n2, Qx_x_tp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{tp} Γ^p_{px}` over the common denominator. -/
def Qx_x_tp_n3 : ZExp 6 := a * x ^ 2 * (a ^ 2 + r ^ 2) * (a ^ 2 - d + r ^ 2) * (a ^ 4 * x ^ 4 - a ^
    4 * x ^ 2 + a ^ 4 + a ^ 2 * d * x ^ 2 - a ^ 2 * d + a ^ 2 * r ^ 2 * x ^ 2 + a ^ 2 * r ^ 2 + r ^
    4)
/-- `Γ^x_{tp} Γ^p_{px}`, reduced to the common denominator. -/
theorem Qx_x_tp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_tp * Gp_xp) (⟨Qx_x_tp_n3, Qx_x_tp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_tp, Gp_xp, Qx_x_tp_n3, Qx_x_tp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{pp} Γ^p_{tx}` over the common denominator. -/
def Qx_x_tp_n4 : ZExp 6 := a * x ^ 2 * (a ^ 2 - d + r ^ 2) * (a ^ 6 + a ^ 4 * d * x ^ 4 - a ^ 4 * d
    + 3 * a ^ 4 * r ^ 2 + 2 * a ^ 2 * d * r ^ 2 * x ^ 2 - 2 * a ^ 2 * d * r ^ 2 + 3 * a ^ 2 * r ^ 4
    + r ^ 6)
/-- `Γ^x_{pp} Γ^p_{tx}`, reduced to the common denominator. -/
theorem Qx_x_tp_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_pp * Gp_tx) (⟨Qx_x_tp_n4, Qx_x_tp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_pp, Gp_tx, Qx_x_tp_n4, Qx_x_tp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R^x_{xtp}` (`eq:Riemann`): the signed sum of its terms is `0`. -/
theorem riemann_x_x_tp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Qx_x_tp_n1 - Qx_x_tp_n2 + Qx_x_tp_n3 - Qx_x_tp_n4, Qx_x_tp_cd⟩) (Frac.ofZ
          0))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Qx_x_tp_n1, Qx_x_tp_n2, Qx_x_tp_n3, Qx_x_tp_n4, Qx_x_tp_cd, δr_0, δr_1, δr_2,
        δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R^x_{xrx}` -/

/-- The common denominator of the terms of `R^x_{xrx}`. -/
def Qx_x_rx_cd : ZExp 6 := (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2

/-- The numerator of `∂_r Γ^x_{xx}` over the common denominator. -/
def Qx_x_rx_n1 : ZExp 6 := -2 * a ^ 2 * r * x * (x - 1) * (x + 1)
/-- `∂_r Γ^x_{xx}`, reduced to the common denominator. -/
theorem Qx_x_rx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (dr_Gx_xx) (⟨Qx_x_rx_n1, Qx_x_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [dr_Gx_xx, Qx_x_rx_n1, Qx_x_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `∂_x Γ^x_{rx}` over the common denominator. -/
def Qx_x_rx_n2 : ZExp 6 := -2 * a ^ 2 * r * x * (x - 1) * (x + 1)
/-- `∂_x Γ^x_{rx}`, reduced to the common denominator. -/
theorem Qx_x_rx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (dx_Gx_rx) (⟨Qx_x_rx_n2, Qx_x_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [dx_Gx_rx, Qx_x_rx_n2, Qx_x_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{rr} Γ^r_{xx}` over the common denominator. -/
def Qx_x_rx_n3 : ZExp 6 := a ^ 2 * r * x * (x - 1) * (x + 1)
/-- `Γ^x_{rr} Γ^r_{xx}`, reduced to the common denominator. -/
theorem Qx_x_rx_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_rr * Gr_xx) (⟨Qx_x_rx_n3, Qx_x_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rr, Gr_xx, Qx_x_rx_n3, Qx_x_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{xr} Γ^r_{rx}` over the common denominator. -/
def Qx_x_rx_n4 : ZExp 6 := a ^ 2 * r * x * (x - 1) * (x + 1)
/-- `Γ^x_{xr} Γ^r_{rx}`, reduced to the common denominator. -/
theorem Qx_x_rx_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_rx * Gr_rx) (⟨Qx_x_rx_n4, Qx_x_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rx, Gr_rx, Qx_x_rx_n4, Qx_x_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{rx} Γ^x_{xx}` over the common denominator. -/
def Qx_x_rx_n5 : ZExp 6 := -r * x * (a ^ 2 + r ^ 2)
/-- `Γ^x_{rx} Γ^x_{xx}`, reduced to the common denominator. -/
theorem Qx_x_rx_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_rx * Gx_xx) (⟨Qx_x_rx_n5, Qx_x_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rx, Gx_xx, Qx_x_rx_n5, Qx_x_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{xx} Γ^x_{rx}` over the common denominator. -/
def Qx_x_rx_n6 : ZExp 6 := -r * x * (a ^ 2 + r ^ 2)
/-- `Γ^x_{xx} Γ^x_{rx}`, reduced to the common denominator. -/
theorem Qx_x_rx_t6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_xx * Gx_rx) (⟨Qx_x_rx_n6, Qx_x_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_xx, Gx_rx, Qx_x_rx_n6, Qx_x_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R^x_{xrx}` (`eq:Riemann`): the signed sum of its terms is `0`. -/
theorem riemann_x_x_rx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Qx_x_rx_n1 - Qx_x_rx_n2 + Qx_x_rx_n3 - Qx_x_rx_n4 + Qx_x_rx_n5 -
          Qx_x_rx_n6, Qx_x_rx_cd⟩) (Frac.ofZ 0))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Qx_x_rx_n1, Qx_x_rx_n2, Qx_x_rx_n3, Qx_x_rx_n4, Qx_x_rx_n5, Qx_x_rx_n6,
        Qx_x_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R^x_{ptr}` -/

/-- `R^x_{ptr}`, reduced. -/
def Qx_p_tr : Frac 6 := ⟨a * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 - 3 * a ^ 2 - 2 * r ^ 2) * (2 *
    a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v), 2 *
    (a ^ 2 * x ^ 2 + r ^ 2) ^ 4⟩

/-- The common denominator of the terms of `R^x_{ptr}`. -/
def Qx_p_tr_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `∂_r Γ^x_{tp}` over the common denominator. -/
def Qx_p_tr_n1 : ZExp 6 := 2 * a * d * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (4 * a ^ 4
    * r * x ^ 2 - 6 * a ^ 4 * r - a ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d * r * x ^ 2 + 6 * a ^ 2 * d * r
    + 4 * a ^ 2 * r ^ 3 * x ^ 2 - 8 * a ^ 2 * r ^ 3 - a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 * v
    + 4 * d * r ^ 3 - 2 * r ^ 5 - r ^ 4 * v)
/-- `∂_r Γ^x_{tp}`, reduced to the common denominator. -/
theorem Qx_p_tr_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (dr_Gx_tp) (⟨Qx_p_tr_n1, Qx_p_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [dr_Gx_tp, Qx_p_tr_n1, Qx_p_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{tt} Γ^t_{rp}` over the common denominator. -/
def Qx_p_tr_n2 : ZExp 6 := -a ^ 3 * x * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 - d + r ^ 2) * (2 * a ^
    4 * r + a ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d * r * x ^ 2 - 2 * a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 +
    a ^ 2 * r ^ 2 * v * x ^ 2 + a ^ 2 * r ^ 2 * v - 4 * d * r ^ 3 + 2 * r ^ 5 + r ^ 4 * v)
/-- `Γ^x_{tt} Γ^t_{rp}`, reduced to the common denominator. -/
theorem Qx_p_tr_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_tt * Gt_rp) (⟨Qx_p_tr_n2, Qx_p_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_tt, Gt_rp, Qx_p_tr_n2, Qx_p_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{rr} Γ^r_{tp}` over the common denominator. -/
def Qx_p_tr_n3 : ZExp 6 := -a ^ 3 * d * x * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) *
    (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^x_{rr} Γ^r_{tp}`, reduced to the common denominator. -/
theorem Qx_p_tr_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_rr * Gr_tp) (⟨Qx_p_tr_n3, Qx_p_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rr, Gr_tp, Qx_p_tr_n3, Qx_p_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{rx} Γ^x_{tp}` over the common denominator. -/
def Qx_p_tr_n4 : ZExp 6 := 2 * a * d * r * x * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2
    + r ^ 2) * (a ^ 2 - d + r ^ 2)
/-- `Γ^x_{rx} Γ^x_{tp}`, reduced to the common denominator. -/
theorem Qx_p_tr_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_rx * Gx_tp) (⟨Qx_p_tr_n4, Qx_p_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rx, Gx_tp, Qx_p_tr_n4, Qx_p_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{tp} Γ^p_{rp}` over the common denominator. -/
def Qx_p_tr_n5 : ZExp 6 := a * x * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) * (2 *
    a ^ 4 * r * x ^ 2 - 2 * a ^ 4 * r + a ^ 4 * v * x ^ 4 - a ^ 4 * v * x ^ 2 + 2 * a ^ 2 * d * r +
    2 * a ^ 2 * r ^ 3 * x ^ 2 - 2 * a ^ 2 * r ^ 3 + a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 * v +
    2 * d * r ^ 3)
/-- `Γ^x_{tp} Γ^p_{rp}`, reduced to the common denominator. -/
theorem Qx_p_tr_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_tp * Gp_rp) (⟨Qx_p_tr_n5, Qx_p_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_tp, Gp_rp, Qx_p_tr_n5, Qx_p_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R^x_{ptr}` (`eq:Riemann`): the signed sum of its terms is the reduced fraction. -/
theorem riemann_x_p_tr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨0 - Qx_p_tr_n1 + Qx_p_tr_n2 - Qx_p_tr_n3 - Qx_p_tr_n4 + Qx_p_tr_n5,
          Qx_p_tr_cd⟩) (Qx_p_tr))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Qx_p_tr_n1, Qx_p_tr_n2, Qx_p_tr_n3, Qx_p_tr_n4, Qx_p_tr_n5, Qx_p_tr_cd,
        Qx_p_tr, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R^x_{ptx}` -/

/-- `R^x_{ptx}`, reduced. -/
def Qx_p_tx : Frac 6 := ⟨a * (x - 1) * (x + 1) * (6 * a ^ 6 * x ^ 2 - 4 * a ^ 4 * d * x ^ 2 + 12 *
    a ^ 4 * r ^ 2 * x ^ 2 - 2 * a ^ 4 * r ^ 2 - 2 * a ^ 2 * d ^ 2 * x ^ 2 - 2 * a ^ 2 * d * r ^ 2 *
    x ^ 2 - a ^ 2 * d * r * v * x ^ 2 + 6 * a ^ 2 * r ^ 4 * x ^ 2 - 4 * a ^ 2 * r ^ 4 + 2 * d ^ 2 *
    r ^ 2 + 2 * d * r ^ 4 - d * r ^ 3 * v - 2 * r ^ 6), 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4⟩

/-- The common denominator of the terms of `R^x_{ptx}`. -/
def Qx_p_tx_cd : ZExp 6 := 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `∂_x Γ^x_{tp}` over the common denominator. -/
def Qx_p_tx_n1 : ZExp 6 := -2 * a * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 - d + r ^ 2)
    * (3 * a ^ 2 * x ^ 4 - 5 * a ^ 2 * x ^ 2 - 3 * r ^ 2 * x ^ 2 + r ^ 2)
/-- `∂_x Γ^x_{tp}`, reduced to the common denominator. -/
theorem Qx_p_tx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (dx_Gx_tp) (⟨Qx_p_tx_n1, Qx_p_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [dx_Gx_tp, Qx_p_tx_n1, Qx_p_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{tt} Γ^t_{xp}` over the common denominator. -/
def Qx_p_tx_n2 : ZExp 6 := -2 * a ^ 5 * x ^ 2 * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 - d + r ^ 2) ^ 2
/-- `Γ^x_{tt} Γ^t_{xp}`, reduced to the common denominator. -/
theorem Qx_p_tx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_tt * Gt_xp) (⟨Qx_p_tx_n2, Qx_p_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_tt, Gt_xp, Qx_p_tx_n2, Qx_p_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{xr} Γ^r_{tp}` over the common denominator. -/
def Qx_p_tx_n3 : ZExp 6 := -a * d * r * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (2 * a ^ 2 *
    r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^x_{xr} Γ^r_{tp}`, reduced to the common denominator. -/
theorem Qx_p_tx_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_rx * Gr_tp) (⟨Qx_p_tx_n3, Qx_p_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rx, Gr_tp, Qx_p_tx_n3, Qx_p_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{xx} Γ^x_{tp}` over the common denominator. -/
def Qx_p_tx_n4 : ZExp 6 := -2 * a * x ^ 2 * (a ^ 2 + r ^ 2) ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2
    - d + r ^ 2)
/-- `Γ^x_{xx} Γ^x_{tp}`, reduced to the common denominator. -/
theorem Qx_p_tx_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_xx * Gx_tp) (⟨Qx_p_tx_n4, Qx_p_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_xx, Gx_tp, Qx_p_tx_n4, Qx_p_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{tp} Γ^p_{xp}` over the common denominator. -/
def Qx_p_tx_n5 : ZExp 6 := 2 * a * x ^ 2 * (a ^ 2 + r ^ 2) * (a ^ 2 - d + r ^ 2) * (a ^ 4 * x ^ 4 -
    a ^ 4 * x ^ 2 + a ^ 4 + a ^ 2 * d * x ^ 2 - a ^ 2 * d + a ^ 2 * r ^ 2 * x ^ 2 + a ^ 2 * r ^ 2 +
    r ^ 4)
/-- `Γ^x_{tp} Γ^p_{xp}`, reduced to the common denominator. -/
theorem Qx_p_tx_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_tp * Gp_xp) (⟨Qx_p_tx_n5, Qx_p_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_tp, Gp_xp, Qx_p_tx_n5, Qx_p_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R^x_{ptx}` (`eq:Riemann`): the signed sum of its terms is the reduced fraction. -/
theorem riemann_x_p_tx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨0 - Qx_p_tx_n1 + Qx_p_tx_n2 - Qx_p_tx_n3 - Qx_p_tx_n4 + Qx_p_tx_n5,
          Qx_p_tx_cd⟩) (Qx_p_tx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Qx_p_tx_n1, Qx_p_tx_n2, Qx_p_tx_n3, Qx_p_tx_n4, Qx_p_tx_n5, Qx_p_tx_cd,
        Qx_p_tx, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R^x_{prp}` -/

/-- `R^x_{prp}`, reduced. -/
def Qx_p_rp : Frac 6 := ⟨3 * a ^ 2 * x * (a ^ 2 + r ^ 2) * (x - 1) ^ 2 * (x + 1) ^ 2 * (2 * a ^ 2 *
    r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v), 2 * (a ^ 2
    * x ^ 2 + r ^ 2) ^ 4⟩

/-- The common denominator of the terms of `R^x_{prp}`. -/
def Qx_p_rp_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `∂_r Γ^x_{pp}` over the common denominator. -/
def Qx_p_rp_n1 : ZExp 6 := -2 * a ^ 2 * d * x * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2)
    * (6 * a ^ 4 * r + a ^ 4 * v * x ^ 4 + a ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d * r * x ^ 2 - 6 * a ^
    2 * d * r + 12 * a ^ 2 * r ^ 3 + 3 * a ^ 2 * r ^ 2 * v * x ^ 2 + a ^ 2 * r ^ 2 * v - 8 * d * r
    ^ 3 + 6 * r ^ 5 + 2 * r ^ 4 * v)
/-- `∂_r Γ^x_{pp}`, reduced to the common denominator. -/
theorem Qx_p_rp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (dr_Gx_pp) (⟨Qx_p_rp_n1, Qx_p_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [dr_Gx_pp, Qx_p_rp_n1, Qx_p_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{pt} Γ^t_{rp}` over the common denominator. -/
def Qx_p_rp_n2 : ZExp 6 := a ^ 2 * x * (a ^ 2 + r ^ 2) * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 - d + r
    ^ 2) * (2 * a ^ 4 * r + a ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d * r * x ^ 2 - 2 * a ^ 2 * d * r + 4 *
    a ^ 2 * r ^ 3 + a ^ 2 * r ^ 2 * v * x ^ 2 + a ^ 2 * r ^ 2 * v - 4 * d * r ^ 3 + 2 * r ^ 5 + r ^
    4 * v)
/-- `Γ^x_{pt} Γ^t_{rp}`, reduced to the common denominator. -/
theorem Qx_p_rp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_tp * Gt_rp) (⟨Qx_p_rp_n2, Qx_p_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_tp, Gt_rp, Qx_p_rp_n2, Qx_p_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{rr} Γ^r_{pp}` over the common denominator. -/
def Qx_p_rp_n3 : ZExp 6 := a ^ 2 * d * x * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) * (4
    * a ^ 4 * r * x ^ 2 - 2 * a ^ 4 * r + a ^ 4 * v * x ^ 4 - a ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d * r
    * x ^ 2 + 2 * a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 * x ^ 2 + a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r
    ^ 2 * v + 2 * r ^ 5)
/-- `Γ^x_{rr} Γ^r_{pp}`, reduced to the common denominator. -/
theorem Qx_p_rp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_rr * Gr_pp) (⟨Qx_p_rp_n3, Qx_p_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rr, Gr_pp, Qx_p_rp_n3, Qx_p_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{rx} Γ^x_{pp}` over the common denominator. -/
def Qx_p_rp_n4 : ZExp 6 := -2 * d * r * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 6 +
    a ^ 4 * d * x ^ 4 - a ^ 4 * d + 3 * a ^ 4 * r ^ 2 + 2 * a ^ 2 * d * r ^ 2 * x ^ 2 - 2 * a ^ 2 *
    d * r ^ 2 + 3 * a ^ 2 * r ^ 4 + r ^ 6)
/-- `Γ^x_{rx} Γ^x_{pp}`, reduced to the common denominator. -/
theorem Qx_p_rp_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_rx * Gx_pp) (⟨Qx_p_rp_n4, Qx_p_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rx, Gx_pp, Qx_p_rp_n4, Qx_p_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{pp} Γ^p_{rp}` over the common denominator. -/
def Qx_p_rp_n5 : ZExp 6 := -x * (x - 1) * (x + 1) * (a ^ 6 + a ^ 4 * d * x ^ 4 - a ^ 4 * d + 3 * a
    ^ 4 * r ^ 2 + 2 * a ^ 2 * d * r ^ 2 * x ^ 2 - 2 * a ^ 2 * d * r ^ 2 + 3 * a ^ 2 * r ^ 4 + r ^
    6) * (2 * a ^ 4 * r * x ^ 2 - 2 * a ^ 4 * r + a ^ 4 * v * x ^ 4 - a ^ 4 * v * x ^ 2 + 2 * a ^ 2
    * d * r + 2 * a ^ 2 * r ^ 3 * x ^ 2 - 2 * a ^ 2 * r ^ 3 + a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r
    ^ 2 * v + 2 * d * r ^ 3)
/-- `Γ^x_{pp} Γ^p_{rp}`, reduced to the common denominator. -/
theorem Qx_p_rp_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_pp * Gp_rp) (⟨Qx_p_rp_n5, Qx_p_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_pp, Gp_rp, Qx_p_rp_n5, Qx_p_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R^x_{prp}` (`eq:Riemann`): the signed sum of its terms is the reduced fraction. -/
theorem riemann_x_p_rp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Qx_p_rp_n1 - Qx_p_rp_n2 + Qx_p_rp_n3 + Qx_p_rp_n4 - Qx_p_rp_n5,
          Qx_p_rp_cd⟩) (Qx_p_rp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Qx_p_rp_n1, Qx_p_rp_n2, Qx_p_rp_n3, Qx_p_rp_n4, Qx_p_rp_n5, Qx_p_rp_cd,
        Qx_p_rp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R^x_{pxp}` -/

/-- `R^x_{pxp}`, reduced. -/
def Qx_p_xp : Frac 6 := ⟨-(x - 1) * (x + 1) * (-6 * a ^ 8 * x ^ 2 + 2 * a ^ 6 * d * x ^ 4 + 4 * a ^
    6 * d * x ^ 2 - 18 * a ^ 6 * r ^ 2 * x ^ 2 + 2 * a ^ 6 * r ^ 2 - 2 * a ^ 4 * d ^ 2 * x ^ 4 + 2
    * a ^ 4 * d ^ 2 * x ^ 2 + 4 * a ^ 4 * d * r ^ 2 * x ^ 4 + 6 * a ^ 4 * d * r ^ 2 * x ^ 2 - a ^ 4
    * d * r * v * x ^ 4 + a ^ 4 * d * r * v * x ^ 2 - 18 * a ^ 4 * r ^ 4 * x ^ 2 + 6 * a ^ 4 * r ^
    4 + 2 * a ^ 2 * d ^ 2 * r ^ 2 * x ^ 2 - 2 * a ^ 2 * d ^ 2 * r ^ 2 + 6 * a ^ 2 * d * r ^ 4 * x ^
    2 - 4 * a ^ 2 * d * r ^ 4 - a ^ 2 * d * r ^ 3 * v * x ^ 2 + a ^ 2 * d * r ^ 3 * v - 6 * a ^ 2 *
    r ^ 6 * x ^ 2 + 6 * a ^ 2 * r ^ 6 - 2 * d * r ^ 6 + 2 * r ^ 8), 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4⟩

/-- The common denominator of the terms of `R^x_{pxp}`. -/
def Qx_p_xp_cd : ZExp 6 := 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `∂_x Γ^x_{pp}` over the common denominator. -/
def Qx_p_xp_n1 : ZExp 6 := -2 * (a ^ 2 * x ^ 2 + r ^ 2) * (-3 * a ^ 8 * x ^ 4 + 5 * a ^ 8 * x ^ 2 +
    a ^ 6 * d * x ^ 8 + a ^ 6 * d * x ^ 6 + 3 * a ^ 6 * d * x ^ 4 - 5 * a ^ 6 * d * x ^ 2 - 9 * a ^
    6 * r ^ 2 * x ^ 4 + 18 * a ^ 6 * r ^ 2 * x ^ 2 - a ^ 6 * r ^ 2 + 5 * a ^ 4 * d * r ^ 2 * x ^ 6
    + 7 * a ^ 4 * d * r ^ 2 * x ^ 4 - 13 * a ^ 4 * d * r ^ 2 * x ^ 2 + a ^ 4 * d * r ^ 2 - 9 * a ^
    4 * r ^ 4 * x ^ 4 + 24 * a ^ 4 * r ^ 4 * x ^ 2 - 3 * a ^ 4 * r ^ 4 + 10 * a ^ 2 * d * r ^ 4 * x
    ^ 4 - 12 * a ^ 2 * d * r ^ 4 * x ^ 2 + 2 * a ^ 2 * d * r ^ 4 - 3 * a ^ 2 * r ^ 6 * x ^ 4 + 14 *
    a ^ 2 * r ^ 6 * x ^ 2 - 3 * a ^ 2 * r ^ 6 + 3 * r ^ 8 * x ^ 2 - r ^ 8)
/-- `∂_x Γ^x_{pp}`, reduced to the common denominator. -/
theorem Qx_p_xp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (dx_Gx_pp) (⟨Qx_p_xp_n1, Qx_p_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [dx_Gx_pp, Qx_p_xp_n1, Qx_p_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{pt} Γ^t_{xp}` over the common denominator. -/
def Qx_p_xp_n2 : ZExp 6 := 2 * a ^ 4 * x ^ 2 * (a ^ 2 + r ^ 2) * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2
    - d + r ^ 2) ^ 2
/-- `Γ^x_{pt} Γ^t_{xp}`, reduced to the common denominator. -/
theorem Qx_p_xp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_tp * Gt_xp) (⟨Qx_p_xp_n2, Qx_p_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_tp, Gt_xp, Qx_p_xp_n2, Qx_p_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{xr} Γ^r_{pp}` over the common denominator. -/
def Qx_p_xp_n3 : ZExp 6 := d * r * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (4 * a ^ 4 * r * x
    ^ 2 - 2 * a ^ 4 * r + a ^ 4 * v * x ^ 4 - a ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d * r * x ^ 2 + 2 * a
    ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 * x ^ 2 + a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 * v + 2 * r
    ^ 5)
/-- `Γ^x_{xr} Γ^r_{pp}`, reduced to the common denominator. -/
theorem Qx_p_xp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_rx * Gr_pp) (⟨Qx_p_xp_n3, Qx_p_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rx, Gr_pp, Qx_p_xp_n3, Qx_p_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{xx} Γ^x_{pp}` over the common denominator. -/
def Qx_p_xp_n4 : ZExp 6 := 2 * x ^ 2 * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 6 + a ^ 4 *
    d * x ^ 4 - a ^ 4 * d + 3 * a ^ 4 * r ^ 2 + 2 * a ^ 2 * d * r ^ 2 * x ^ 2 - 2 * a ^ 2 * d * r ^
    2 + 3 * a ^ 2 * r ^ 4 + r ^ 6)
/-- `Γ^x_{xx} Γ^x_{pp}`, reduced to the common denominator. -/
theorem Qx_p_xp_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_xx * Gx_pp) (⟨Qx_p_xp_n4, Qx_p_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_xx, Gx_pp, Qx_p_xp_n4, Qx_p_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^x_{pp} Γ^p_{xp}` over the common denominator. -/
def Qx_p_xp_n5 : ZExp 6 := -2 * x ^ 2 * (a ^ 6 + a ^ 4 * d * x ^ 4 - a ^ 4 * d + 3 * a ^ 4 * r ^ 2
    + 2 * a ^ 2 * d * r ^ 2 * x ^ 2 - 2 * a ^ 2 * d * r ^ 2 + 3 * a ^ 2 * r ^ 4 + r ^ 6) * (a ^ 4 *
    x ^ 4 - a ^ 4 * x ^ 2 + a ^ 4 + a ^ 2 * d * x ^ 2 - a ^ 2 * d + a ^ 2 * r ^ 2 * x ^ 2 + a ^ 2 *
    r ^ 2 + r ^ 4)
/-- `Γ^x_{pp} Γ^p_{xp}`, reduced to the common denominator. -/
theorem Qx_p_xp_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gx_pp * Gp_xp) (⟨Qx_p_xp_n5, Qx_p_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_pp, Gp_xp, Qx_p_xp_n5, Qx_p_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R^x_{pxp}` (`eq:Riemann`): the signed sum of its terms is the reduced fraction. -/
theorem riemann_x_p_xp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Qx_p_xp_n1 - Qx_p_xp_n2 + Qx_p_xp_n3 + Qx_p_xp_n4 - Qx_p_xp_n5,
          Qx_p_xp_cd⟩) (Qx_p_xp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Qx_p_xp_n1, Qx_p_xp_n2, Qx_p_xp_n3, Qx_p_xp_n4, Qx_p_xp_n5, Qx_p_xp_cd,
        Qx_p_xp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

end LeanProofs.IPRA.Geometry.KerrNewmanRiemannX
