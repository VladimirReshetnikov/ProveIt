import IPRADerivations.Geometry.KerrNewmanConnectionDerivatives

/-!
# The Riemann tensor of the radial-function metric, upper index `t` (`four_metrics_ipra`)

Packet: `geometry/four_metrics_ipra_2026-11-15`, `eq:Riemann`: `R^i_{jkℓ} = ∂_k Γ^i_{ℓj} − ∂_ℓ
    Γ^i_{kj} + Σ_h (Γ^i_{kh} Γ^h_{ℓj} − Γ^i_{ℓh} Γ^h_{kj})`, here for
`i = t`, with the connection of `Geometry/KerrNewmanConnection` and its reduced derivatives of
`Geometry/KerrNewmanConnectionDerivatives` (radial function `d`, `∂_r d = v`, `∂_r v = w`;
Boyer–Lindquist coordinates, index `p` for `φ`; `∂_t = ∂_φ = 0`).

For each component `R^t_{jkℓ}` with `k < ℓ` that has a term with nonzero factors:
`Qt_j_kl_tn` (each term reduced over a common denominator) and `riemann_t_j_kl` (their
signed sum is the reduced fraction `Qt_j_kl`, or `0`). The upper indices `t`, `r`, `x`, `φ` are
the four modules `Geometry/KerrNewmanRiemannT`, `…R`, `…X`, `…P`; the contraction is
`Geometry/KerrNewmanKretschmann`. The curvature symmetries and the contraction to the Ricci
tensor (`Geometry/KerrNewmanRicci`) are not restated.

The reduced fractions and numerators were proposed by a computer algebra script; every identity
is checked by Lean as an identity of fractions cleared of denominators, a closed sentence of iPRA
certified in every commutative ring.
-/

namespace LeanProofs.IPRA.Geometry.KerrNewmanRiemannT

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

/-! ### `R^t_{ttp}` -/

/-- `R^t_{ttp}`, reduced. -/
def Qt_t_tp : Frac 6 := ⟨a * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) * (2 * a ^ 4 * x ^ 2 - 2 * a ^
    2 * d * x ^ 2 + 4 * a ^ 2 * r ^ 2 * x ^ 2 - 2 * a ^ 2 * r ^ 2 - a ^ 2 * r * v * x ^ 2 + 2 * d *
    r ^ 2 - r ^ 3 * v), 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4⟩

/-- The common denominator of the terms of `R^t_{ttp}`. -/
def Qt_t_tp_cd : ZExp 6 := 4 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `Γ^t_{tr} Γ^r_{pt}` over the common denominator. -/
def Qt_t_tp_n1 : ZExp 6 := a * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (2 * a ^ 2 * r * x ^ 2 - 2 * a
    ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v) ^ 2
/-- `Γ^t_{tr} Γ^r_{pt}`, reduced to the common denominator. -/
theorem Qt_t_tp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_tr * Gr_tp) (⟨Qt_t_tp_n1, Qt_t_tp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tr, Gr_tp, Qt_t_tp_n1, Qt_t_tp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{pr} Γ^r_{tt}` over the common denominator. -/
def Qt_t_tp_n2 : ZExp 6 := -a * (x - 1) * (x + 1) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2
    * v * x ^ 2 + 2 * d * r - r ^ 2 * v) * (2 * a ^ 4 * r + a ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d * r *
    x ^ 2 - 2 * a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 + a ^ 2 * r ^ 2 * v * x ^ 2 + a ^ 2 * r ^ 2 * v -
    4 * d * r ^ 3 + 2 * r ^ 5 + r ^ 4 * v)
/-- `Γ^t_{pr} Γ^r_{tt}`, reduced to the common denominator. -/
theorem Qt_t_tp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_rp * Gr_tt) (⟨Qt_t_tp_n2, Qt_t_tp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_rp, Gr_tt, Qt_t_tp_n2, Qt_t_tp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{tx} Γ^x_{pt}` over the common denominator. -/
def Qt_t_tp_n3 : ZExp 6 := 4 * a ^ 3 * x ^ 2 * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 - d + r
    ^ 2) ^ 2
/-- `Γ^t_{tx} Γ^x_{pt}`, reduced to the common denominator. -/
theorem Qt_t_tp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_tx * Gx_tp) (⟨Qt_t_tp_n3, Qt_t_tp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tx, Gx_tp, Qt_t_tp_n3, Qt_t_tp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{px} Γ^x_{tt}` over the common denominator. -/
def Qt_t_tp_n4 : ZExp 6 := -4 * a ^ 5 * x ^ 2 * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 - d + r ^ 2) ^ 2
/-- `Γ^t_{px} Γ^x_{tt}`, reduced to the common denominator. -/
theorem Qt_t_tp_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_xp * Gx_tt) (⟨Qt_t_tp_n4, Qt_t_tp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_xp, Gx_tt, Qt_t_tp_n4, Qt_t_tp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R^t_{ttp}` (`eq:Riemann`): the signed sum of its terms is the reduced fraction. -/
theorem riemann_t_t_tp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Qt_t_tp_n1 - Qt_t_tp_n2 + Qt_t_tp_n3 - Qt_t_tp_n4, Qt_t_tp_cd⟩)
          (Qt_t_tp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Qt_t_tp_n1, Qt_t_tp_n2, Qt_t_tp_n3, Qt_t_tp_n4, Qt_t_tp_cd, Qt_t_tp, δr_0,
        δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R^t_{trx}` -/

/-- `R^t_{trx}`, reduced. -/
def Qt_t_rx : Frac 6 := ⟨-a ^ 2 * x * (a ^ 2 - d + r ^ 2) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r
    - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v), 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `R^t_{trx}`. -/
def Qt_t_rx_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4

/-- The numerator of `∂_r Γ^t_{xt}` over the common denominator. -/
def Qt_t_rx_n1 : ZExp 6 := 2 * a ^ 2 * d * x * (a ^ 2 * x ^ 2 + r ^ 2) * (2 * a ^ 2 * r * x ^ 2 - 4
    * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v)
/-- `∂_r Γ^t_{xt}`, reduced to the common denominator. -/
theorem Qt_t_rx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (dr_Gt_tx) (⟨Qt_t_rx_n1, Qt_t_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [dr_Gt_tx, Qt_t_rx_n1, Qt_t_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `∂_x Γ^t_{rt}` over the common denominator. -/
def Qt_t_rx_n2 : ZExp 6 := 2 * a ^ 2 * x * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) * (2 * a ^ 2 *
    r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v)
/-- `∂_x Γ^t_{rt}`, reduced to the common denominator. -/
theorem Qt_t_rx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (dx_Gt_tr) (⟨Qt_t_rx_n2, Qt_t_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [dx_Gt_tr, Qt_t_rx_n2, Qt_t_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{rt} Γ^t_{xt}` over the common denominator. -/
def Qt_t_rx_n3 : ZExp 6 := -a ^ 2 * x * (a ^ 2 + r ^ 2) * (a ^ 2 - d + r ^ 2) * (2 * a ^ 2 * r * x
    ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^t_{rt} Γ^t_{xt}`, reduced to the common denominator. -/
theorem Qt_t_rx_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_tr * Gt_tx) (⟨Qt_t_rx_n3, Qt_t_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tr, Gt_tx, Qt_t_rx_n3, Qt_t_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{xt} Γ^t_{rt}` over the common denominator. -/
def Qt_t_rx_n4 : ZExp 6 := -a ^ 2 * x * (a ^ 2 + r ^ 2) * (a ^ 2 - d + r ^ 2) * (2 * a ^ 2 * r * x
    ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^t_{xt} Γ^t_{rt}`, reduced to the common denominator. -/
theorem Qt_t_rx_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_tx * Gt_tr) (⟨Qt_t_rx_n4, Qt_t_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tx, Gt_tr, Qt_t_rx_n4, Qt_t_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{rp} Γ^p_{xt}` over the common denominator. -/
def Qt_t_rx_n5 : ZExp 6 := -a ^ 2 * x * (a ^ 2 - d + r ^ 2) * (2 * a ^ 4 * r + a ^ 4 * v * x ^ 2 -
    2 * a ^ 2 * d * r * x ^ 2 - 2 * a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 + a ^ 2 * r ^ 2 * v * x ^ 2 +
    a ^ 2 * r ^ 2 * v - 4 * d * r ^ 3 + 2 * r ^ 5 + r ^ 4 * v)
/-- `Γ^t_{rp} Γ^p_{xt}`, reduced to the common denominator. -/
theorem Qt_t_rx_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_rp * Gp_tx) (⟨Qt_t_rx_n5, Qt_t_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_rp, Gp_tx, Qt_t_rx_n5, Qt_t_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{xp} Γ^p_{rt}` over the common denominator. -/
def Qt_t_rx_n6 : ZExp 6 := -a ^ 4 * x * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) * (2 * a ^ 2 * r *
    x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^t_{xp} Γ^p_{rt}`, reduced to the common denominator. -/
theorem Qt_t_rx_t6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_xp * Gp_tr) (⟨Qt_t_rx_n6, Qt_t_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_xp, Gp_tr, Qt_t_rx_n6, Qt_t_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R^t_{trx}` (`eq:Riemann`): the signed sum of its terms is the reduced fraction. -/
theorem riemann_t_t_rx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Qt_t_rx_n1 - Qt_t_rx_n2 + Qt_t_rx_n3 - Qt_t_rx_n4 + Qt_t_rx_n5 -
          Qt_t_rx_n6, Qt_t_rx_cd⟩) (Qt_t_rx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Qt_t_rx_n1, Qt_t_rx_n2, Qt_t_rx_n3, Qt_t_rx_n4, Qt_t_rx_n5, Qt_t_rx_n6,
        Qt_t_rx_cd, Qt_t_rx, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R^t_{rtr}` -/

/-- `R^t_{rtr}`, reduced. -/
def Qt_r_tr : Frac 6 := ⟨-a ^ 6 * w * x ^ 4 + 4 * a ^ 6 * x ^ 4 - 4 * a ^ 6 * x ^ 2 - 2 * a ^ 4 * d
    * x ^ 4 + 4 * a ^ 4 * d * x ^ 2 - a ^ 4 * r ^ 2 * w * x ^ 4 - 2 * a ^ 4 * r ^ 2 * w * x ^ 2 + 6
    * a ^ 4 * r ^ 2 * x ^ 4 - 14 * a ^ 4 * r ^ 2 * x ^ 2 + 8 * a ^ 4 * r ^ 2 - a ^ 4 * r * v * x ^
    4 + 5 * a ^ 4 * r * v * x ^ 2 + 4 * a ^ 2 * d * r ^ 2 * x ^ 2 - 8 * a ^ 2 * d * r ^ 2 - 2 * a ^
    2 * r ^ 4 * w * x ^ 2 - a ^ 2 * r ^ 4 * w - 6 * a ^ 2 * r ^ 4 * x ^ 2 + 6 * a ^ 2 * r ^ 4 + 3 *
    a ^ 2 * r ^ 3 * v * x ^ 2 + 5 * a ^ 2 * r ^ 3 * v - 6 * d * r ^ 4 - r ^ 6 * w + 4 * r ^ 5 * v,
    2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `R^t_{rtr}`. -/
def Qt_r_tr_cd : ZExp 6 := 4 * d ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4

/-- The numerator of `∂_r Γ^t_{tr}` over the common denominator. -/
def Qt_r_tr_n1 : ZExp 6 := 2 * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 6 * d * w * x ^ 4 - 2 * a ^ 6 * d * x
    ^ 4 + 2 * a ^ 6 * d * x ^ 2 + 2 * a ^ 6 * r * v * x ^ 4 - 2 * a ^ 6 * r * v * x ^ 2 - a ^ 6 * v
    ^ 2 * x ^ 4 - 2 * a ^ 4 * d ^ 2 * x ^ 2 + a ^ 4 * d * r ^ 2 * w * x ^ 4 + 2 * a ^ 4 * d * r ^ 2
    * w * x ^ 2 - 6 * a ^ 4 * d * r ^ 2 * x ^ 4 + 12 * a ^ 4 * d * r ^ 2 * x ^ 2 - 6 * a ^ 4 * d *
    r ^ 2 + 2 * a ^ 4 * d * r * v * x ^ 4 - 2 * a ^ 4 * d * r * v * x ^ 2 + 2 * a ^ 4 * r ^ 3 * v *
    x ^ 4 - 2 * a ^ 4 * r ^ 3 * v - a ^ 4 * r ^ 2 * v ^ 2 * x ^ 4 - 2 * a ^ 4 * r ^ 2 * v ^ 2 * x ^
    2 - 6 * a ^ 2 * d ^ 2 * r ^ 2 * x ^ 2 + 6 * a ^ 2 * d ^ 2 * r ^ 2 + 2 * a ^ 2 * d * r ^ 4 * w *
    x ^ 2 + a ^ 2 * d * r ^ 4 * w + 2 * a ^ 2 * d * r ^ 4 * x ^ 2 - 2 * a ^ 2 * d * r ^ 4 + 2 * a ^
    2 * d * r ^ 3 * v * x ^ 2 - 2 * a ^ 2 * d * r ^ 3 * v + 2 * a ^ 2 * r ^ 5 * v * x ^ 2 - 2 * a ^
    2 * r ^ 5 * v - 2 * a ^ 2 * r ^ 4 * v ^ 2 * x ^ 2 - a ^ 2 * r ^ 4 * v ^ 2 + 2 * d ^ 2 * r ^ 4 +
    d * r ^ 6 * w - r ^ 6 * v ^ 2)
/-- `∂_r Γ^t_{tr}`, reduced to the common denominator. -/
theorem Qt_r_tr_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (dr_Gt_tr) (⟨Qt_r_tr_n1, Qt_r_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [dr_Gt_tr, Qt_r_tr_n1, Qt_r_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{rt} Γ^t_{tr}` over the common denominator. -/
def Qt_r_tr_n2 : ZExp 6 := (a ^ 2 + r ^ 2) ^ 2 * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v
    * x ^ 2 + 2 * d * r - r ^ 2 * v) ^ 2
/-- `Γ^t_{rt} Γ^t_{tr}`, reduced to the common denominator. -/
theorem Qt_r_tr_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_tr * Gt_tr) (⟨Qt_r_tr_n2, Qt_r_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tr, Qt_r_tr_n2, Qt_r_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1,
        δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{tr} Γ^r_{rr}` over the common denominator. -/
def Qt_r_tr_n3 : ZExp 6 := (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 * v * x ^ 2 - 2 * d *
    r + r ^ 2 * v) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2
    * v)
/-- `Γ^t_{tr} Γ^r_{rr}`, reduced to the common denominator. -/
theorem Qt_r_tr_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_tr * Gr_rr) (⟨Qt_r_tr_n3, Qt_r_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tr, Gr_rr, Qt_r_tr_n3, Qt_r_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{tx} Γ^x_{rr}` over the common denominator. -/
def Qt_r_tr_n4 : ZExp 6 := 4 * a ^ 4 * d * x ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (a
    ^ 2 - d + r ^ 2)
/-- `Γ^t_{tx} Γ^x_{rr}`, reduced to the common denominator. -/
theorem Qt_r_tr_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_tx * Gx_rr) (⟨Qt_r_tr_n4, Qt_r_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tx, Gx_rr, Qt_r_tr_n4, Qt_r_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{rp} Γ^p_{tr}` over the common denominator. -/
def Qt_r_tr_n5 : ZExp 6 := -a ^ 2 * (x - 1) * (x + 1) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a
    ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v) * (2 * a ^ 4 * r + a ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d *
    r * x ^ 2 - 2 * a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 + a ^ 2 * r ^ 2 * v * x ^ 2 + a ^ 2 * r ^ 2 *
    v - 4 * d * r ^ 3 + 2 * r ^ 5 + r ^ 4 * v)
/-- `Γ^t_{rp} Γ^p_{tr}`, reduced to the common denominator. -/
theorem Qt_r_tr_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_rp * Gp_tr) (⟨Qt_r_tr_n5, Qt_r_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_rp, Gp_tr, Qt_r_tr_n5, Qt_r_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R^t_{rtr}` (`eq:Riemann`): the signed sum of its terms is the reduced fraction. -/
theorem riemann_t_r_tr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨0 - Qt_r_tr_n1 - Qt_r_tr_n2 + Qt_r_tr_n3 + Qt_r_tr_n4 - Qt_r_tr_n5,
          Qt_r_tr_cd⟩) (Qt_r_tr))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Qt_r_tr_n1, Qt_r_tr_n2, Qt_r_tr_n3, Qt_r_tr_n4, Qt_r_tr_n5, Qt_r_tr_cd,
        Qt_r_tr, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R^t_{rtx}` -/

/-- `R^t_{rtx}`, reduced. -/
def Qt_r_tx : Frac 6 := ⟨-a ^ 2 * x * (2 * a ^ 2 + d + 2 * r ^ 2) * (2 * a ^ 2 * r * x ^ 2 - 4 * a
    ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v), 2 * d * (a ^ 2 * x ^ 2 + r ^
    2) ^ 3⟩

/-- The common denominator of the terms of `R^t_{rtx}`. -/
def Qt_r_tx_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4

/-- The numerator of `∂_x Γ^t_{tr}` over the common denominator. -/
def Qt_r_tx_n1 : ZExp 6 := 2 * a ^ 2 * x * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) * (2 * a ^ 2 *
    r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v)
/-- `∂_x Γ^t_{tr}`, reduced to the common denominator. -/
theorem Qt_r_tx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (dx_Gt_tr) (⟨Qt_r_tx_n1, Qt_r_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [dx_Gt_tr, Qt_r_tx_n1, Qt_r_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{xt} Γ^t_{tr}` over the common denominator. -/
def Qt_r_tx_n2 : ZExp 6 := -a ^ 2 * x * (a ^ 2 + r ^ 2) * (a ^ 2 - d + r ^ 2) * (2 * a ^ 2 * r * x
    ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^t_{xt} Γ^t_{tr}`, reduced to the common denominator. -/
theorem Qt_r_tx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_tx * Gt_tr) (⟨Qt_r_tx_n2, Qt_r_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tx, Gt_tr, Qt_r_tx_n2, Qt_r_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{tr} Γ^r_{xr}` over the common denominator. -/
def Qt_r_tx_n3 : ZExp 6 := -a ^ 2 * x * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) * (2 * a ^ 2 * r
    * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^t_{tr} Γ^r_{xr}`, reduced to the common denominator. -/
theorem Qt_r_tx_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_tr * Gr_rx) (⟨Qt_r_tx_n3, Qt_r_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tr, Gr_rx, Qt_r_tx_n3, Qt_r_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{tx} Γ^x_{xr}` over the common denominator. -/
def Qt_r_tx_n4 : ZExp 6 := 2 * a ^ 2 * d * r * x * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 - d + r ^ 2)
/-- `Γ^t_{tx} Γ^x_{xr}`, reduced to the common denominator. -/
theorem Qt_r_tx_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_tx * Gx_rx) (⟨Qt_r_tx_n4, Qt_r_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tx, Gx_rx, Qt_r_tx_n4, Qt_r_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{xp} Γ^p_{tr}` over the common denominator. -/
def Qt_r_tx_n5 : ZExp 6 := -a ^ 4 * x * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) * (2 * a ^ 2 * r *
    x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^t_{xp} Γ^p_{tr}`, reduced to the common denominator. -/
theorem Qt_r_tx_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_xp * Gp_tr) (⟨Qt_r_tx_n5, Qt_r_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_xp, Gp_tr, Qt_r_tx_n5, Qt_r_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R^t_{rtx}` (`eq:Riemann`): the signed sum of its terms is the reduced fraction. -/
theorem riemann_t_r_tx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨0 - Qt_r_tx_n1 - Qt_r_tx_n2 + Qt_r_tx_n3 + Qt_r_tx_n4 - Qt_r_tx_n5,
          Qt_r_tx_cd⟩) (Qt_r_tx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Qt_r_tx_n1, Qt_r_tx_n2, Qt_r_tx_n3, Qt_r_tx_n4, Qt_r_tx_n5, Qt_r_tx_cd,
        Qt_r_tx, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R^t_{rrp}` -/

/-- `R^t_{rrp}`, reduced. -/
def Qt_r_rp : Frac 6 := ⟨a * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 4 * w * x ^ 4 - 2 * a ^ 4 *
    x ^ 4 + 4 * a ^ 4 * x ^ 2 - 4 * a ^ 2 * d * x ^ 2 + 2 * a ^ 2 * r ^ 2 * w * x ^ 2 + 10 * a ^ 2
    * r ^ 2 * x ^ 2 - 8 * a ^ 2 * r ^ 2 - 5 * a ^ 2 * r * v * x ^ 2 + 8 * d * r ^ 2 + r ^ 4 * w - 5
    * r ^ 3 * v), 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `R^t_{rrp}`. -/
def Qt_r_rp_cd : ZExp 6 := 4 * d ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4

/-- The numerator of `∂_r Γ^t_{pr}` over the common denominator. -/
def Qt_r_rp_n1 : ZExp 6 := -2 * a * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (-a ^ 6 * d * w *
    x ^ 4 - 2 * a ^ 6 * d * x ^ 2 + 2 * a ^ 6 * r * v * x ^ 2 + a ^ 6 * v ^ 2 * x ^ 4 + 2 * a ^ 4 *
    d ^ 2 * x ^ 4 + 2 * a ^ 4 * d ^ 2 * x ^ 2 - a ^ 4 * d * r ^ 2 * w * x ^ 4 - 2 * a ^ 4 * d * r ^
    2 * w * x ^ 2 - 12 * a ^ 4 * d * r ^ 2 * x ^ 2 + 6 * a ^ 4 * d * r ^ 2 - 2 * a ^ 4 * d * r * v
    * x ^ 4 + 2 * a ^ 4 * d * r * v * x ^ 2 + 4 * a ^ 4 * r ^ 3 * v * x ^ 2 + 2 * a ^ 4 * r ^ 3 * v
    + a ^ 4 * r ^ 2 * v ^ 2 * x ^ 4 + 2 * a ^ 4 * r ^ 2 * v ^ 2 * x ^ 2 + 6 * a ^ 2 * d ^ 2 * r ^ 2
    * x ^ 2 - 6 * a ^ 2 * d ^ 2 * r ^ 2 - 2 * a ^ 2 * d * r ^ 4 * w * x ^ 2 - a ^ 2 * d * r ^ 4 * w
    - 10 * a ^ 2 * d * r ^ 4 * x ^ 2 + 4 * a ^ 2 * d * r ^ 4 - 2 * a ^ 2 * d * r ^ 3 * v * x ^ 2 +
    2 * a ^ 2 * d * r ^ 3 * v + 2 * a ^ 2 * r ^ 5 * v * x ^ 2 + 4 * a ^ 2 * r ^ 5 * v + 2 * a ^ 2 *
    r ^ 4 * v ^ 2 * x ^ 2 + a ^ 2 * r ^ 4 * v ^ 2 - 4 * d ^ 2 * r ^ 4 - d * r ^ 6 * w - 2 * d * r ^
    6 + 2 * r ^ 7 * v + r ^ 6 * v ^ 2)
/-- `∂_r Γ^t_{pr}`, reduced to the common denominator. -/
theorem Qt_r_rp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (dr_Gt_rp) (⟨Qt_r_rp_n1, Qt_r_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [dr_Gt_rp, Qt_r_rp_n1, Qt_r_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{rt} Γ^t_{pr}` over the common denominator. -/
def Qt_r_rp_n2 : ZExp 6 := -a * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (2 * a ^ 2 * r * x ^ 2 - 2 *
    a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v) * (2 * a ^ 4 * r + a ^ 4 * v * x ^ 2 - 2
    * a ^ 2 * d * r * x ^ 2 - 2 * a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 + a ^ 2 * r ^ 2 * v * x ^ 2 + a
    ^ 2 * r ^ 2 * v - 4 * d * r ^ 3 + 2 * r ^ 5 + r ^ 4 * v)
/-- `Γ^t_{rt} Γ^t_{pr}`, reduced to the common denominator. -/
theorem Qt_r_rp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_tr * Gt_rp) (⟨Qt_r_rp_n2, Qt_r_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tr, Gt_rp, Qt_r_rp_n2, Qt_r_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{pr} Γ^r_{rr}` over the common denominator. -/
def Qt_r_rp_n3 : ZExp 6 := -a * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 * v * x ^ 2 -
    2 * d * r + r ^ 2 * v) * (2 * a ^ 4 * r + a ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d * r * x ^ 2 - 2 * a
    ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 + a ^ 2 * r ^ 2 * v * x ^ 2 + a ^ 2 * r ^ 2 * v - 4 * d * r ^ 3
    + 2 * r ^ 5 + r ^ 4 * v)
/-- `Γ^t_{pr} Γ^r_{rr}`, reduced to the common denominator. -/
theorem Qt_r_rp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_rp * Gr_rr) (⟨Qt_r_rp_n3, Qt_r_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_rp, Gr_rr, Qt_r_rp_n3, Qt_r_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{px} Γ^x_{rr}` over the common denominator. -/
def Qt_r_rp_n4 : ZExp 6 := 4 * a ^ 5 * d * x ^ 2 * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * x ^ 2 + r ^
    2) * (a ^ 2 - d + r ^ 2)
/-- `Γ^t_{px} Γ^x_{rr}`, reduced to the common denominator. -/
theorem Qt_r_rp_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_xp * Gx_rr) (⟨Qt_r_rp_n4, Qt_r_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_xp, Gx_rr, Qt_r_rp_n4, Qt_r_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{rp} Γ^p_{pr}` over the common denominator. -/
def Qt_r_rp_n5 : ZExp 6 := a * (x - 1) * (x + 1) * (2 * a ^ 4 * r + a ^ 4 * v * x ^ 2 - 2 * a ^ 2 *
    d * r * x ^ 2 - 2 * a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 + a ^ 2 * r ^ 2 * v * x ^ 2 + a ^ 2 * r ^
    2 * v - 4 * d * r ^ 3 + 2 * r ^ 5 + r ^ 4 * v) * (2 * a ^ 4 * r * x ^ 2 - 2 * a ^ 4 * r + a ^ 4
    * v * x ^ 4 - a ^ 4 * v * x ^ 2 + 2 * a ^ 2 * d * r + 2 * a ^ 2 * r ^ 3 * x ^ 2 - 2 * a ^ 2 * r
    ^ 3 + a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 * v + 2 * d * r ^ 3)
/-- `Γ^t_{rp} Γ^p_{pr}`, reduced to the common denominator. -/
theorem Qt_r_rp_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_rp * Gp_rp) (⟨Qt_r_rp_n5, Qt_r_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_rp, Gp_rp, Qt_r_rp_n5, Qt_r_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R^t_{rrp}` (`eq:Riemann`): the signed sum of its terms is the reduced fraction. -/
theorem riemann_t_r_rp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Qt_r_rp_n1 + Qt_r_rp_n2 - Qt_r_rp_n3 - Qt_r_rp_n4 + Qt_r_rp_n5,
          Qt_r_rp_cd⟩) (Qt_r_rp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Qt_r_rp_n1, Qt_r_rp_n2, Qt_r_rp_n3, Qt_r_rp_n4, Qt_r_rp_n5, Qt_r_rp_cd,
        Qt_r_rp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R^t_{rxp}` -/

/-- `R^t_{rxp}`, reduced. -/
def Qt_r_xp : Frac 6 := ⟨a * x * (-2 * a ^ 4 + a ^ 2 * d * x ^ 2 - a ^ 2 * d - 4 * a ^ 2 * r ^ 2 -
    2 * r ^ 4) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3
    - r ^ 2 * v), 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `R^t_{rxp}`. -/
def Qt_r_xp_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4

/-- The numerator of `∂_x Γ^t_{pr}` over the common denominator. -/
def Qt_r_xp_n1 : ZExp 6 := -2 * a * x * (a ^ 2 + r ^ 2) ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) * (2 * a ^ 2
    * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v)
/-- `∂_x Γ^t_{pr}`, reduced to the common denominator. -/
theorem Qt_r_xp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (dx_Gt_rp) (⟨Qt_r_xp_n1, Qt_r_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [dx_Gt_rp, Qt_r_xp_n1, Qt_r_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{xt} Γ^t_{pr}` over the common denominator. -/
def Qt_r_xp_n2 : ZExp 6 := a ^ 3 * x * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) * (2 * a ^ 4 * r + a
    ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d * r * x ^ 2 - 2 * a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 + a ^ 2 * r
    ^ 2 * v * x ^ 2 + a ^ 2 * r ^ 2 * v - 4 * d * r ^ 3 + 2 * r ^ 5 + r ^ 4 * v)
/-- `Γ^t_{xt} Γ^t_{pr}`, reduced to the common denominator. -/
theorem Qt_r_xp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_tx * Gt_rp) (⟨Qt_r_xp_n2, Qt_r_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tx, Gt_rp, Qt_r_xp_n2, Qt_r_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{pr} Γ^r_{xr}` over the common denominator. -/
def Qt_r_xp_n3 : ZExp 6 := a ^ 3 * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (2 * a ^ 4 * r
    + a ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d * r * x ^ 2 - 2 * a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 + a ^ 2
    * r ^ 2 * v * x ^ 2 + a ^ 2 * r ^ 2 * v - 4 * d * r ^ 3 + 2 * r ^ 5 + r ^ 4 * v)
/-- `Γ^t_{pr} Γ^r_{xr}`, reduced to the common denominator. -/
theorem Qt_r_xp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_rp * Gr_rx) (⟨Qt_r_xp_n3, Qt_r_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_rp, Gr_rx, Qt_r_xp_n3, Qt_r_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{px} Γ^x_{xr}` over the common denominator. -/
def Qt_r_xp_n4 : ZExp 6 := 2 * a ^ 3 * d * r * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (a
    ^ 2 - d + r ^ 2)
/-- `Γ^t_{px} Γ^x_{xr}`, reduced to the common denominator. -/
theorem Qt_r_xp_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_xp * Gx_rx) (⟨Qt_r_xp_n4, Qt_r_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_xp, Gx_rx, Qt_r_xp_n4, Qt_r_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{xp} Γ^p_{pr}` over the common denominator. -/
def Qt_r_xp_n5 : ZExp 6 := a ^ 3 * x * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) * (2 * a ^ 4 * r * x
    ^ 2 - 2 * a ^ 4 * r + a ^ 4 * v * x ^ 4 - a ^ 4 * v * x ^ 2 + 2 * a ^ 2 * d * r + 2 * a ^ 2 * r
    ^ 3 * x ^ 2 - 2 * a ^ 2 * r ^ 3 + a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 * v + 2 * d * r ^ 3)
/-- `Γ^t_{xp} Γ^p_{pr}`, reduced to the common denominator. -/
theorem Qt_r_xp_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_xp * Gp_rp) (⟨Qt_r_xp_n5, Qt_r_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_xp, Gp_rp, Qt_r_xp_n5, Qt_r_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R^t_{rxp}` (`eq:Riemann`): the signed sum of its terms is the reduced fraction. -/
theorem riemann_t_r_xp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Qt_r_xp_n1 + Qt_r_xp_n2 - Qt_r_xp_n3 - Qt_r_xp_n4 + Qt_r_xp_n5,
          Qt_r_xp_cd⟩) (Qt_r_xp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Qt_r_xp_n1, Qt_r_xp_n2, Qt_r_xp_n3, Qt_r_xp_n4, Qt_r_xp_n5, Qt_r_xp_cd,
        Qt_r_xp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R^t_{xtr}` -/

/-- `R^t_{xtr}`, reduced. -/
def Qt_x_tr : Frac 6 := ⟨-a ^ 2 * x * (a ^ 2 + 2 * d + r ^ 2) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2
    * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v), 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^
    3⟩

/-- The common denominator of the terms of `R^t_{xtr}`. -/
def Qt_x_tr_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4

/-- The numerator of `∂_r Γ^t_{tx}` over the common denominator. -/
def Qt_x_tr_n1 : ZExp 6 := 2 * a ^ 2 * d * x * (a ^ 2 * x ^ 2 + r ^ 2) * (2 * a ^ 2 * r * x ^ 2 - 4
    * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v)
/-- `∂_r Γ^t_{tx}`, reduced to the common denominator. -/
theorem Qt_x_tr_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (dr_Gt_tx) (⟨Qt_x_tr_n1, Qt_x_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [dr_Gt_tx, Qt_x_tr_n1, Qt_x_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{rt} Γ^t_{tx}` over the common denominator. -/
def Qt_x_tr_n2 : ZExp 6 := -a ^ 2 * x * (a ^ 2 + r ^ 2) * (a ^ 2 - d + r ^ 2) * (2 * a ^ 2 * r * x
    ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^t_{rt} Γ^t_{tx}`, reduced to the common denominator. -/
theorem Qt_x_tr_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_tr * Gt_tx) (⟨Qt_x_tr_n2, Qt_x_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tr, Gt_tx, Qt_x_tr_n2, Qt_x_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{tr} Γ^r_{rx}` over the common denominator. -/
def Qt_x_tr_n3 : ZExp 6 := -a ^ 2 * x * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) * (2 * a ^ 2 * r
    * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^t_{tr} Γ^r_{rx}`, reduced to the common denominator. -/
theorem Qt_x_tr_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_tr * Gr_rx) (⟨Qt_x_tr_n3, Qt_x_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tr, Gr_rx, Qt_x_tr_n3, Qt_x_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{tx} Γ^x_{rx}` over the common denominator. -/
def Qt_x_tr_n4 : ZExp 6 := 2 * a ^ 2 * d * r * x * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 - d + r ^ 2)
/-- `Γ^t_{tx} Γ^x_{rx}`, reduced to the common denominator. -/
theorem Qt_x_tr_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_tx * Gx_rx) (⟨Qt_x_tr_n4, Qt_x_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tx, Gx_rx, Qt_x_tr_n4, Qt_x_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{rp} Γ^p_{tx}` over the common denominator. -/
def Qt_x_tr_n5 : ZExp 6 := -a ^ 2 * x * (a ^ 2 - d + r ^ 2) * (2 * a ^ 4 * r + a ^ 4 * v * x ^ 2 -
    2 * a ^ 2 * d * r * x ^ 2 - 2 * a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 + a ^ 2 * r ^ 2 * v * x ^ 2 +
    a ^ 2 * r ^ 2 * v - 4 * d * r ^ 3 + 2 * r ^ 5 + r ^ 4 * v)
/-- `Γ^t_{rp} Γ^p_{tx}`, reduced to the common denominator. -/
theorem Qt_x_tr_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_rp * Gp_tx) (⟨Qt_x_tr_n5, Qt_x_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_rp, Gp_tx, Qt_x_tr_n5, Qt_x_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R^t_{xtr}` (`eq:Riemann`): the signed sum of its terms is the reduced fraction. -/
theorem riemann_t_x_tr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨0 - Qt_x_tr_n1 - Qt_x_tr_n2 + Qt_x_tr_n3 + Qt_x_tr_n4 - Qt_x_tr_n5,
          Qt_x_tr_cd⟩) (Qt_x_tr))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Qt_x_tr_n1, Qt_x_tr_n2, Qt_x_tr_n3, Qt_x_tr_n4, Qt_x_tr_n5, Qt_x_tr_cd,
        Qt_x_tr, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R^t_{xtx}` -/

/-- `R^t_{xtx}`, reduced. -/
def Qt_x_tx : Frac 6 := ⟨6 * a ^ 6 * x ^ 4 - 8 * a ^ 6 * x ^ 2 - 6 * a ^ 4 * d * x ^ 4 + 8 * a ^ 4
    * d * x ^ 2 + 6 * a ^ 4 * r ^ 2 * x ^ 4 - 14 * a ^ 4 * r ^ 2 * x ^ 2 + 4 * a ^ 4 * r ^ 2 + a ^
    4 * r * v * x ^ 2 + 4 * a ^ 2 * d * r ^ 2 * x ^ 2 - 4 * a ^ 2 * d * r ^ 2 - 6 * a ^ 2 * r ^ 4 *
    x ^ 2 + 4 * a ^ 2 * r ^ 4 + a ^ 2 * r ^ 3 * v * x ^ 2 + a ^ 2 * r ^ 3 * v - 2 * d * r ^ 4 + r ^
    5 * v, 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `R^t_{xtx}`. -/
def Qt_x_tx_cd : ZExp 6 := 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4

/-- The numerator of `∂_x Γ^t_{tx}` over the common denominator. -/
def Qt_x_tx_n1 : ZExp 6 := -2 * a ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (3 * a ^ 2 *
    x ^ 2 - r ^ 2) * (a ^ 2 - d + r ^ 2)
/-- `∂_x Γ^t_{tx}`, reduced to the common denominator. -/
theorem Qt_x_tx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (dx_Gt_tx) (⟨Qt_x_tx_n1, Qt_x_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [dx_Gt_tx, Qt_x_tx_n1, Qt_x_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{xt} Γ^t_{tx}` over the common denominator. -/
def Qt_x_tx_n2 : ZExp 6 := 2 * a ^ 4 * x ^ 2 * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) ^ 2
/-- `Γ^t_{xt} Γ^t_{tx}`, reduced to the common denominator. -/
theorem Qt_x_tx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_tx * Gt_tx) (⟨Qt_x_tx_n2, Qt_x_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tx, Qt_x_tx_n2, Qt_x_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1,
        δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{tr} Γ^r_{xx}` over the common denominator. -/
def Qt_x_tx_n3 : ZExp 6 := -r * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) * (2 * a ^ 2 * r * x ^ 2
    - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^t_{tr} Γ^r_{xx}`, reduced to the common denominator. -/
theorem Qt_x_tx_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_tr * Gr_xx) (⟨Qt_x_tx_n3, Qt_x_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tr, Gr_xx, Qt_x_tx_n3, Qt_x_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{tx} Γ^x_{xx}` over the common denominator. -/
def Qt_x_tx_n4 : ZExp 6 := -2 * a ^ 2 * x ^ 2 * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2
    - d + r ^ 2)
/-- `Γ^t_{tx} Γ^x_{xx}`, reduced to the common denominator. -/
theorem Qt_x_tx_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_tx * Gx_xx) (⟨Qt_x_tx_n4, Qt_x_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tx, Gx_xx, Qt_x_tx_n4, Qt_x_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{xp} Γ^p_{tx}` over the common denominator. -/
def Qt_x_tx_n5 : ZExp 6 := -2 * a ^ 4 * x ^ 2 * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) ^ 2
/-- `Γ^t_{xp} Γ^p_{tx}`, reduced to the common denominator. -/
theorem Qt_x_tx_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_xp * Gp_tx) (⟨Qt_x_tx_n5, Qt_x_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_xp, Gp_tx, Qt_x_tx_n5, Qt_x_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R^t_{xtx}` (`eq:Riemann`): the signed sum of its terms is the reduced fraction. -/
theorem riemann_t_x_tx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨0 - Qt_x_tx_n1 - Qt_x_tx_n2 + Qt_x_tx_n3 + Qt_x_tx_n4 - Qt_x_tx_n5,
          Qt_x_tx_cd⟩) (Qt_x_tx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Qt_x_tx_n1, Qt_x_tx_n2, Qt_x_tx_n3, Qt_x_tx_n4, Qt_x_tx_n5, Qt_x_tx_cd,
        Qt_x_tx, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R^t_{xrp}` -/

/-- `R^t_{xrp}`, reduced. -/
def Qt_x_rp : Frac 6 := ⟨a * x * (-a ^ 4 + 2 * a ^ 2 * d * x ^ 2 - 2 * a ^ 2 * d - 2 * a ^ 2 * r ^
    2 - r ^ 4) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3
    - r ^ 2 * v), 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `R^t_{xrp}`. -/
def Qt_x_rp_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4

/-- The numerator of `∂_r Γ^t_{px}` over the common denominator. -/
def Qt_x_rp_n1 : ZExp 6 := 2 * a ^ 3 * d * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (2 * a
    ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v)
/-- `∂_r Γ^t_{px}`, reduced to the common denominator. -/
theorem Qt_x_rp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (dr_Gt_xp) (⟨Qt_x_rp_n1, Qt_x_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [dr_Gt_xp, Qt_x_rp_n1, Qt_x_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{rt} Γ^t_{px}` over the common denominator. -/
def Qt_x_rp_n2 : ZExp 6 := -a ^ 3 * x * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) *
    (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^t_{rt} Γ^t_{px}`, reduced to the common denominator. -/
theorem Qt_x_rp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_tr * Gt_xp) (⟨Qt_x_rp_n2, Qt_x_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tr, Gt_xp, Qt_x_rp_n2, Qt_x_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{pr} Γ^r_{rx}` over the common denominator. -/
def Qt_x_rp_n3 : ZExp 6 := a ^ 3 * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (2 * a ^ 4 * r
    + a ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d * r * x ^ 2 - 2 * a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 + a ^ 2
    * r ^ 2 * v * x ^ 2 + a ^ 2 * r ^ 2 * v - 4 * d * r ^ 3 + 2 * r ^ 5 + r ^ 4 * v)
/-- `Γ^t_{pr} Γ^r_{rx}`, reduced to the common denominator. -/
theorem Qt_x_rp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_rp * Gr_rx) (⟨Qt_x_rp_n3, Qt_x_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_rp, Gr_rx, Qt_x_rp_n3, Qt_x_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{px} Γ^x_{rx}` over the common denominator. -/
def Qt_x_rp_n4 : ZExp 6 := 2 * a ^ 3 * d * r * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (a
    ^ 2 - d + r ^ 2)
/-- `Γ^t_{px} Γ^x_{rx}`, reduced to the common denominator. -/
theorem Qt_x_rp_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_xp * Gx_rx) (⟨Qt_x_rp_n4, Qt_x_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_xp, Gx_rx, Qt_x_rp_n4, Qt_x_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{rp} Γ^p_{px}` over the common denominator. -/
def Qt_x_rp_n5 : ZExp 6 := a * x * (a ^ 4 * x ^ 4 - a ^ 4 * x ^ 2 + a ^ 4 + a ^ 2 * d * x ^ 2 - a ^
    2 * d + a ^ 2 * r ^ 2 * x ^ 2 + a ^ 2 * r ^ 2 + r ^ 4) * (2 * a ^ 4 * r + a ^ 4 * v * x ^ 2 - 2
    * a ^ 2 * d * r * x ^ 2 - 2 * a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 + a ^ 2 * r ^ 2 * v * x ^ 2 + a
    ^ 2 * r ^ 2 * v - 4 * d * r ^ 3 + 2 * r ^ 5 + r ^ 4 * v)
/-- `Γ^t_{rp} Γ^p_{px}`, reduced to the common denominator. -/
theorem Qt_x_rp_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_rp * Gp_xp) (⟨Qt_x_rp_n5, Qt_x_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_rp, Gp_xp, Qt_x_rp_n5, Qt_x_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R^t_{xrp}` (`eq:Riemann`): the signed sum of its terms is the reduced fraction. -/
theorem riemann_t_x_rp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Qt_x_rp_n1 + Qt_x_rp_n2 - Qt_x_rp_n3 - Qt_x_rp_n4 + Qt_x_rp_n5,
          Qt_x_rp_cd⟩) (Qt_x_rp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Qt_x_rp_n1, Qt_x_rp_n2, Qt_x_rp_n3, Qt_x_rp_n4, Qt_x_rp_n5, Qt_x_rp_cd,
        Qt_x_rp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R^t_{xxp}` -/

/-- `R^t_{xxp}`, reduced. -/
def Qt_x_xp : Frac 6 := ⟨a * (a ^ 2 + r ^ 2) * (8 * a ^ 4 * x ^ 2 - 8 * a ^ 2 * d * x ^ 2 + 10 * a
    ^ 2 * r ^ 2 * x ^ 2 - 4 * a ^ 2 * r ^ 2 - a ^ 2 * r * v * x ^ 2 + 4 * d * r ^ 2 - 2 * r ^ 4 - r
    ^ 3 * v), 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `R^t_{xxp}`. -/
def Qt_x_xp_cd : ZExp 6 := 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4

/-- The numerator of `∂_x Γ^t_{px}` over the common denominator. -/
def Qt_x_xp_n1 : ZExp 6 := -2 * a ^ 3 * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 - d + r ^ 2) * (a ^ 2 * x
    ^ 4 - 3 * a ^ 2 * x ^ 2 - 3 * r ^ 2 * x ^ 2 + r ^ 2)
/-- `∂_x Γ^t_{px}`, reduced to the common denominator. -/
theorem Qt_x_xp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (dx_Gt_xp) (⟨Qt_x_xp_n1, Qt_x_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [dx_Gt_xp, Qt_x_xp_n1, Qt_x_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{xt} Γ^t_{px}` over the common denominator. -/
def Qt_x_xp_n2 : ZExp 6 := 2 * a ^ 5 * x ^ 2 * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) ^ 2
/-- `Γ^t_{xt} Γ^t_{px}`, reduced to the common denominator. -/
theorem Qt_x_xp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_tx * Gt_xp) (⟨Qt_x_xp_n2, Qt_x_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tx, Gt_xp, Qt_x_xp_n2, Qt_x_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{pr} Γ^r_{xx}` over the common denominator. -/
def Qt_x_xp_n3 : ZExp 6 := a * r * (a ^ 2 * x ^ 2 + r ^ 2) * (2 * a ^ 4 * r + a ^ 4 * v * x ^ 2 - 2
    * a ^ 2 * d * r * x ^ 2 - 2 * a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 + a ^ 2 * r ^ 2 * v * x ^ 2 + a
    ^ 2 * r ^ 2 * v - 4 * d * r ^ 3 + 2 * r ^ 5 + r ^ 4 * v)
/-- `Γ^t_{pr} Γ^r_{xx}`, reduced to the common denominator. -/
theorem Qt_x_xp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_rp * Gr_xx) (⟨Qt_x_xp_n3, Qt_x_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_rp, Gr_xx, Qt_x_xp_n3, Qt_x_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{px} Γ^x_{xx}` over the common denominator. -/
def Qt_x_xp_n4 : ZExp 6 := -2 * a ^ 3 * x ^ 2 * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2
    - d + r ^ 2)
/-- `Γ^t_{px} Γ^x_{xx}`, reduced to the common denominator. -/
theorem Qt_x_xp_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_xp * Gx_xx) (⟨Qt_x_xp_n4, Qt_x_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_xp, Gx_xx, Qt_x_xp_n4, Qt_x_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{xp} Γ^p_{px}` over the common denominator. -/
def Qt_x_xp_n5 : ZExp 6 := 2 * a ^ 3 * x ^ 2 * (a ^ 2 - d + r ^ 2) * (a ^ 4 * x ^ 4 - a ^ 4 * x ^ 2
    + a ^ 4 + a ^ 2 * d * x ^ 2 - a ^ 2 * d + a ^ 2 * r ^ 2 * x ^ 2 + a ^ 2 * r ^ 2 + r ^ 4)
/-- `Γ^t_{xp} Γ^p_{px}`, reduced to the common denominator. -/
theorem Qt_x_xp_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_xp * Gp_xp) (⟨Qt_x_xp_n5, Qt_x_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_xp, Gp_xp, Qt_x_xp_n5, Qt_x_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R^t_{xxp}` (`eq:Riemann`): the signed sum of its terms is the reduced fraction. -/
theorem riemann_t_x_xp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Qt_x_xp_n1 + Qt_x_xp_n2 - Qt_x_xp_n3 - Qt_x_xp_n4 + Qt_x_xp_n5,
          Qt_x_xp_cd⟩) (Qt_x_xp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Qt_x_xp_n1, Qt_x_xp_n2, Qt_x_xp_n3, Qt_x_xp_n4, Qt_x_xp_n5, Qt_x_xp_cd,
        Qt_x_xp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R^t_{ptp}` -/

/-- `R^t_{ptp}`, reduced. -/
def Qt_p_tp : Frac 6 := ⟨-(x - 1) * (x + 1) * (a ^ 4 + a ^ 2 * d * x ^ 2 - a ^ 2 * d + 2 * a ^ 2 *
    r ^ 2 + r ^ 4) * (2 * a ^ 4 * x ^ 2 - 2 * a ^ 2 * d * x ^ 2 + 4 * a ^ 2 * r ^ 2 * x ^ 2 - 2 * a
    ^ 2 * r ^ 2 - a ^ 2 * r * v * x ^ 2 + 2 * d * r ^ 2 - r ^ 3 * v), 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^
    4⟩

/-- The common denominator of the terms of `R^t_{ptp}`. -/
def Qt_p_tp_cd : ZExp 6 := 4 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `Γ^t_{tr} Γ^r_{pp}` over the common denominator. -/
def Qt_p_tp_n1 : ZExp 6 := -(a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^
    2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v) * (4 * a ^ 4 * r * x ^ 2 - 2 * a ^ 4 * r + a
    ^ 4 * v * x ^ 4 - a ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d * r * x ^ 2 + 2 * a ^ 2 * d * r + 4 * a ^ 2
    * r ^ 3 * x ^ 2 + a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 * v + 2 * r ^ 5)
/-- `Γ^t_{tr} Γ^r_{pp}`, reduced to the common denominator. -/
theorem Qt_p_tp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_tr * Gr_pp) (⟨Qt_p_tp_n1, Qt_p_tp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tr, Gr_pp, Qt_p_tp_n1, Qt_p_tp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{pr} Γ^r_{tp}` over the common denominator. -/
def Qt_p_tp_n2 : ZExp 6 := -a ^ 2 * (x - 1) ^ 2 * (x + 1) ^ 2 * (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2
    * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v) * (2 * a ^ 4 * r + a ^ 4 * v * x ^ 2 - 2 * a ^
    2 * d * r * x ^ 2 - 2 * a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 + a ^ 2 * r ^ 2 * v * x ^ 2 + a ^ 2 *
    r ^ 2 * v - 4 * d * r ^ 3 + 2 * r ^ 5 + r ^ 4 * v)
/-- `Γ^t_{pr} Γ^r_{tp}`, reduced to the common denominator. -/
theorem Qt_p_tp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_rp * Gr_tp) (⟨Qt_p_tp_n2, Qt_p_tp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_rp, Gr_tp, Qt_p_tp_n2, Qt_p_tp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{tx} Γ^x_{pp}` over the common denominator. -/
def Qt_p_tp_n3 : ZExp 6 := -4 * a ^ 2 * x ^ 2 * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) * (a ^ 6 +
    a ^ 4 * d * x ^ 4 - a ^ 4 * d + 3 * a ^ 4 * r ^ 2 + 2 * a ^ 2 * d * r ^ 2 * x ^ 2 - 2 * a ^ 2 *
    d * r ^ 2 + 3 * a ^ 2 * r ^ 4 + r ^ 6)
/-- `Γ^t_{tx} Γ^x_{pp}`, reduced to the common denominator. -/
theorem Qt_p_tp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_tx * Gx_pp) (⟨Qt_p_tp_n3, Qt_p_tp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tx, Gx_pp, Qt_p_tp_n3, Qt_p_tp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{px} Γ^x_{tp}` over the common denominator. -/
def Qt_p_tp_n4 : ZExp 6 := 4 * a ^ 4 * x ^ 2 * (a ^ 2 + r ^ 2) * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2
    - d + r ^ 2) ^ 2
/-- `Γ^t_{px} Γ^x_{tp}`, reduced to the common denominator. -/
theorem Qt_p_tp_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_xp * Gx_tp) (⟨Qt_p_tp_n4, Qt_p_tp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_xp, Gx_tp, Qt_p_tp_n4, Qt_p_tp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R^t_{ptp}` (`eq:Riemann`): the signed sum of its terms is the reduced fraction. -/
theorem riemann_t_p_tp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Qt_p_tp_n1 - Qt_p_tp_n2 + Qt_p_tp_n3 - Qt_p_tp_n4, Qt_p_tp_cd⟩)
          (Qt_p_tp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Qt_p_tp_n1, Qt_p_tp_n2, Qt_p_tp_n3, Qt_p_tp_n4, Qt_p_tp_cd, Qt_p_tp, δr_0,
        δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `R^t_{prx}` -/

/-- `R^t_{prx}`, reduced. -/
def Qt_p_rx : Frac 6 := ⟨a * x * (a ^ 4 + a ^ 2 * d * x ^ 2 - a ^ 2 * d + 2 * a ^ 2 * r ^ 2 + r ^
    4) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2
    * v), 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `R^t_{prx}`. -/
def Qt_p_rx_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4

/-- The numerator of `∂_r Γ^t_{xp}` over the common denominator. -/
def Qt_p_rx_n1 : ZExp 6 := 2 * a ^ 3 * d * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (2 * a
    ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v)
/-- `∂_r Γ^t_{xp}`, reduced to the common denominator. -/
theorem Qt_p_rx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (dr_Gt_xp) (⟨Qt_p_rx_n1, Qt_p_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [dr_Gt_xp, Qt_p_rx_n1, Qt_p_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `∂_x Γ^t_{rp}` over the common denominator. -/
def Qt_p_rx_n2 : ZExp 6 := -2 * a * x * (a ^ 2 + r ^ 2) ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) * (2 * a ^ 2
    * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v)
/-- `∂_x Γ^t_{rp}`, reduced to the common denominator. -/
theorem Qt_p_rx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (dx_Gt_rp) (⟨Qt_p_rx_n2, Qt_p_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [dx_Gt_rp, Qt_p_rx_n2, Qt_p_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{rt} Γ^t_{xp}` over the common denominator. -/
def Qt_p_rx_n3 : ZExp 6 := -a ^ 3 * x * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) *
    (2 * a ^ 2 * r * x ^ 2 - 2 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 2 * d * r - r ^ 2 * v)
/-- `Γ^t_{rt} Γ^t_{xp}`, reduced to the common denominator. -/
theorem Qt_p_rx_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_tr * Gt_xp) (⟨Qt_p_rx_n3, Qt_p_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tr, Gt_xp, Qt_p_rx_n3, Qt_p_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{xt} Γ^t_{rp}` over the common denominator. -/
def Qt_p_rx_n4 : ZExp 6 := a ^ 3 * x * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) * (2 * a ^ 4 * r + a
    ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d * r * x ^ 2 - 2 * a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 + a ^ 2 * r
    ^ 2 * v * x ^ 2 + a ^ 2 * r ^ 2 * v - 4 * d * r ^ 3 + 2 * r ^ 5 + r ^ 4 * v)
/-- `Γ^t_{xt} Γ^t_{rp}`, reduced to the common denominator. -/
theorem Qt_p_rx_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_tx * Gt_rp) (⟨Qt_p_rx_n4, Qt_p_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tx, Gt_rp, Qt_p_rx_n4, Qt_p_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{rp} Γ^p_{xp}` over the common denominator. -/
def Qt_p_rx_n5 : ZExp 6 := a * x * (a ^ 4 * x ^ 4 - a ^ 4 * x ^ 2 + a ^ 4 + a ^ 2 * d * x ^ 2 - a ^
    2 * d + a ^ 2 * r ^ 2 * x ^ 2 + a ^ 2 * r ^ 2 + r ^ 4) * (2 * a ^ 4 * r + a ^ 4 * v * x ^ 2 - 2
    * a ^ 2 * d * r * x ^ 2 - 2 * a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 + a ^ 2 * r ^ 2 * v * x ^ 2 + a
    ^ 2 * r ^ 2 * v - 4 * d * r ^ 3 + 2 * r ^ 5 + r ^ 4 * v)
/-- `Γ^t_{rp} Γ^p_{xp}`, reduced to the common denominator. -/
theorem Qt_p_rx_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_rp * Gp_xp) (⟨Qt_p_rx_n5, Qt_p_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_rp, Gp_xp, Qt_p_rx_n5, Qt_p_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `Γ^t_{xp} Γ^p_{rp}` over the common denominator. -/
def Qt_p_rx_n6 : ZExp 6 := a ^ 3 * x * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) * (2 * a ^ 4 * r * x
    ^ 2 - 2 * a ^ 4 * r + a ^ 4 * v * x ^ 4 - a ^ 4 * v * x ^ 2 + 2 * a ^ 2 * d * r + 2 * a ^ 2 * r
    ^ 3 * x ^ 2 - 2 * a ^ 2 * r ^ 3 + a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 * v + 2 * d * r ^ 3)
/-- `Γ^t_{xp} Γ^p_{rp}`, reduced to the common denominator. -/
theorem Qt_p_rx_t6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Gt_xp * Gp_rp) (⟨Qt_p_rx_n6, Qt_p_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_xp, Gp_rp, Qt_p_rx_n6, Qt_p_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `R^t_{prx}` (`eq:Riemann`): the signed sum of its terms is the reduced fraction. -/
theorem riemann_t_p_rx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨Qt_p_rx_n1 - Qt_p_rx_n2 + Qt_p_rx_n3 - Qt_p_rx_n4 + Qt_p_rx_n5 -
          Qt_p_rx_n6, Qt_p_rx_cd⟩) (Qt_p_rx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Qt_p_rx_n1, Qt_p_rx_n2, Qt_p_rx_n3, Qt_p_rx_n4, Qt_p_rx_n5, Qt_p_rx_n6,
        Qt_p_rx_cd, Qt_p_rx, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

end LeanProofs.IPRA.Geometry.KerrNewmanRiemannT
