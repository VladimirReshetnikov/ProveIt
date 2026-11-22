import IPRADerivations.Geometry.KerrNewmanPairProductA
import IPRADerivations.Geometry.KerrNewmanPairProductB

/-!
# The row `xp` of the trace `tr(C J C J)` (`four_metrics_ipra`)

Packet: `geometry/four_metrics_ipra_2026-11-15`, `eq:paircontract` (`𝒦 = 4 tr(C J C J)`). With the
product `M = C J` of `Geometry/KerrNewmanPairProductA`, `…B` (radial function `d`, Boyer–Lindquist
coordinates, index `p` for `φ`), for the pair `I = xp`: `row_I` with `P_I_tn` certifies the row sum
`P_I = Σ_K M_{IK} M_{KI}` of `tr(M M)` as a reduced fraction, each product reduced over the row's
common denominator. Summing the rows (`Geometry/KerrNewmanKretschmann`) instead of all the
products at once keeps every cleared identity small.

The reduced fractions and numerators were proposed by a computer algebra script; every identity
is checked by Lean as an identity of fractions cleared of denominators, a closed sentence of iPRA
certified in every commutative ring.
-/

namespace LeanProofs.IPRA.Geometry.KerrNewmanTraceRowXP

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Geometry.KerrNewmanBase (δr δx δr_0 δr_1 δr_2 δr_3 δr_4 δr_5 δx_0 δx_1 δx_2
  δx_3 δx_4 δx_5 Sg sx)
open LeanProofs.IPRA.Geometry.KerrNewmanConnection
open LeanProofs.IPRA.Geometry.KerrNewmanRiemannT
open LeanProofs.IPRA.Geometry.KerrNewmanRiemannR
open LeanProofs.IPRA.Geometry.KerrNewmanRiemannX
open LeanProofs.IPRA.Geometry.KerrNewmanRiemannP
open LeanProofs.IPRA.Geometry.KerrNewmanPairMatrix
open LeanProofs.IPRA.Geometry.KerrNewmanPairProductA
open LeanProofs.IPRA.Geometry.KerrNewmanPairProductB
open ZExp

local notation "r" => (ZExp.var 0 : ZExp 6)
local notation "x" => (ZExp.var 1 : ZExp 6)
local notation "a" => (ZExp.var 2 : ZExp 6)
local notation "d" => (ZExp.var 3 : ZExp 6)
local notation "v" => (ZExp.var 4 : ZExp 6)
local notation "w" => (ZExp.var 5 : ZExp 6)

/-! ### The row `xp` -/

set_option maxHeartbeats 4000000 in
def P_xp_c1 : ZExp 6 := 4 * a ^ 10 * x ^ 6
    + 32 * a ^ 10 * x ^ 4 - 8 * a ^ 8 * d * x ^ 6 - 64 * a ^ 8 * d * x ^ 4
    - 4 * a ^ 8 * r ^ 2 * x ^ 8 + 20 * a ^ 8 * r ^ 2 * x ^ 6
    + 116 * a ^ 8 * r ^ 2 * x ^ 4 - 64 * a ^ 8 * r ^ 2 * x ^ 2
    + 4 * a ^ 8 * r * v * x ^ 8 - 20 * a ^ 8 * r * v * x ^ 4 - a ^ 8 * v ^ 2 * x ^ 8
    - 3 * a ^ 8 * v ^ 2 * x ^ 6 + 4 * a ^ 6 * d ^ 2 * x ^ 6
    + 32 * a ^ 6 * d ^ 2 * x ^ 4 - 32 * a ^ 6 * d * r ^ 2 * x ^ 6 - 128 * a ^ 6 * d * r ^ 2 * x ^ 4

set_option maxHeartbeats 4000000 in
def P_xp_c2 : ZExp 6 := 128 * a ^ 6 * d * r ^ 2 * x ^ 2 + 12 * a ^ 6 * d * r * v * x ^ 6
    + 20 * a ^ 6 * d * r * v * x ^ 4 + 8 * a ^ 6 * r ^ 4 * x ^ 6
    + 148 * a ^ 6 * r ^ 4 * x ^ 4 - 164 * a ^ 6 * r ^ 4 * x ^ 2
    + 8 * a ^ 6 * r ^ 3 * v * x ^ 6 - 32 * a ^ 6 * r ^ 3 * v * x ^ 4
    - 24 * a ^ 6 * r ^ 3 * v * x ^ 2 - 5 * a ^ 6 * r ^ 2 * v ^ 2 * x ^ 6
    - 7 * a ^ 6 * r ^ 2 * v ^ 2 * x ^ 4
    + 12 * a ^ 4 * d ^ 2 * r ^ 2 * x ^ 4 - 64 * a ^ 4 * d ^ 2 * r ^ 2 * x ^ 2

set_option maxHeartbeats 4000000 in
def P_xp_c3 : ZExp 6 := 104 * a ^ 4 * d * r ^ 4 * x ^ 4 - 248 * a ^ 4 * d * r ^ 4 * x ^ 2
    - 40 * a ^ 4 * d * r ^ 3 * v * x ^ 4 - 24 * a ^ 4 * d * r ^ 3 * v * x ^ 2
    - 64 * a ^ 4 * r ^ 6 * x ^ 4 + 148 * a ^ 4 * r ^ 6 * x ^ 2 - 12 * a ^ 4 * r ^ 6
    + 12 * a ^ 4 * r ^ 5 * v * x ^ 4 + 32 * a ^ 4 * r ^ 5 * v * x ^ 2 + 4 * a ^ 4 * r ^ 5 * v
    + 7 * a ^ 4 * r ^ 4 * v ^ 2 * x ^ 4 + 5 * a ^ 4 * r ^ 4 * v ^ 2 * x ^ 2
    + 84 * a ^ 2 * d ^ 2 * r ^ 4 * x ^ 2

set_option maxHeartbeats 4000000 in
def P_xp_c4 : ZExp 6 := 112 * a ^ 2 * d * r ^ 6 * x ^ 2 - 16 * a ^ 2 * d * r ^ 6
    + 28 * a ^ 2 * d * r ^ 5 * v * x ^ 2 + 4 * a ^ 2 * d * r ^ 5 * v - 40 * a ^ 2 * r ^ 8 * x ^ 2
    + 12 * a ^ 2 * r ^ 8 - 16 * a ^ 2 * r ^ 7 * v * x ^ 2 - 3 * a ^ 2 * r ^ 6 * v ^ 2 * x ^ 2
    - a ^ 2 * r ^ 6 * v ^ 2 + 4 * d ^ 2 * r ^ 6 - 8 * d * r ^ 8 + 4 * r ^ 10

set_option maxHeartbeats 4000000 in
/-- `Σ_K M_{xp,K} M_{K,xp}`, reduced. -/
def P_xp : Frac 6 := ⟨P_xp_c1 + P_xp_c2 - P_xp_c3 + P_xp_c4, 4 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 7⟩

/-- The common denominator of the terms of the row `xp` of `tr(M M)`. -/
def P_xp_cd : ZExp 6 := 4 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 8

/-- The numerator of `M_{xp,tr} M_{tr,xp}` over the common denominator. -/
def P_xp_n1 : ZExp 6 := -a ^ 2 * x ^ 2 * (a ^ 2 * x ^ 2 - a ^ 2 - 2 * d) * (-2 * a ^ 4 + a ^ 2 * d
    * x ^ 2 - a ^ 2 * d - 4 * a ^ 2 * r ^ 2 - 2 * r ^ 4) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r -
    a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v) ^ 2
/-- `M_{xp,tr} M_{tr,xp}`, reduced to the common denominator. -/
theorem P_xp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (M_xp_tr * M_tr_xp) (⟨P_xp_n1, P_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [M_xp_tr, M_tr_xp, P_xp_n1, P_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `M_{xp,tx} M_{tx,xp}` over the common denominator. -/
def P_xp_n2 : ZExp 6 := a ^ 2 * d * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (8 * a ^ 4 * x ^ 2 - 8 *
    a ^ 2 * d * x ^ 2 + 10 * a ^ 2 * r ^ 2 * x ^ 2 - 4 * a ^ 2 * r ^ 2 - a ^ 2 * r * v * x ^ 2 + 4
    * d * r ^ 2 - 2 * r ^ 4 - r ^ 3 * v) ^ 2
/-- `M_{xp,tx} M_{tx,xp}`, reduced to the common denominator. -/
theorem P_xp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (M_xp_tx * M_tx_xp) (⟨P_xp_n2, P_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [M_xp_tx, M_tx_xp, P_xp_n2, P_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `M_{xp,rp} M_{rp,xp}` over the common denominator. -/
def P_xp_n3 : ZExp 6 := -a ^ 4 * x ^ 2 * (x - 1) * (x + 1) * (a ^ 2 + 2 * d + r ^ 2) * (2 * a ^ 2 +
    d + 2 * r ^ 2) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r
    ^ 3 - r ^ 2 * v) ^ 2
/-- `M_{xp,rp} M_{rp,xp}`, reduced to the common denominator. -/
theorem P_xp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (M_xp_rp * M_rp_xp) (⟨P_xp_n3, P_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [M_xp_rp, M_rp_xp, P_xp_n3, P_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `M_{xp,xp} M_{xp,xp}` over the common denominator. -/
def P_xp_n4 : ZExp 6 := d * (2 * a ^ 6 * x ^ 4 - 8 * a ^ 6 * x ^ 2 - 2 * a ^ 4 * d * x ^ 4 + 8 * a
    ^ 4 * d * x ^ 2 + 4 * a ^ 4 * r ^ 2 * x ^ 4 - 18 * a ^ 4 * r ^ 2 * x ^ 2 + 4 * a ^ 4 * r ^ 2 -
    a ^ 4 * r * v * x ^ 4 + a ^ 4 * r * v * x ^ 2 + 8 * a ^ 2 * d * r ^ 2 * x ^ 2 - 4 * a ^ 2 * d *
    r ^ 2 - 6 * a ^ 2 * r ^ 4 * x ^ 2 + 4 * a ^ 2 * r ^ 4 - a ^ 2 * r ^ 3 * v * x ^ 2 + a ^ 2 * r ^
    3 * v - 2 * d * r ^ 4 + 2 * r ^ 6) ^ 2
/-- `M_{xp,xp} M_{xp,xp}`, reduced to the common denominator. -/
theorem P_xp_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (M_xp_xp * M_xp_xp) (⟨P_xp_n4, P_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [M_xp_xp, P_xp_n4, P_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1,
        δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The row `xp` of `tr(M M)`: `Σ_K M_{xp,K} M_{K,xp}` is the reduced fraction. -/
theorem row_xp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨P_xp_n1 + P_xp_n2 + P_xp_n3 + P_xp_n4, P_xp_cd⟩) (P_xp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [P_xp_n1, P_xp_n2, P_xp_n3, P_xp_n4, P_xp_cd, P_xp, P_xp_c1, P_xp_c2, P_xp_c3,
        P_xp_c4, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

end LeanProofs.IPRA.Geometry.KerrNewmanTraceRowXP
