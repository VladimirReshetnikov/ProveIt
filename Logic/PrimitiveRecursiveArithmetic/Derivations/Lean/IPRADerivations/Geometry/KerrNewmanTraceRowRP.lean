import IPRADerivations.Geometry.KerrNewmanPairProductA
import IPRADerivations.Geometry.KerrNewmanPairProductB

/-!
# The row `rp` of the trace `tr(C J C J)` (`four_metrics_ipra`)

Packet: `geometry/four_metrics_ipra_2026-11-15`, `eq:paircontract` (`𝒦 = 4 tr(C J C J)`). With the
product `M = C J` of `Geometry/KerrNewmanPairProductA`, `…B` (radial function `d`, Boyer–Lindquist
coordinates, index `p` for `φ`), for the pair `I = rp`: `row_I` with `P_I_tn` certifies the row sum
`P_I = Σ_K M_{IK} M_{KI}` of `tr(M M)` as a reduced fraction, each product reduced over the row's
common denominator. Summing the rows (`Geometry/KerrNewmanKretschmann`) instead of all the
products at once keeps every cleared identity small.

The reduced fractions and numerators were proposed by a computer algebra script; every identity
is checked by Lean as an identity of fractions cleared of denominators, a closed sentence of iPRA
certified in every commutative ring.
-/

namespace LeanProofs.IPRA.Geometry.KerrNewmanTraceRowRP

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

/-! ### The row `rp` -/

set_option maxHeartbeats 4000000 in
def P_rp_c1 : ZExp 6 := a ^ 10 * w ^ 2 * x ^ 10 - a ^ 10 * w ^ 2 * x ^ 8
    - 4 * a ^ 10 * w * x ^ 10 + 8 * a ^ 10 * w * x ^ 8 - 4 * a ^ 10 * w * x ^ 6
    + 4 * a ^ 10 * x ^ 10 - 12 * a ^ 10 * x ^ 8 + 12 * a ^ 10 * x ^ 6 - 4 * a ^ 8 * d * w * x ^ 8
    + 4 * a ^ 8 * d * w * x ^ 6 + 8 * a ^ 8 * d * x ^ 8 - 16 * a ^ 8 * d * x ^ 6
    + 4 * a ^ 8 * r ^ 2 * w ^ 2 * x ^ 8 - 4 * a ^ 8 * r ^ 2 * w ^ 2 * x ^ 6
    + 4 * a ^ 8 * r ^ 2 * w * x ^ 8 - 8 * a ^ 8 * r ^ 2 * w * x ^ 6

set_option maxHeartbeats 4000000 in
def P_rp_c2 : ZExp 6 := 4 * a ^ 8 * r ^ 2 * w * x ^ 4 - 40 * a ^ 8 * r ^ 2 * x ^ 8
    + 148 * a ^ 8 * r ^ 2 * x ^ 6 - 164 * a ^ 8 * r ^ 2 * x ^ 4
    + 64 * a ^ 8 * r ^ 2 * x ^ 2 - 8 * a ^ 8 * r * v * w * x ^ 8 + 8 * a ^ 8 * r * v * w * x ^ 6
    + 32 * a ^ 8 * r * v * x ^ 8 - 76 * a ^ 8 * r * v * x ^ 6
    + 36 * a ^ 8 * r * v * x ^ 4 - 4 * a ^ 8 * v ^ 2 * x ^ 8 + 3 * a ^ 8 * v ^ 2 * x ^ 6
    + 4 * a ^ 6 * d ^ 2 * x ^ 6 + 4 * a ^ 6 * d * r ^ 2 * w * x ^ 6

set_option maxHeartbeats 4000000 in
def P_rp_c3 : ZExp 6 := 4 * a ^ 6 * d * r ^ 2 * w * x ^ 4
    + 112 * a ^ 6 * d * r ^ 2 * x ^ 6 - 248 * a ^ 6 * d * r ^ 2 * x ^ 4
    + 128 * a ^ 6 * d * r ^ 2 * x ^ 2 - 48 * a ^ 6 * d * r * v * x ^ 6
    + 36 * a ^ 6 * d * r * v * x ^ 4 - 6 * a ^ 6 * r ^ 4 * w ^ 2 * x ^ 6
    + 6 * a ^ 6 * r ^ 4 * w ^ 2 * x ^ 4 - 20 * a ^ 6 * r ^ 4 * w * x ^ 6
    + 40 * a ^ 6 * r ^ 4 * w * x ^ 4 - 20 * a ^ 6 * r ^ 4 * w * x ^ 2
    - 64 * a ^ 6 * r ^ 4 * x ^ 6 + 148 * a ^ 6 * r ^ 4 * x ^ 4

set_option maxHeartbeats 4000000 in
def P_rp_c4 : ZExp 6 := 116 * a ^ 6 * r ^ 4 * x ^ 2 - 32 * a ^ 6 * r ^ 4
    - 24 * a ^ 6 * r ^ 3 * v * w * x ^ 6
    + 24 * a ^ 6 * r ^ 3 * v * w * x ^ 4 - 28 * a ^ 6 * r ^ 3 * v * x ^ 6
    + 12 * a ^ 6 * r ^ 3 * v * x ^ 4 - 8 * a ^ 6 * r ^ 3 * v * x ^ 2
    + 7 * a ^ 6 * r ^ 2 * v ^ 2 * x ^ 6 - 9 * a ^ 6 * r ^ 2 * v ^ 2 * x ^ 4
    - 84 * a ^ 4 * d ^ 2 * r ^ 2 * x ^ 4 + 64 * a ^ 4 * d ^ 2 * r ^ 2 * x ^ 2
    + 20 * a ^ 4 * d * r ^ 4 * w * x ^ 4 - 20 * a ^ 4 * d * r ^ 4 * w * x ^ 2

set_option maxHeartbeats 4000000 in
def P_rp_c5 : ZExp 6 := 104 * a ^ 4 * d * r ^ 4 * x ^ 4 - 128 * a ^ 4 * d * r ^ 4 * x ^ 2
    + 64 * a ^ 4 * d * r ^ 4 + 12 * a ^ 4 * d * r ^ 3 * v * x ^ 4
    + 8 * a ^ 4 * d * r ^ 3 * v * x ^ 2
    + 4 * a ^ 4 * r ^ 6 * w ^ 2 * x ^ 4 - 4 * a ^ 4 * r ^ 6 * w ^ 2 * x ^ 2
    + 12 * a ^ 4 * r ^ 6 * w * x ^ 4 - 24 * a ^ 4 * r ^ 6 * w * x ^ 2 + 12 * a ^ 4 * r ^ 6 * w
    + 8 * a ^ 4 * r ^ 6 * x ^ 4 - 20 * a ^ 4 * r ^ 6 * x ^ 2
    + 4 * a ^ 4 * r ^ 6 - 24 * a ^ 4 * r ^ 5 * v * w * x ^ 4

set_option maxHeartbeats 4000000 in
def P_rp_c6 : ZExp 6 := 24 * a ^ 4 * r ^ 5 * v * w * x ^ 2 - 72 * a ^ 4 * r ^ 5 * v * x ^ 4
    + 92 * a ^ 4 * r ^ 5 * v * x ^ 2 - 44 * a ^ 4 * r ^ 5 * v
    + 27 * a ^ 4 * r ^ 4 * v ^ 2 * x ^ 4 - 27 * a ^ 4 * r ^ 4 * v ^ 2 * x ^ 2
    + 12 * a ^ 2 * d ^ 2 * r ^ 4 * x ^ 2 - 32 * a ^ 2 * d ^ 2 * r ^ 4
    + 12 * a ^ 2 * d * r ^ 6 * w * x ^ 2 - 12 * a ^ 2 * d * r ^ 6 * w
    + 32 * a ^ 2 * d * r ^ 6 * x ^ 2 - 8 * a ^ 2 * d * r ^ 6 - 40 * a ^ 2 * d * r ^ 5 * v * x ^ 2

set_option maxHeartbeats 4000000 in
def P_rp_c7 : ZExp 6 := 44 * a ^ 2 * d * r ^ 5 * v
    + a ^ 2 * r ^ 8 * w ^ 2 * x ^ 2 - a ^ 2 * r ^ 8 * w ^ 2 - 4 * a ^ 2 * r ^ 8 * x ^ 2
    - 8 * a ^ 2 * r ^ 7 * v * w * x ^ 2
    + 8 * a ^ 2 * r ^ 7 * v * w - 12 * a ^ 2 * r ^ 7 * v * x ^ 2 + 4 * a ^ 2 * r ^ 7 * v
    + 17 * a ^ 2 * r ^ 6 * v ^ 2 * x ^ 2 - 15 * a ^ 2 * r ^ 6 * v ^ 2
    + 4 * d ^ 2 * r ^ 6 - 4 * d * r ^ 7 * v + r ^ 8 * v ^ 2

set_option maxHeartbeats 4000000 in
/-- `Σ_K M_{rp,K} M_{K,rp}`, reduced. -/
def P_rp : Frac 6 := ⟨P_rp_c1 + P_rp_c2 - P_rp_c3 + P_rp_c4 + P_rp_c5 + P_rp_c6
    + P_rp_c7, 4 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 7⟩

/-- The common denominator of the terms of the row `rp` of `tr(M M)`. -/
def P_rp_cd : ZExp 6 := 4 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 8

/-- The numerator of `M_{rp,tr} M_{tr,rp}` over the common denominator. -/
def P_rp_n1 : ZExp 6 := a ^ 2 * d * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 4 * w * x ^ 4 - 2 *
    a ^ 4 * x ^ 4 + 4 * a ^ 4 * x ^ 2 - 4 * a ^ 2 * d * x ^ 2 + 2 * a ^ 2 * r ^ 2 * w * x ^ 2 + 10
    * a ^ 2 * r ^ 2 * x ^ 2 - 8 * a ^ 2 * r ^ 2 - 5 * a ^ 2 * r * v * x ^ 2 + 8 * d * r ^ 2 + r ^ 4
    * w - 5 * r ^ 3 * v) ^ 2
/-- `M_{rp,tr} M_{tr,rp}`, reduced to the common denominator. -/
theorem P_rp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (M_rp_tr * M_tr_rp) (⟨P_rp_n1, P_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [M_rp_tr, M_tr_rp, P_rp_n1, P_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `M_{rp,tx} M_{tx,rp}` over the common denominator. -/
def P_rp_n2 : ZExp 6 := -a ^ 2 * x ^ 2 * (2 * a ^ 2 * x ^ 2 - 2 * a ^ 2 - d) * (-a ^ 4 + 2 * a ^ 2
    * d * x ^ 2 - 2 * a ^ 2 * d - 2 * a ^ 2 * r ^ 2 - r ^ 4) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 *
    r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v) ^ 2
/-- `M_{rp,tx} M_{tx,rp}`, reduced to the common denominator. -/
theorem P_rp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (M_rp_tx * M_tx_rp) (⟨P_rp_n2, P_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [M_rp_tx, M_tx_rp, P_rp_n2, P_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

set_option maxHeartbeats 4000000 in
def P_rp_n3_c1 : ZExp 6 := a ^ 6 * w * x ^ 6 - a ^ 6 * w * x ^ 4 - 2 * a ^ 6 * x ^ 6
    + 4 * a ^ 6 * x ^ 4 - 4 * a ^ 6 * x ^ 2 - 2 * a ^ 4 * d * x ^ 4 + 4 * a ^ 4 * d * x ^ 2
    + 2 * a ^ 4 * r ^ 2 * w * x ^ 4 - 2 * a ^ 4 * r ^ 2 * w * x ^ 2
    + 6 * a ^ 4 * r ^ 2 * x ^ 4 - 18 * a ^ 4 * r ^ 2 * x ^ 2
    + 8 * a ^ 4 * r ^ 2 - 4 * a ^ 4 * r * v * x ^ 4 + 5 * a ^ 4 * r * v * x ^ 2
    + 8 * a ^ 2 * d * r ^ 2 * x ^ 2 - 8 * a ^ 2 * d * r ^ 2
    + a ^ 2 * r ^ 4 * w * x ^ 2 - a ^ 2 * r ^ 4 * w

set_option maxHeartbeats 4000000 in
def P_rp_n3_c2 : ZExp 6 := 4 * a ^ 2 * r ^ 4 * x ^ 2 - 2 * a ^ 2 * r ^ 4
    + 3 * a ^ 2 * r ^ 3 * v * x ^ 2 - 5 * a ^ 2 * r ^ 3 * v + 2 * d * r ^ 4 - r ^ 5 * v

set_option maxHeartbeats 4000000 in
/-- The numerator of `M_{rp,rp} M_{rp,rp}` over the common denominator. -/
def P_rp_n3 : ZExp 6 := d * ((P_rp_n3_c1 - P_rp_n3_c2) ^ 2)
/-- `M_{rp,rp} M_{rp,rp}`, reduced to the common denominator. -/
theorem P_rp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (M_rp_rp * M_rp_rp) (⟨P_rp_n3, P_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [M_rp_rp, P_rp_n3, P_rp_n3_c1, P_rp_n3_c2, P_rp_cd, δr_0, δr_1, δr_2, δr_3,
        δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `M_{rp,xp} M_{xp,rp}` over the common denominator. -/
def P_rp_n4 : ZExp 6 := -a ^ 4 * x ^ 2 * (x - 1) * (x + 1) * (a ^ 2 + 2 * d + r ^ 2) * (2 * a ^ 2 +
    d + 2 * r ^ 2) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r
    ^ 3 - r ^ 2 * v) ^ 2
/-- `M_{rp,xp} M_{xp,rp}`, reduced to the common denominator. -/
theorem P_rp_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (M_rp_xp * M_xp_rp) (⟨P_rp_n4, P_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [M_rp_xp, M_xp_rp, P_rp_n4, P_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The row `rp` of `tr(M M)`: `Σ_K M_{rp,K} M_{K,rp}` is the reduced fraction. -/
theorem row_rp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨P_rp_n1 + P_rp_n2 + P_rp_n3 + P_rp_n4, P_rp_cd⟩) (P_rp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [P_rp_n1, P_rp_n2, P_rp_n3, P_rp_n3_c1, P_rp_n3_c2, P_rp_n4, P_rp_cd, P_rp,
        P_rp_c1, P_rp_c2, P_rp_c3, P_rp_c4, P_rp_c5, P_rp_c6, P_rp_c7, δr_0, δr_1, δr_2, δr_3,
        δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

end LeanProofs.IPRA.Geometry.KerrNewmanTraceRowRP
