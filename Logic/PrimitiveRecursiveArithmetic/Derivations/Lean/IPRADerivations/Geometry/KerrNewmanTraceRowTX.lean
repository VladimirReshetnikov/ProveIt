import IPRADerivations.Geometry.KerrNewmanPairProductA
import IPRADerivations.Geometry.KerrNewmanPairProductB

/-!
# The row `tx` of the trace `tr(C J C J)` (`four_metrics_ipra`)

Packet: `geometry/four_metrics_ipra_2026-11-15`, `eq:paircontract` (`𝒦 = 4 tr(C J C J)`). With the
product `M = C J` of `Geometry/KerrNewmanPairProductA`, `…B` (radial function `d`, Boyer–Lindquist
coordinates, index `p` for `φ`), for the pair `I = tx`: `row_I` with `P_I_tn` certifies the row sum
`P_I = Σ_K M_{IK} M_{KI}` of `tr(M M)` as a reduced fraction, each product reduced over the row's
common denominator. Summing the rows (`Geometry/KerrNewmanKretschmann`) instead of all the
products at once keeps every cleared identity small.

The reduced fractions and numerators were proposed by a computer algebra script; every identity
is checked by Lean as an identity of fractions cleared of denominators, a closed sentence of iPRA
certified in every commutative ring.
-/

namespace LeanProofs.IPRA.Geometry.KerrNewmanTraceRowTX

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

/-! ### The row `tx` -/

set_option maxHeartbeats 4000000 in
def P_tx_c1 : ZExp 6 := 36 * a ^ 10 * x ^ 6 - 32 * a ^ 10 * x ^ 4 - 72 * a ^ 8 * d * x ^ 6
    + 64 * a ^ 8 * d * x ^ 4 - 16 * a ^ 8 * r ^ 2 * x ^ 8
    + 148 * a ^ 8 * r ^ 2 * x ^ 6 - 188 * a ^ 8 * r ^ 2 * x ^ 4 + 64 * a ^ 8 * r ^ 2 * x ^ 2
    + 16 * a ^ 8 * r * v * x ^ 8 - 44 * a ^ 8 * r * v * x ^ 6
    + 20 * a ^ 8 * r * v * x ^ 4 - 4 * a ^ 8 * v ^ 2 * x ^ 8 + 3 * a ^ 8 * v ^ 2 * x ^ 6
    + 36 * a ^ 6 * d ^ 2 * x ^ 6 - 32 * a ^ 6 * d ^ 2 * x ^ 4 - 136 * a ^ 6 * d * r ^ 2 * x ^ 6

set_option maxHeartbeats 4000000 in
def P_tx_c2 : ZExp 6 := 272 * a ^ 6 * d * r ^ 2 * x ^ 4 - 128 * a ^ 6 * d * r ^ 2 * x ^ 2
    + 32 * a ^ 6 * d * r * v * x ^ 6 - 20 * a ^ 6 * d * r * v * x ^ 4
    + 64 * a ^ 6 * r ^ 4 * x ^ 6 - 124 * a ^ 6 * r ^ 4 * x ^ 4 + 60 * a ^ 6 * r ^ 4 * x ^ 2
    + 4 * a ^ 6 * r ^ 3 * v * x ^ 6 - 52 * a ^ 6 * r ^ 3 * v * x ^ 4
    + 24 * a ^ 6 * r ^ 3 * v * x ^ 2 - 9 * a ^ 6 * r ^ 2 * v ^ 2 * x ^ 6
    + 7 * a ^ 6 * r ^ 2 * v ^ 2 * x ^ 4 - 84 * a ^ 4 * d ^ 2 * r ^ 2 * x ^ 4

set_option maxHeartbeats 4000000 in
def P_tx_c3 : ZExp 6 := 64 * a ^ 4 * d ^ 2 * r ^ 2 * x ^ 2
    + 80 * a ^ 4 * d * r ^ 4 * x ^ 4 - 40 * a ^ 4 * d * r ^ 4 * x ^ 2
    + 44 * a ^ 4 * d * r ^ 3 * v * x ^ 4 - 24 * a ^ 4 * d * r ^ 3 * v * x ^ 2
    - 16 * a ^ 4 * r ^ 6 * x ^ 4
    + 12 * a ^ 4 * r ^ 6 * x ^ 2 - 4 * a ^ 4 * r ^ 6 - 24 * a ^ 4 * r ^ 5 * v * x ^ 4
    - 4 * a ^ 4 * r ^ 5 * v * x ^ 2 + 4 * a ^ 4 * r ^ 5 * v - 5 * a ^ 4 * r ^ 4 * v ^ 2 * x ^ 4
    + 5 * a ^ 4 * r ^ 4 * v ^ 2 * x ^ 2 - 20 * a ^ 2 * d ^ 2 * r ^ 4 * x ^ 2

set_option maxHeartbeats 4000000 in
def P_tx_c4 : ZExp 6 := 24 * a ^ 2 * d * r ^ 6 * x ^ 2
    + 8 * a ^ 2 * d * r ^ 5 * v * x ^ 2 - 4 * a ^ 2 * d * r ^ 5 * v - 4 * a ^ 2 * r ^ 8
    - 12 * a ^ 2 * r ^ 7 * v * x ^ 2 + 4 * a ^ 2 * r ^ 7 * v + a ^ 2 * r ^ 6 * v ^ 2 * x ^ 2
    + a ^ 2 * r ^ 6 * v ^ 2 + 4 * d ^ 2 * r ^ 6 - 4 * d * r ^ 7 * v + r ^ 8 * v ^ 2

set_option maxHeartbeats 4000000 in
/-- `Σ_K M_{tx,K} M_{K,tx}`, reduced. -/
def P_tx : Frac 6 := ⟨P_tx_c1 + P_tx_c2 + P_tx_c3 + P_tx_c4, 4 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 7⟩

/-- The common denominator of the terms of the row `tx` of `tr(M M)`. -/
def P_tx_cd : ZExp 6 := 4 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 8

/-- The numerator of `M_{tx,tr} M_{tr,tx}` over the common denominator. -/
def P_tx_n1 : ZExp 6 := -a ^ 4 * x ^ 2 * (x - 1) * (x + 1) * (a ^ 2 + 2 * d + r ^ 2) * (2 * a ^ 2 +
    d + 2 * r ^ 2) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r
    ^ 3 - r ^ 2 * v) ^ 2
/-- `M_{tx,tr} M_{tr,tx}`, reduced to the common denominator. -/
theorem P_tx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (M_tx_tr * M_tr_tx) (⟨P_tx_n1, P_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [M_tx_tr, M_tr_tx, P_tx_n1, P_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `M_{tx,tx} M_{tx,tx}` over the common denominator. -/
def P_tx_n2 : ZExp 6 := d * (6 * a ^ 6 * x ^ 4 - 8 * a ^ 6 * x ^ 2 - 6 * a ^ 4 * d * x ^ 4 + 8 * a
    ^ 4 * d * x ^ 2 + 6 * a ^ 4 * r ^ 2 * x ^ 4 - 14 * a ^ 4 * r ^ 2 * x ^ 2 + 4 * a ^ 4 * r ^ 2 +
    a ^ 4 * r * v * x ^ 2 + 4 * a ^ 2 * d * r ^ 2 * x ^ 2 - 4 * a ^ 2 * d * r ^ 2 - 6 * a ^ 2 * r ^
    4 * x ^ 2 + 4 * a ^ 2 * r ^ 4 + a ^ 2 * r ^ 3 * v * x ^ 2 + a ^ 2 * r ^ 3 * v - 2 * d * r ^ 4 +
    r ^ 5 * v) ^ 2
/-- `M_{tx,tx} M_{tx,tx}`, reduced to the common denominator. -/
theorem P_tx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (M_tx_tx * M_tx_tx) (⟨P_tx_n2, P_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [M_tx_tx, P_tx_n2, P_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1,
        δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `M_{tx,rp} M_{rp,tx}` over the common denominator. -/
def P_tx_n3 : ZExp 6 := -a ^ 2 * x ^ 2 * (2 * a ^ 2 * x ^ 2 - 2 * a ^ 2 - d) * (-a ^ 4 + 2 * a ^ 2
    * d * x ^ 2 - 2 * a ^ 2 * d - 2 * a ^ 2 * r ^ 2 - r ^ 4) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 *
    r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v) ^ 2
/-- `M_{tx,rp} M_{rp,tx}`, reduced to the common denominator. -/
theorem P_tx_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (M_tx_rp * M_rp_tx) (⟨P_tx_n3, P_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [M_tx_rp, M_rp_tx, P_tx_n3, P_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `M_{tx,xp} M_{xp,tx}` over the common denominator. -/
def P_tx_n4 : ZExp 6 := a ^ 2 * d * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (8 * a ^ 4 * x ^ 2 - 8 *
    a ^ 2 * d * x ^ 2 + 10 * a ^ 2 * r ^ 2 * x ^ 2 - 4 * a ^ 2 * r ^ 2 - a ^ 2 * r * v * x ^ 2 + 4
    * d * r ^ 2 - 2 * r ^ 4 - r ^ 3 * v) ^ 2
/-- `M_{tx,xp} M_{xp,tx}`, reduced to the common denominator. -/
theorem P_tx_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (M_tx_xp * M_xp_tx) (⟨P_tx_n4, P_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [M_tx_xp, M_xp_tx, P_tx_n4, P_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The row `tx` of `tr(M M)`: `Σ_K M_{tx,K} M_{K,tx}` is the reduced fraction. -/
theorem row_tx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨P_tx_n1 + P_tx_n2 + P_tx_n3 + P_tx_n4, P_tx_cd⟩) (P_tx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [P_tx_n1, P_tx_n2, P_tx_n3, P_tx_n4, P_tx_cd, P_tx, P_tx_c1, P_tx_c2, P_tx_c3,
        P_tx_c4, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

end LeanProofs.IPRA.Geometry.KerrNewmanTraceRowTX
