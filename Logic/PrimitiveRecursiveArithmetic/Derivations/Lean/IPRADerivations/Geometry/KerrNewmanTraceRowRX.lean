import IPRADerivations.Geometry.KerrNewmanPairProductA
import IPRADerivations.Geometry.KerrNewmanPairProductB

/-!
# The row `rx` of the trace `tr(C J C J)` (`four_metrics_ipra`)

Packet: `geometry/four_metrics_ipra_2026-11-15`, `eq:paircontract` (`𝒦 = 4 tr(C J C J)`). With the
product `M = C J` of `Geometry/KerrNewmanPairProductA`, `…B` (radial function `d`, Boyer–Lindquist
coordinates, index `p` for `φ`), for the pair `I = rx`: `row_I` with `P_I_tn` certifies the row sum
`P_I = Σ_K M_{IK} M_{KI}` of `tr(M M)` as a reduced fraction, each product reduced over the row's
common denominator. Summing the rows (`Geometry/KerrNewmanKretschmann`) instead of all the
products at once keeps every cleared identity small.

The reduced fractions and numerators were proposed by a computer algebra script; every identity
is checked by Lean as an identity of fractions cleared of denominators, a closed sentence of iPRA
certified in every commutative ring.
-/

namespace LeanProofs.IPRA.Geometry.KerrNewmanTraceRowRX

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

/-! ### The row `rx` -/



set_option maxHeartbeats 4000000 in
/-- `Σ_K M_{rx,K} M_{K,rx}`, reduced. -/
def P_rx : Frac 6 := ⟨-((-2 * a ^ 4 * x ^ 2
    + 2 * a ^ 3 * r * x ^ 3 - 4 * a ^ 3 * r * x - a ^ 3 * v * x ^ 3
    + 2 * a ^ 2 * d * x ^ 2 - 4 * a ^ 2 * r ^ 2 * x ^ 2 + 2 * a ^ 2 * r ^ 2
    + a ^ 2 * r * v * x ^ 2
    + 4 * a * d * r * x - 2 * a * r ^ 3 * x - a * r ^ 2 * v * x - 2 * d * r ^ 2
    + r ^ 3 * v) * (2 * a ^ 4 * x ^ 2
    + 2 * a ^ 3 * r * x ^ 3 - 4 * a ^ 3 * r * x - a ^ 3 * v * x ^ 3 - 2 * a ^ 2 * d * x ^ 2
    + 4 * a ^ 2 * r ^ 2 * x ^ 2 - 2 * a ^ 2 * r ^ 2 - a ^ 2 * r * v * x ^ 2
    + 4 * a * d * r * x - 2 * a * r ^ 3 * x - a * r ^ 2 * v * x
    + 2 * d * r ^ 2 - r ^ 3 * v)), 4 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 6⟩

/-- The common denominator of the terms of the row `rx` of `tr(M M)`. -/
def P_rx_cd : ZExp 6 := 4 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 6

/-- The numerator of `M_{rx,tp} M_{tp,rx}` over the common denominator. -/
def P_rx_n1 : ZExp 6 := -a ^ 2 * x ^ 2 * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2
    + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v) ^ 2
/-- `M_{rx,tp} M_{tp,rx}`, reduced to the common denominator. -/
theorem P_rx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (M_rx_tp * M_tp_rx) (⟨P_rx_n1, P_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [M_rx_tp, M_tp_rx, P_rx_n1, P_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `M_{rx,rx} M_{rx,rx}` over the common denominator. -/
def P_rx_n2 : ZExp 6 := (2 * a ^ 4 * x ^ 2 - 2 * a ^ 2 * d * x ^ 2 + 4 * a ^ 2 * r ^ 2 * x ^ 2 - 2
    * a ^ 2 * r ^ 2 - a ^ 2 * r * v * x ^ 2 + 2 * d * r ^ 2 - r ^ 3 * v) ^ 2
/-- `M_{rx,rx} M_{rx,rx}`, reduced to the common denominator. -/
theorem P_rx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (M_rx_rx * M_rx_rx) (⟨P_rx_n2, P_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [M_rx_rx, P_rx_n2, P_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1,
        δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The row `rx` of `tr(M M)`: `Σ_K M_{rx,K} M_{K,rx}` is the reduced fraction. -/
theorem row_rx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨P_rx_n1 + P_rx_n2, P_rx_cd⟩) (P_rx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [P_rx_n1, P_rx_n2, P_rx_cd, P_rx, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

end LeanProofs.IPRA.Geometry.KerrNewmanTraceRowRX
