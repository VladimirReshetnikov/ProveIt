import IPRADerivations.Geometry.KerrNewmanTraceRowTR
import IPRADerivations.Geometry.KerrNewmanTraceRowTX
import IPRADerivations.Geometry.KerrNewmanTraceRowTP
import IPRADerivations.Geometry.KerrNewmanTraceRowRX
import IPRADerivations.Geometry.KerrNewmanTraceRowRP
import IPRADerivations.Geometry.KerrNewmanTraceRowXP
import IPRADerivations.Geometry.KerrNewmanEinstein

/-!
# The Kretschmann scalar of the Kerr–Newman metric (`four_metrics_ipra`)

Packet: `geometry/four_metrics_ipra_2026-11-15`, `eq:paircontract` and `eq:Kretschmann`: "Order the
six pairs `I = (i, j)` with `i < j`. Let `C_{IJ} = R_{ijkℓ}` for `J = (k, ℓ)` and let
`J_{(i,j),(k,ℓ)} = g^{ik} g^{jℓ} − g^{iℓ} g^{jk}`. Then `𝒦 = 4 tr(C J C J)`", and

`𝒦 = (8/Σ⁶) [6m² (r⁶ − 15 r⁴ a² x² + 15 r² a⁴ x⁴ − a⁶ x⁶)
  − 12 m q² r (r⁴ − 10 r² a² x² + 5 a⁴ x⁴) + q⁴ (7 r⁴ − 34 r² a² x² + 7 a⁴ x⁴)]`.

With the Riemann tensor of `Geometry/KerrNewmanRiemannT`, `…R`, `…X`, `…P` (radial function `d`,
`∂_r d = v`, `∂_r v = w`; Boyer–Lindquist coordinates, index `p` for `φ`):

* the pair matrix `C`, the pair inverse `J` (`Geometry/KerrNewmanPairMatrix`), the product
  `M = C J` (`Geometry/KerrNewmanPairProductA`, `…B`) and the row sums
  `P_I = Σ_K M_{IK} M_{KI}` (`Geometry/KerrNewmanTraceRowTR`, …);
* `kretschmann_radial` with `K_tn`: `4 Σ_I P_I = Kf`, the Kretschmann scalar of the
  radial-function metric (a reduced fraction in `r, x, a, d, v, w`);
* `kn_kretschmann`: after renaming into `r, x, a, d, v, w, m, q` (`Foundations/ExpressionRenaming`,
  `Geometry/KerrNewmanEinstein.ι₆`), under `d = Δ`, `v = 2r − 2m`, `w = 2`
  (`Geometry/KerrNewmanRicci.knHyps`): `Kf = 8 Kn/Σ⁶` with the bracket `Kn` of `eq:Kretschmann`.

With `Geometry/KerrNewmanHorizon.equator_K` and its two sum-of-squares certificates this gives
`eq:equatorK` and the equatorial blow-up bounds from the full Riemann tensor. The composition of
the stages (each layer's reduced fractions are the next layer's inputs) is the chain of cleared
identities; it is not restated as one sentence.

The reduced fractions and numerators were proposed by a computer algebra script; every identity
is checked by Lean as an identity of fractions cleared of denominators, a closed sentence of iPRA
certified in every commutative ring.
-/

namespace LeanProofs.IPRA.Geometry.KerrNewmanKretschmann

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
open LeanProofs.IPRA.Geometry.KerrNewmanTraceRowTR
open LeanProofs.IPRA.Geometry.KerrNewmanTraceRowTX
open LeanProofs.IPRA.Geometry.KerrNewmanTraceRowTP
open LeanProofs.IPRA.Geometry.KerrNewmanTraceRowRX
open LeanProofs.IPRA.Geometry.KerrNewmanTraceRowRP
open LeanProofs.IPRA.Geometry.KerrNewmanTraceRowXP
open ZExp

local notation "r" => (ZExp.var 0 : ZExp 6)
local notation "x" => (ZExp.var 1 : ZExp 6)
local notation "a" => (ZExp.var 2 : ZExp 6)
local notation "d" => (ZExp.var 3 : ZExp 6)
local notation "v" => (ZExp.var 4 : ZExp 6)
local notation "w" => (ZExp.var 5 : ZExp 6)

/-! ## The Kretschmann scalar for a general radial function -/

set_option maxHeartbeats 4000000 in
def Kf_c1 : ZExp 6 := a ^ 8 * w ^ 2 * x ^ 8 - 4 * a ^ 8 * w * x ^ 8 + 4 * a ^ 8 * w * x ^ 6
    + 4 * a ^ 8 * x ^ 8 - 8 * a ^ 8 * x ^ 6 + 56 * a ^ 8 * x ^ 4 - 4 * a ^ 6 * d * w * x ^ 6
    + 8 * a ^ 6 * d * x ^ 6 - 112 * a ^ 6 * d * x ^ 4 + 4 * a ^ 6 * r ^ 2 * w ^ 2 * x ^ 6
    + 4 * a ^ 6 * r ^ 2 * w * x ^ 6 - 4 * a ^ 6 * r ^ 2 * w * x ^ 4 - 72 * a ^ 6 * r ^ 2 * x ^ 6
    + 376 * a ^ 6 * r ^ 2 * x ^ 4 - 272 * a ^ 6 * r ^ 2 * x ^ 2 - 8 * a ^ 6 * r * v * w * x ^ 6

set_option maxHeartbeats 4000000 in
def Kf_c2 : ZExp 6 := 64 * a ^ 6 * r * v * x ^ 6 - 128 * a ^ 6 * r * v * x ^ 4
    - 12 * a ^ 6 * v ^ 2 * x ^ 6 + 56 * a ^ 4 * d ^ 2 * x ^ 4
    + 4 * a ^ 4 * d * r ^ 2 * w * x ^ 4 - 376 * a ^ 4 * d * r ^ 2 * x ^ 4
    + 544 * a ^ 4 * d * r ^ 2 * x ^ 2 + 128 * a ^ 4 * d * r * v * x ^ 4
    + 6 * a ^ 4 * r ^ 4 * w ^ 2 * x ^ 4
    + 20 * a ^ 4 * r ^ 4 * w * x ^ 4 - 20 * a ^ 4 * r ^ 4 * w * x ^ 2
    + 232 * a ^ 4 * r ^ 4 * x ^ 4 - 376 * a ^ 4 * r ^ 4 * x ^ 2 + 56 * a ^ 4 * r ^ 4

set_option maxHeartbeats 4000000 in
def Kf_c3 : ZExp 6 := 24 * a ^ 4 * r ^ 3 * v * w * x ^ 4 + 64 * a ^ 4 * r ^ 3 * v * x ^ 4
    + 64 * a ^ 4 * r ^ 3 * v * x ^ 2 + 4 * a ^ 4 * r ^ 2 * v ^ 2 * x ^ 4
    + 272 * a ^ 2 * d ^ 2 * r ^ 2 * x ^ 2 - 20 * a ^ 2 * d * r ^ 4 * w * x ^ 2
    - 376 * a ^ 2 * d * r ^ 4 * x ^ 2
    + 112 * a ^ 2 * d * r ^ 4 - 64 * a ^ 2 * d * r ^ 3 * v * x ^ 2
    - 4 * a ^ 2 * r ^ 6 * w ^ 2 * x ^ 2 - 12 * a ^ 2 * r ^ 6 * w * x ^ 2 + 12 * a ^ 2 * r ^ 6 * w
    + 72 * a ^ 2 * r ^ 6 * x ^ 2

set_option maxHeartbeats 4000000 in
def Kf_c4 : ZExp 6 := 8 * a ^ 2 * r ^ 6 - 24 * a ^ 2 * r ^ 5 * v * w * x ^ 2
    - 128 * a ^ 2 * r ^ 5 * v * x ^ 2 + 64 * a ^ 2 * r ^ 5 * v
    + 28 * a ^ 2 * r ^ 4 * v ^ 2 * x ^ 2 + 56 * d ^ 2 * r ^ 4
    + 12 * d * r ^ 6 * w - 8 * d * r ^ 6 - 64 * d * r ^ 5 * v + r ^ 8 * w ^ 2
    + 4 * r ^ 8 - 8 * r ^ 7 * v * w + 20 * r ^ 6 * v ^ 2

set_option maxHeartbeats 4000000 in
/-- The Kretschmann scalar `4 tr(C J C J)` of the radial-function metric, reduced. -/
def Kf : Frac 6 := ⟨Kf_c1 + Kf_c2 - Kf_c3 + Kf_c4, (a ^ 2 * x ^ 2 + r ^ 2) ^ 6⟩

/-- The common denominator of the terms of `4 tr(C J C J)`. -/
def K_cd : ZExp 6 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 7

def K_n1_c1 : ZExp 6 := a ^ 10 * w ^ 2 * x ^ 8 - 4 * a ^ 10 * w * x ^ 8 + 4 * a ^ 10 * w * x ^ 6
    + 4 * a ^ 10 * x ^ 8 - 4 * a ^ 10 * x ^ 6 - 4 * a ^ 8 * d * w * x ^ 6
    + a ^ 8 * r ^ 2 * w ^ 2 * x ^ 8
    + 4 * a ^ 8 * r ^ 2 * w ^ 2 * x ^ 6 - 4 * a ^ 8 * r ^ 2 * w * x ^ 8
    + 8 * a ^ 8 * r ^ 2 * w * x ^ 6 - 4 * a ^ 8 * r ^ 2 * w * x ^ 4 - 12 * a ^ 8 * r ^ 2 * x ^ 6
    + 60 * a ^ 8 * r ^ 2 * x ^ 4 - 64 * a ^ 8 * r ^ 2 * x ^ 2 - 8 * a ^ 8 * r * v * w * x ^ 6

def K_n1_c2 : ZExp 6 := 4 * a ^ 8 * r * v * x ^ 8
    + 16 * a ^ 8 * r * v * x ^ 6 - 36 * a ^ 8 * r * v * x ^ 4 - a ^ 8 * v ^ 2 * x ^ 8
    - 3 * a ^ 8 * v ^ 2 * x ^ 6 + 4 * a ^ 6 * d ^ 2 * x ^ 6 - 4 * a ^ 6 * d * r ^ 2 * w * x ^ 6
    + 4 * a ^ 6 * d * r ^ 2 * w * x ^ 4 - 24 * a ^ 6 * d * r ^ 2 * x ^ 6
    - 40 * a ^ 6 * d * r ^ 2 * x ^ 4 + 128 * a ^ 6 * d * r ^ 2 * x ^ 2
    + 12 * a ^ 6 * d * r * v * x ^ 6 + 36 * a ^ 6 * d * r * v * x ^ 4
    + 4 * a ^ 6 * r ^ 4 * w ^ 2 * x ^ 6

def K_n1_c3 : ZExp 6 := 6 * a ^ 6 * r ^ 4 * w ^ 2 * x ^ 4 + 4 * a ^ 6 * r ^ 4 * w * x ^ 6
    + 16 * a ^ 6 * r ^ 4 * w * x ^ 4 - 20 * a ^ 6 * r ^ 4 * w * x ^ 2
    - 16 * a ^ 6 * r ^ 4 * x ^ 6 + 124 * a ^ 6 * r ^ 4 * x ^ 4 - 188 * a ^ 6 * r ^ 4 * x ^ 2
    + 32 * a ^ 6 * r ^ 4 - 8 * a ^ 6 * r ^ 3 * v * w * x ^ 6 - 24 * a ^ 6 * r ^ 3 * v * w * x ^ 4
    + 24 * a ^ 6 * r ^ 3 * v * x ^ 6 - 80 * a ^ 6 * r ^ 3 * v * x ^ 4
    + 8 * a ^ 6 * r ^ 3 * v * x ^ 2 - 5 * a ^ 6 * r ^ 2 * v ^ 2 * x ^ 6

def K_n1_c4 : ZExp 6 := 9 * a ^ 6 * r ^ 2 * v ^ 2 * x ^ 4 - 20 * a ^ 4 * d ^ 2 * r ^ 2 * x ^ 4
    - 64 * a ^ 4 * d ^ 2 * r ^ 2 * x ^ 2 + 4 * a ^ 4 * d * r ^ 4 * w * x ^ 4
    + 20 * a ^ 4 * d * r ^ 4 * w * x ^ 2 - 80 * a ^ 4 * d * r ^ 4 * x ^ 4
    + 272 * a ^ 4 * d * r ^ 4 * x ^ 2 - 64 * a ^ 4 * d * r ^ 4
    + 56 * a ^ 4 * d * r ^ 3 * v * x ^ 4 - 8 * a ^ 4 * d * r ^ 3 * v * x ^ 2
    + 6 * a ^ 4 * r ^ 6 * w ^ 2 * x ^ 4 + 4 * a ^ 4 * r ^ 6 * w ^ 2 * x ^ 2
    + 20 * a ^ 4 * r ^ 6 * w * x ^ 4

def K_n1_c5 : ZExp 6 := 8 * a ^ 4 * r ^ 6 * w * x ^ 2
    + 12 * a ^ 4 * r ^ 6 * w - 64 * a ^ 4 * r ^ 6 * x ^ 4
    + 148 * a ^ 4 * r ^ 6 * x ^ 2 - 36 * a ^ 4 * r ^ 6 + 24 * a ^ 4 * r ^ 5 * v * w * x ^ 4
    + 24 * a ^ 4 * r ^ 5 * v * w * x ^ 2 + 44 * a ^ 4 * r ^ 5 * v * x ^ 4
    + 48 * a ^ 4 * r ^ 5 * v * x ^ 2 - 44 * a ^ 4 * r ^ 5 * v - 9 * a ^ 4 * r ^ 4 * v ^ 2 * x ^ 4
    - 27 * a ^ 4 * r ^ 4 * v ^ 2 * x ^ 2
    + 84 * a ^ 2 * d ^ 2 * r ^ 4 * x ^ 2 - 32 * a ^ 2 * d ^ 2 * r ^ 4

def K_n1_c6 : ZExp 6 := 20 * a ^ 2 * d * r ^ 6 * w * x ^ 2 + 12 * a ^ 2 * d * r ^ 6 * w
    + 136 * a ^ 2 * d * r ^ 6 * x ^ 2 - 72 * a ^ 2 * d * r ^ 6
    - 4 * a ^ 2 * d * r ^ 5 * v * x ^ 2 - 44 * a ^ 2 * d * r ^ 5 * v
    + 4 * a ^ 2 * r ^ 8 * w ^ 2 * x ^ 2 + a ^ 2 * r ^ 8 * w ^ 2
    + 12 * a ^ 2 * r ^ 8 * w * x ^ 2 - 12 * a ^ 2 * r ^ 8 * w - 16 * a ^ 2 * r ^ 8 * x ^ 2
    - 24 * a ^ 2 * r ^ 7 * v * w * x ^ 2 - 8 * a ^ 2 * r ^ 7 * v * w
    - 64 * a ^ 2 * r ^ 7 * v * x ^ 2

def K_n1_c7 : ZExp 6 := 48 * a ^ 2 * r ^ 7 * v + 29 * a ^ 2 * r ^ 6 * v ^ 2 * x ^ 2
    + 15 * a ^ 2 * r ^ 6 * v ^ 2 + 36 * d ^ 2 * r ^ 6 + 12 * d * r ^ 8 * w - 48 * d * r ^ 7 * v
    + r ^ 10 * w ^ 2 - 8 * r ^ 9 * v * w + 16 * r ^ 8 * v ^ 2

/-- The numerator of `4 P_{tr}` over the common denominator. -/
def K_n1 : ZExp 6 := K_n1_c1 + K_n1_c2 + K_n1_c3 + K_n1_c4 - K_n1_c5 + K_n1_c6 + K_n1_c7
set_option maxRecDepth 20000 in
/-- `4 P_{tr}`, reduced to the common denominator. -/
theorem K_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.ofZ 4 * P_tr) (⟨K_n1, K_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [P_tr, P_tr_c1, P_tr_c2, P_tr_c3, P_tr_c4, P_tr_c5, P_tr_c6, P_tr_c7, K_n1,
        K_n1_c1, K_n1_c2, K_n1_c3, K_n1_c4, K_n1_c5, K_n1_c6, K_n1_c7, K_cd, δr_0, δr_1, δr_2,
        δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

def K_n2_c1 : ZExp 6 := 36 * a ^ 10 * x ^ 6 - 32 * a ^ 10 * x ^ 4 - 72 * a ^ 8 * d * x ^ 6
    + 64 * a ^ 8 * d * x ^ 4 - 16 * a ^ 8 * r ^ 2 * x ^ 8
    + 148 * a ^ 8 * r ^ 2 * x ^ 6 - 188 * a ^ 8 * r ^ 2 * x ^ 4 + 64 * a ^ 8 * r ^ 2 * x ^ 2
    + 16 * a ^ 8 * r * v * x ^ 8 - 44 * a ^ 8 * r * v * x ^ 6
    + 20 * a ^ 8 * r * v * x ^ 4 - 4 * a ^ 8 * v ^ 2 * x ^ 8 + 3 * a ^ 8 * v ^ 2 * x ^ 6
    + 36 * a ^ 6 * d ^ 2 * x ^ 6 - 32 * a ^ 6 * d ^ 2 * x ^ 4 - 136 * a ^ 6 * d * r ^ 2 * x ^ 6

def K_n2_c2 : ZExp 6 := 272 * a ^ 6 * d * r ^ 2 * x ^ 4 - 128 * a ^ 6 * d * r ^ 2 * x ^ 2
    + 32 * a ^ 6 * d * r * v * x ^ 6 - 20 * a ^ 6 * d * r * v * x ^ 4
    + 64 * a ^ 6 * r ^ 4 * x ^ 6 - 124 * a ^ 6 * r ^ 4 * x ^ 4 + 60 * a ^ 6 * r ^ 4 * x ^ 2
    + 4 * a ^ 6 * r ^ 3 * v * x ^ 6 - 52 * a ^ 6 * r ^ 3 * v * x ^ 4
    + 24 * a ^ 6 * r ^ 3 * v * x ^ 2 - 9 * a ^ 6 * r ^ 2 * v ^ 2 * x ^ 6
    + 7 * a ^ 6 * r ^ 2 * v ^ 2 * x ^ 4 - 84 * a ^ 4 * d ^ 2 * r ^ 2 * x ^ 4

def K_n2_c3 : ZExp 6 := 64 * a ^ 4 * d ^ 2 * r ^ 2 * x ^ 2
    + 80 * a ^ 4 * d * r ^ 4 * x ^ 4 - 40 * a ^ 4 * d * r ^ 4 * x ^ 2
    + 44 * a ^ 4 * d * r ^ 3 * v * x ^ 4 - 24 * a ^ 4 * d * r ^ 3 * v * x ^ 2
    - 16 * a ^ 4 * r ^ 6 * x ^ 4
    + 12 * a ^ 4 * r ^ 6 * x ^ 2 - 4 * a ^ 4 * r ^ 6 - 24 * a ^ 4 * r ^ 5 * v * x ^ 4
    - 4 * a ^ 4 * r ^ 5 * v * x ^ 2 + 4 * a ^ 4 * r ^ 5 * v - 5 * a ^ 4 * r ^ 4 * v ^ 2 * x ^ 4
    + 5 * a ^ 4 * r ^ 4 * v ^ 2 * x ^ 2 - 20 * a ^ 2 * d ^ 2 * r ^ 4 * x ^ 2

def K_n2_c4 : ZExp 6 := 24 * a ^ 2 * d * r ^ 6 * x ^ 2
    + 8 * a ^ 2 * d * r ^ 5 * v * x ^ 2 - 4 * a ^ 2 * d * r ^ 5 * v - 4 * a ^ 2 * r ^ 8
    - 12 * a ^ 2 * r ^ 7 * v * x ^ 2 + 4 * a ^ 2 * r ^ 7 * v + a ^ 2 * r ^ 6 * v ^ 2 * x ^ 2
    + a ^ 2 * r ^ 6 * v ^ 2 + 4 * d ^ 2 * r ^ 6 - 4 * d * r ^ 7 * v + r ^ 8 * v ^ 2

/-- The numerator of `4 P_{tx}` over the common denominator. -/
def K_n2 : ZExp 6 := K_n2_c1 + K_n2_c2 + K_n2_c3 + K_n2_c4
set_option maxRecDepth 20000 in
/-- `4 P_{tx}`, reduced to the common denominator. -/
theorem K_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.ofZ 4 * P_tx) (⟨K_n2, K_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [P_tx, P_tx_c1, P_tx_c2, P_tx_c3, P_tx_c4, K_n2, K_n2_c1, K_n2_c2, K_n2_c3,
        K_n2_c4, K_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)



/-- The numerator of `4 P_{tp}` over the common denominator. -/
def K_n3 : ZExp 6 := -((a ^ 2 * x ^ 2 + r ^ 2) * (-2 * a ^ 4 * x ^ 2
    + 2 * a ^ 3 * r * x ^ 3 - 4 * a ^ 3 * r * x - a ^ 3 * v * x ^ 3
    + 2 * a ^ 2 * d * x ^ 2 - 4 * a ^ 2 * r ^ 2 * x ^ 2 + 2 * a ^ 2 * r ^ 2
    + a ^ 2 * r * v * x ^ 2
    + 4 * a * d * r * x - 2 * a * r ^ 3 * x - a * r ^ 2 * v * x - 2 * d * r ^ 2
    + r ^ 3 * v) * (2 * a ^ 4 * x ^ 2
    + 2 * a ^ 3 * r * x ^ 3 - 4 * a ^ 3 * r * x - a ^ 3 * v * x ^ 3 - 2 * a ^ 2 * d * x ^ 2
    + 4 * a ^ 2 * r ^ 2 * x ^ 2 - 2 * a ^ 2 * r ^ 2 - a ^ 2 * r * v * x ^ 2
    + 4 * a * d * r * x - 2 * a * r ^ 3 * x - a * r ^ 2 * v * x + 2 * d * r ^ 2 - r ^ 3 * v))
/-- `4 P_{tp}`, reduced to the common denominator. -/
theorem K_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.ofZ 4 * P_tp) (⟨K_n3, K_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [P_tp, K_n3, K_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)



/-- The numerator of `4 P_{rx}` over the common denominator. -/
def K_n4 : ZExp 6 := -((a ^ 2 * x ^ 2 + r ^ 2) * (-2 * a ^ 4 * x ^ 2
    + 2 * a ^ 3 * r * x ^ 3 - 4 * a ^ 3 * r * x - a ^ 3 * v * x ^ 3
    + 2 * a ^ 2 * d * x ^ 2 - 4 * a ^ 2 * r ^ 2 * x ^ 2 + 2 * a ^ 2 * r ^ 2
    + a ^ 2 * r * v * x ^ 2
    + 4 * a * d * r * x - 2 * a * r ^ 3 * x - a * r ^ 2 * v * x - 2 * d * r ^ 2
    + r ^ 3 * v) * (2 * a ^ 4 * x ^ 2
    + 2 * a ^ 3 * r * x ^ 3 - 4 * a ^ 3 * r * x - a ^ 3 * v * x ^ 3 - 2 * a ^ 2 * d * x ^ 2
    + 4 * a ^ 2 * r ^ 2 * x ^ 2 - 2 * a ^ 2 * r ^ 2 - a ^ 2 * r * v * x ^ 2
    + 4 * a * d * r * x - 2 * a * r ^ 3 * x - a * r ^ 2 * v * x + 2 * d * r ^ 2 - r ^ 3 * v))
/-- `4 P_{rx}`, reduced to the common denominator. -/
theorem K_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.ofZ 4 * P_rx) (⟨K_n4, K_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [P_rx, K_n4, K_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

def K_n5_c1 : ZExp 6 := a ^ 10 * w ^ 2 * x ^ 10 - a ^ 10 * w ^ 2 * x ^ 8
    - 4 * a ^ 10 * w * x ^ 10 + 8 * a ^ 10 * w * x ^ 8 - 4 * a ^ 10 * w * x ^ 6
    + 4 * a ^ 10 * x ^ 10 - 12 * a ^ 10 * x ^ 8 + 12 * a ^ 10 * x ^ 6 - 4 * a ^ 8 * d * w * x ^ 8
    + 4 * a ^ 8 * d * w * x ^ 6 + 8 * a ^ 8 * d * x ^ 8 - 16 * a ^ 8 * d * x ^ 6
    + 4 * a ^ 8 * r ^ 2 * w ^ 2 * x ^ 8 - 4 * a ^ 8 * r ^ 2 * w ^ 2 * x ^ 6
    + 4 * a ^ 8 * r ^ 2 * w * x ^ 8 - 8 * a ^ 8 * r ^ 2 * w * x ^ 6

def K_n5_c2 : ZExp 6 := 4 * a ^ 8 * r ^ 2 * w * x ^ 4 - 40 * a ^ 8 * r ^ 2 * x ^ 8
    + 148 * a ^ 8 * r ^ 2 * x ^ 6 - 164 * a ^ 8 * r ^ 2 * x ^ 4
    + 64 * a ^ 8 * r ^ 2 * x ^ 2 - 8 * a ^ 8 * r * v * w * x ^ 8 + 8 * a ^ 8 * r * v * w * x ^ 6
    + 32 * a ^ 8 * r * v * x ^ 8 - 76 * a ^ 8 * r * v * x ^ 6
    + 36 * a ^ 8 * r * v * x ^ 4 - 4 * a ^ 8 * v ^ 2 * x ^ 8 + 3 * a ^ 8 * v ^ 2 * x ^ 6
    + 4 * a ^ 6 * d ^ 2 * x ^ 6 + 4 * a ^ 6 * d * r ^ 2 * w * x ^ 6

def K_n5_c3 : ZExp 6 := 4 * a ^ 6 * d * r ^ 2 * w * x ^ 4
    + 112 * a ^ 6 * d * r ^ 2 * x ^ 6 - 248 * a ^ 6 * d * r ^ 2 * x ^ 4
    + 128 * a ^ 6 * d * r ^ 2 * x ^ 2 - 48 * a ^ 6 * d * r * v * x ^ 6
    + 36 * a ^ 6 * d * r * v * x ^ 4 - 6 * a ^ 6 * r ^ 4 * w ^ 2 * x ^ 6
    + 6 * a ^ 6 * r ^ 4 * w ^ 2 * x ^ 4 - 20 * a ^ 6 * r ^ 4 * w * x ^ 6
    + 40 * a ^ 6 * r ^ 4 * w * x ^ 4 - 20 * a ^ 6 * r ^ 4 * w * x ^ 2
    - 64 * a ^ 6 * r ^ 4 * x ^ 6 + 148 * a ^ 6 * r ^ 4 * x ^ 4

def K_n5_c4 : ZExp 6 := 116 * a ^ 6 * r ^ 4 * x ^ 2 - 32 * a ^ 6 * r ^ 4
    - 24 * a ^ 6 * r ^ 3 * v * w * x ^ 6
    + 24 * a ^ 6 * r ^ 3 * v * w * x ^ 4 - 28 * a ^ 6 * r ^ 3 * v * x ^ 6
    + 12 * a ^ 6 * r ^ 3 * v * x ^ 4 - 8 * a ^ 6 * r ^ 3 * v * x ^ 2
    + 7 * a ^ 6 * r ^ 2 * v ^ 2 * x ^ 6 - 9 * a ^ 6 * r ^ 2 * v ^ 2 * x ^ 4
    - 84 * a ^ 4 * d ^ 2 * r ^ 2 * x ^ 4 + 64 * a ^ 4 * d ^ 2 * r ^ 2 * x ^ 2
    + 20 * a ^ 4 * d * r ^ 4 * w * x ^ 4 - 20 * a ^ 4 * d * r ^ 4 * w * x ^ 2

def K_n5_c5 : ZExp 6 := 104 * a ^ 4 * d * r ^ 4 * x ^ 4 - 128 * a ^ 4 * d * r ^ 4 * x ^ 2
    + 64 * a ^ 4 * d * r ^ 4 + 12 * a ^ 4 * d * r ^ 3 * v * x ^ 4
    + 8 * a ^ 4 * d * r ^ 3 * v * x ^ 2
    + 4 * a ^ 4 * r ^ 6 * w ^ 2 * x ^ 4 - 4 * a ^ 4 * r ^ 6 * w ^ 2 * x ^ 2
    + 12 * a ^ 4 * r ^ 6 * w * x ^ 4 - 24 * a ^ 4 * r ^ 6 * w * x ^ 2 + 12 * a ^ 4 * r ^ 6 * w
    + 8 * a ^ 4 * r ^ 6 * x ^ 4 - 20 * a ^ 4 * r ^ 6 * x ^ 2
    + 4 * a ^ 4 * r ^ 6 - 24 * a ^ 4 * r ^ 5 * v * w * x ^ 4

def K_n5_c6 : ZExp 6 := 24 * a ^ 4 * r ^ 5 * v * w * x ^ 2 - 72 * a ^ 4 * r ^ 5 * v * x ^ 4
    + 92 * a ^ 4 * r ^ 5 * v * x ^ 2 - 44 * a ^ 4 * r ^ 5 * v
    + 27 * a ^ 4 * r ^ 4 * v ^ 2 * x ^ 4 - 27 * a ^ 4 * r ^ 4 * v ^ 2 * x ^ 2
    + 12 * a ^ 2 * d ^ 2 * r ^ 4 * x ^ 2 - 32 * a ^ 2 * d ^ 2 * r ^ 4
    + 12 * a ^ 2 * d * r ^ 6 * w * x ^ 2 - 12 * a ^ 2 * d * r ^ 6 * w
    + 32 * a ^ 2 * d * r ^ 6 * x ^ 2 - 8 * a ^ 2 * d * r ^ 6 - 40 * a ^ 2 * d * r ^ 5 * v * x ^ 2

def K_n5_c7 : ZExp 6 := 44 * a ^ 2 * d * r ^ 5 * v
    + a ^ 2 * r ^ 8 * w ^ 2 * x ^ 2 - a ^ 2 * r ^ 8 * w ^ 2 - 4 * a ^ 2 * r ^ 8 * x ^ 2
    - 8 * a ^ 2 * r ^ 7 * v * w * x ^ 2
    + 8 * a ^ 2 * r ^ 7 * v * w - 12 * a ^ 2 * r ^ 7 * v * x ^ 2 + 4 * a ^ 2 * r ^ 7 * v
    + 17 * a ^ 2 * r ^ 6 * v ^ 2 * x ^ 2 - 15 * a ^ 2 * r ^ 6 * v ^ 2
    + 4 * d ^ 2 * r ^ 6 - 4 * d * r ^ 7 * v + r ^ 8 * v ^ 2

/-- The numerator of `4 P_{rp}` over the common denominator. -/
def K_n5 : ZExp 6 := K_n5_c1 + K_n5_c2 - K_n5_c3 + K_n5_c4 + K_n5_c5 + K_n5_c6 + K_n5_c7
set_option maxRecDepth 20000 in
/-- `4 P_{rp}`, reduced to the common denominator. -/
theorem K_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.ofZ 4 * P_rp) (⟨K_n5, K_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [P_rp, P_rp_c1, P_rp_c2, P_rp_c3, P_rp_c4, P_rp_c5, P_rp_c6, P_rp_c7, K_n5,
        K_n5_c1, K_n5_c2, K_n5_c3, K_n5_c4, K_n5_c5, K_n5_c6, K_n5_c7, K_cd, δr_0, δr_1, δr_2,
        δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

def K_n6_c1 : ZExp 6 := 4 * a ^ 10 * x ^ 6
    + 32 * a ^ 10 * x ^ 4 - 8 * a ^ 8 * d * x ^ 6 - 64 * a ^ 8 * d * x ^ 4
    - 4 * a ^ 8 * r ^ 2 * x ^ 8 + 20 * a ^ 8 * r ^ 2 * x ^ 6
    + 116 * a ^ 8 * r ^ 2 * x ^ 4 - 64 * a ^ 8 * r ^ 2 * x ^ 2
    + 4 * a ^ 8 * r * v * x ^ 8 - 20 * a ^ 8 * r * v * x ^ 4 - a ^ 8 * v ^ 2 * x ^ 8
    - 3 * a ^ 8 * v ^ 2 * x ^ 6 + 4 * a ^ 6 * d ^ 2 * x ^ 6
    + 32 * a ^ 6 * d ^ 2 * x ^ 4 - 32 * a ^ 6 * d * r ^ 2 * x ^ 6 - 128 * a ^ 6 * d * r ^ 2 * x ^ 4

def K_n6_c2 : ZExp 6 := 128 * a ^ 6 * d * r ^ 2 * x ^ 2 + 12 * a ^ 6 * d * r * v * x ^ 6
    + 20 * a ^ 6 * d * r * v * x ^ 4 + 8 * a ^ 6 * r ^ 4 * x ^ 6
    + 148 * a ^ 6 * r ^ 4 * x ^ 4 - 164 * a ^ 6 * r ^ 4 * x ^ 2
    + 8 * a ^ 6 * r ^ 3 * v * x ^ 6 - 32 * a ^ 6 * r ^ 3 * v * x ^ 4
    - 24 * a ^ 6 * r ^ 3 * v * x ^ 2 - 5 * a ^ 6 * r ^ 2 * v ^ 2 * x ^ 6
    - 7 * a ^ 6 * r ^ 2 * v ^ 2 * x ^ 4
    + 12 * a ^ 4 * d ^ 2 * r ^ 2 * x ^ 4 - 64 * a ^ 4 * d ^ 2 * r ^ 2 * x ^ 2

def K_n6_c3 : ZExp 6 := 104 * a ^ 4 * d * r ^ 4 * x ^ 4 - 248 * a ^ 4 * d * r ^ 4 * x ^ 2
    - 40 * a ^ 4 * d * r ^ 3 * v * x ^ 4 - 24 * a ^ 4 * d * r ^ 3 * v * x ^ 2
    - 64 * a ^ 4 * r ^ 6 * x ^ 4 + 148 * a ^ 4 * r ^ 6 * x ^ 2 - 12 * a ^ 4 * r ^ 6
    + 12 * a ^ 4 * r ^ 5 * v * x ^ 4 + 32 * a ^ 4 * r ^ 5 * v * x ^ 2 + 4 * a ^ 4 * r ^ 5 * v
    + 7 * a ^ 4 * r ^ 4 * v ^ 2 * x ^ 4 + 5 * a ^ 4 * r ^ 4 * v ^ 2 * x ^ 2
    + 84 * a ^ 2 * d ^ 2 * r ^ 4 * x ^ 2

def K_n6_c4 : ZExp 6 := 112 * a ^ 2 * d * r ^ 6 * x ^ 2 - 16 * a ^ 2 * d * r ^ 6
    + 28 * a ^ 2 * d * r ^ 5 * v * x ^ 2 + 4 * a ^ 2 * d * r ^ 5 * v - 40 * a ^ 2 * r ^ 8 * x ^ 2
    + 12 * a ^ 2 * r ^ 8 - 16 * a ^ 2 * r ^ 7 * v * x ^ 2 - 3 * a ^ 2 * r ^ 6 * v ^ 2 * x ^ 2
    - a ^ 2 * r ^ 6 * v ^ 2 + 4 * d ^ 2 * r ^ 6 - 8 * d * r ^ 8 + 4 * r ^ 10

/-- The numerator of `4 P_{xp}` over the common denominator. -/
def K_n6 : ZExp 6 := K_n6_c1 + K_n6_c2 - K_n6_c3 + K_n6_c4
set_option maxRecDepth 20000 in
/-- `4 P_{xp}`, reduced to the common denominator. -/
theorem K_t6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.ofZ 4 * P_xp) (⟨K_n6, K_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [P_xp, P_xp_c1, P_xp_c2, P_xp_c3, P_xp_c4, K_n6, K_n6_c1, K_n6_c2, K_n6_c3,
        K_n6_c4, K_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `eq:paircontract`: `𝒦 = R_{αβγδ} R^{αβγδ} = 4 tr(C J C J)` for the radial-function metric is
`Kf`. -/
theorem kretschmann_radial :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨K_n1 + K_n2 + K_n3 + K_n4 + K_n5 + K_n6, K_cd⟩) (Kf))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [K_n1, K_n1_c1, K_n1_c2, K_n1_c3, K_n1_c4, K_n1_c5, K_n1_c6, K_n1_c7, K_n2,
        K_n2_c1, K_n2_c2, K_n2_c3, K_n2_c4, K_n3, K_n4, K_n5, K_n5_c1, K_n5_c2, K_n5_c3, K_n5_c4,
        K_n5_c5, K_n5_c6, K_n5_c7, K_n6, K_n6_c1, K_n6_c2, K_n6_c3, K_n6_c4, K_cd, Kf, Kf_c1,
        Kf_c2, Kf_c3, Kf_c4, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ## The Kerr–Newman specialization -/

section KN

open LeanProofs.IPRA.Geometry.KerrNewmanRicci (knHyps)
open LeanProofs.IPRA.Geometry.KerrNewmanEinstein (ι₆ ι₆_0 ι₆_1 ι₆_2 ι₆_3 ι₆_4 ι₆_5)

local notation "R" => (ZExp.var 0 : ZExp 8)
local notation "X" => (ZExp.var 1 : ZExp 8)
local notation "A" => (ZExp.var 2 : ZExp 8)
local notation "M" => (ZExp.var 6 : ZExp 8)
local notation "Q" => (ZExp.var 7 : ZExp 8)

/-- The bracket of `eq:Kretschmann`: `𝒦 = 8 Kn/Σ⁶`. -/
def Kn : ZExp 8 :=
  6 * M ^ 2 * (R ^ 6 - 15 * R ^ 4 * A ^ 2 * X ^ 2 + 15 * R ^ 2 * A ^ 4 * X ^ 4 - A ^ 6 * X ^ 6)
    - 12 * M * Q ^ 2 * R * (R ^ 4 - 10 * R ^ 2 * A ^ 2 * X ^ 2 + 5 * A ^ 4 * X ^ 4)
    + Q ^ 4 * (7 * R ^ 4 - 34 * R ^ 2 * A ^ 2 * X ^ 2 + 7 * A ^ 4 * X ^ 4)

/-- `eq:Kretschmann`: for `d = Δ`, `v = 2r − 2m`, `w = 2`, the Kretschmann scalar of the
radial-function metric is `8 Kn/Σ⁶`. -/
theorem kn_kretschmann :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp knHyps (Frac.eqn (Frac.rename ι₆ Kf) ⟨8 * Kn, (R ^ 2 + A ^ 2 * X ^ 2) ^ 6⟩)) :=
  derive_imp _ _ (by
    frac_poly S ρ h [Frac.rename_num, Frac.rename_den, eval_rename, Kf, Kf_c1, Kf_c2, Kf_c3,
        Kf_c4, Kn, ι₆_0, ι₆_1, ι₆_2, ι₆_3, ι₆_4, ι₆_5]
    obtain ⟨h₁, h₂, h₃⟩ := h
    simp only [h₁, h₂, h₃]
    ring)

end KN

end LeanProofs.IPRA.Geometry.KerrNewmanKretschmann
