import IPRADerivations.Geometry.KerrNewmanPairMatrix

/-!
# The product `M = C J` of the pair matrices, part B (`four_metrics_ipra`)

Packet: `geometry/four_metrics_ipra_2026-11-15`, `eq:paircontract` (`𝒦 = 4 tr(C J C J)`): with the
    pair
matrix `C` and the pair inverse `J` of `Geometry/KerrNewmanPairMatrix`, `product_IK` with `M_I_K_tn`
certifies each entry `M_{IK} = Σ_J C_{IJ} J_{JK}` (terms reduced over a common denominator, the sum
equal to the reduced fraction `M_I_K` or `0`). The entries are split between
`Geometry/KerrNewmanPairProductA` and `…B` (this is part B);
the trace is `Geometry/KerrNewmanKretschmann`.

The reduced fractions and numerators were proposed by a computer algebra script; every identity
is checked by Lean as an identity of fractions cleared of denominators, a closed sentence of iPRA
certified in every commutative ring.
-/

namespace LeanProofs.IPRA.Geometry.KerrNewmanPairProductB

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Geometry.KerrNewmanBase (δr δx δr_0 δr_1 δr_2 δr_3 δr_4 δr_5 δx_0 δx_1 δx_2
  δx_3 δx_4 δx_5 Sg sx)
open LeanProofs.IPRA.Geometry.KerrNewmanConnection
open LeanProofs.IPRA.Geometry.KerrNewmanRiemannT
open LeanProofs.IPRA.Geometry.KerrNewmanRiemannR
open LeanProofs.IPRA.Geometry.KerrNewmanRiemannX
open LeanProofs.IPRA.Geometry.KerrNewmanRiemannP
open LeanProofs.IPRA.Geometry.KerrNewmanPairMatrix
open ZExp

local notation "r" => (ZExp.var 0 : ZExp 6)
local notation "x" => (ZExp.var 1 : ZExp 6)
local notation "a" => (ZExp.var 2 : ZExp 6)
local notation "d" => (ZExp.var 3 : ZExp 6)
local notation "v" => (ZExp.var 4 : ZExp 6)
local notation "w" => (ZExp.var 5 : ZExp 6)

/-! ## The product `M = C J` -/

/-! ### `M_{rx,tp}` -/

/-- `M_{rx,tp}`, reduced. -/
def M_rx_tp : Frac 6 := ⟨-a * x * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 *
    d * r - 2 * r ^ 3 - r ^ 2 * v), 2 * d * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2⟩

/-- The common denominator of the terms of `M_{rx,tp}`. -/
def M_rx_tp_cd : ZExp 6 := 2 * d * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2

/-- The numerator of `C_{rx,tp} J_{tp,tp}` over the common denominator. -/
def M_rx_tp_n1 : ZExp 6 := -a * x * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4
    * d * r - 2 * r ^ 3 - r ^ 2 * v)
/-- `C_{rx,tp} J_{tp,tp}`, reduced to the common denominator. -/
theorem M_rx_tp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (C_rx_tp * J_tp_tp) (⟨M_rx_tp_n1, M_rx_tp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_rx_tp, J_tp_tp, M_rx_tp_n1, M_rx_tp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `M_{rx,tp} = Σ_J C_{rx,J} J_{J,tp}`: the reduced fraction. -/
theorem product_rx_tp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨M_rx_tp_n1, M_rx_tp_cd⟩) (M_rx_tp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [M_rx_tp_n1, M_rx_tp_cd, M_rx_tp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5])

/-! ### `M_{rx,rx}` -/

/-- `M_{rx,rx}`, reduced. -/
def M_rx_rx : Frac 6 := ⟨2 * a ^ 4 * x ^ 2 - 2 * a ^ 2 * d * x ^ 2 + 4 * a ^ 2 * r ^ 2 * x ^ 2 - 2
    * a ^ 2 * r ^ 2 - a ^ 2 * r * v * x ^ 2 + 2 * d * r ^ 2 - r ^ 3 * v, 2 * (a ^ 2 * x ^ 2 + r ^
    2) ^ 3⟩

/-- The common denominator of the terms of `M_{rx,rx}`. -/
def M_rx_rx_cd : ZExp 6 := 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3

/-- The numerator of `C_{rx,rx} J_{rx,rx}` over the common denominator. -/
def M_rx_rx_n1 : ZExp 6 := 2 * a ^ 4 * x ^ 2 - 2 * a ^ 2 * d * x ^ 2 + 4 * a ^ 2 * r ^ 2 * x ^ 2 -
    2 * a ^ 2 * r ^ 2 - a ^ 2 * r * v * x ^ 2 + 2 * d * r ^ 2 - r ^ 3 * v
/-- `C_{rx,rx} J_{rx,rx}`, reduced to the common denominator. -/
theorem M_rx_rx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (C_rx_rx * J_rx_rx) (⟨M_rx_rx_n1, M_rx_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_rx_rx, J_rx_rx, M_rx_rx_n1, M_rx_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `M_{rx,rx} = Σ_J C_{rx,J} J_{J,rx}`: the reduced fraction. -/
theorem product_rx_rx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨M_rx_rx_n1, M_rx_rx_cd⟩) (M_rx_rx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [M_rx_rx_n1, M_rx_rx_cd, M_rx_rx, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5])

/-! ### `M_{rp,tr}` -/

/-- `M_{rp,tr}`, reduced. -/
def M_rp_tr : Frac 6 := ⟨a * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 4 * w * x ^ 4 - 2 * a ^ 4 *
    x ^ 4 + 4 * a ^ 4 * x ^ 2 - 4 * a ^ 2 * d * x ^ 2 + 2 * a ^ 2 * r ^ 2 * w * x ^ 2 + 10 * a ^ 2
    * r ^ 2 * x ^ 2 - 8 * a ^ 2 * r ^ 2 - 5 * a ^ 2 * r * v * x ^ 2 + 8 * d * r ^ 2 + r ^ 4 * w - 5
    * r ^ 3 * v), 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4⟩

/-- The common denominator of the terms of `M_{rp,tr}`. -/
def M_rp_tr_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `C_{rp,tr} J_{tr,tr}` over the common denominator. -/
def M_rp_tr_n1 : ZExp 6 := a * (x - 1) * (x + 1) * (a ^ 4 + a ^ 2 * d * x ^ 2 - a ^ 2 * d + 2 * a ^
    2 * r ^ 2 + r ^ 4) * (2 * a ^ 6 * x ^ 2 + a ^ 4 * d * w * x ^ 4 - 2 * a ^ 4 * d * x ^ 4 + 6 * a
    ^ 4 * r ^ 2 * x ^ 2 - 2 * a ^ 4 * r ^ 2 - a ^ 4 * r * v * x ^ 2 - 2 * a ^ 2 * d ^ 2 * x ^ 2 + 2
    * a ^ 2 * d * r ^ 2 * w * x ^ 2 + 4 * a ^ 2 * d * r ^ 2 * x ^ 2 - 4 * a ^ 2 * d * r ^ 2 - 4 * a
    ^ 2 * d * r * v * x ^ 2 + 4 * a ^ 2 * r ^ 4 * x ^ 2 - 2 * a ^ 2 * r ^ 4 - a ^ 2 * r ^ 3 * v * x
    ^ 2 - a ^ 2 * r ^ 3 * v + 6 * d ^ 2 * r ^ 2 + d * r ^ 4 * w + 2 * d * r ^ 4 - 4 * d * r ^ 3 * v
    - r ^ 5 * v)
/-- `C_{rp,tr} J_{tr,tr}`, reduced to the common denominator. -/
theorem M_rp_tr_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (C_rp_tr * J_tr_tr) (⟨M_rp_tr_n1, M_rp_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_rp_tr, J_tr_tr, M_rp_tr_n1, M_rp_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `C_{rp,rp} J_{rp,tr}` over the common denominator. -/
def M_rp_tr_n2 : ZExp 6 := a * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) * (-2 * a ^ 8 * x ^ 2 + a ^
    6 * d * w * x ^ 6 - a ^ 6 * d * w * x ^ 4 - 2 * a ^ 6 * d * x ^ 6 + 4 * a ^ 6 * d * x ^ 4 - 8 *
    a ^ 6 * r ^ 2 * x ^ 2 + 2 * a ^ 6 * r ^ 2 + a ^ 6 * r * v * x ^ 2 - 2 * a ^ 4 * d ^ 2 * x ^ 4 +
    2 * a ^ 4 * d ^ 2 * x ^ 2 + 2 * a ^ 4 * d * r ^ 2 * w * x ^ 4 - 2 * a ^ 4 * d * r ^ 2 * w * x ^
    2 + 6 * a ^ 4 * d * r ^ 2 * x ^ 4 - 8 * a ^ 4 * d * r ^ 2 * x ^ 2 + 4 * a ^ 4 * d * r ^ 2 - 4 *
    a ^ 4 * d * r * v * x ^ 4 + 4 * a ^ 4 * d * r * v * x ^ 2 - 10 * a ^ 4 * r ^ 4 * x ^ 2 + 4 * a
    ^ 4 * r ^ 4 + 2 * a ^ 4 * r ^ 3 * v * x ^ 2 + a ^ 4 * r ^ 3 * v + 6 * a ^ 2 * d ^ 2 * r ^ 2 * x
    ^ 2 - 6 * a ^ 2 * d ^ 2 * r ^ 2 + a ^ 2 * d * r ^ 4 * w * x ^ 2 - a ^ 2 * d * r ^ 4 * w + 2 * a
    ^ 2 * d * r ^ 4 * x ^ 2 - 4 * a ^ 2 * d * r ^ 4 - 4 * a ^ 2 * d * r ^ 3 * v * x ^ 2 + 4 * a ^ 2
    * d * r ^ 3 * v - 4 * a ^ 2 * r ^ 6 * x ^ 2 + 2 * a ^ 2 * r ^ 6 + a ^ 2 * r ^ 5 * v * x ^ 2 + 2
    * a ^ 2 * r ^ 5 * v - 2 * d * r ^ 6 + r ^ 7 * v)
/-- `C_{rp,rp} J_{rp,tr}`, reduced to the common denominator. -/
theorem M_rp_tr_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (C_rp_rp * J_rp_tr) (⟨M_rp_tr_n2, M_rp_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_rp_rp, J_rp_tr, M_rp_tr_n2, M_rp_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `M_{rp,tr} = Σ_J C_{rp,J} J_{J,tr}`: the reduced fraction. -/
theorem product_rp_tr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨M_rp_tr_n1 + M_rp_tr_n2, M_rp_tr_cd⟩) (M_rp_tr))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [M_rp_tr_n1, M_rp_tr_n2, M_rp_tr_cd, M_rp_tr, δr_0, δr_1, δr_2, δr_3, δr_4,
        δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `M_{rp,tx}` -/

/-- `M_{rp,tx}`, reduced. -/
def M_rp_tx : Frac 6 := ⟨-a * x * (x - 1) * (x + 1) * (-a ^ 4 + 2 * a ^ 2 * d * x ^ 2 - 2 * a ^ 2 *
    d - 2 * a ^ 2 * r ^ 2 - r ^ 4) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4
    * d * r - 2 * r ^ 3 - r ^ 2 * v), 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4⟩

/-- The common denominator of the terms of `M_{rp,tx}`. -/
def M_rp_tx_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `C_{rp,tx} J_{tx,tx}` over the common denominator. -/
def M_rp_tx_n1 : ZExp 6 := -a * x * (x - 1) * (x + 1) * (2 * a ^ 2 * x ^ 2 - 3 * a ^ 2 - r ^ 2) *
    (a ^ 4 + a ^ 2 * d * x ^ 2 - a ^ 2 * d + 2 * a ^ 2 * r ^ 2 + r ^ 4) * (2 * a ^ 2 * r * x ^ 2 -
    4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v)
/-- `C_{rp,tx} J_{tx,tx}`, reduced to the common denominator. -/
theorem M_rp_tx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (C_rp_tx * J_tx_tx) (⟨M_rp_tx_n1, M_rp_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_rp_tx, J_tx_tx, M_rp_tx_n1, M_rp_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `C_{rp,xp} J_{xp,tx}` over the common denominator. -/
def M_rp_tx_n2 : ZExp 6 := 3 * a ^ 3 * x * (a ^ 2 + r ^ 2) * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 - d
    + r ^ 2) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 -
    r ^ 2 * v)
/-- `C_{rp,xp} J_{xp,tx}`, reduced to the common denominator. -/
theorem M_rp_tx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (C_rp_xp * J_xp_tx) (⟨M_rp_tx_n2, M_rp_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_rp_xp, J_xp_tx, M_rp_tx_n2, M_rp_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `M_{rp,tx} = Σ_J C_{rp,J} J_{J,tx}`: the reduced fraction. -/
theorem product_rp_tx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨M_rp_tx_n1 + M_rp_tx_n2, M_rp_tx_cd⟩) (M_rp_tx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [M_rp_tx_n1, M_rp_tx_n2, M_rp_tx_cd, M_rp_tx, δr_0, δr_1, δr_2, δr_3, δr_4,
        δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `M_{rp,rp}` -/

/-- `M_{rp,rp}`, reduced. -/
def M_rp_rp : Frac 6 := ⟨-a ^ 6 * w * x ^ 6 + a ^ 6 * w * x ^ 4 + 2 * a ^ 6 * x ^ 6 - 4 * a ^ 6 * x
    ^ 4 + 4 * a ^ 6 * x ^ 2 + 2 * a ^ 4 * d * x ^ 4 - 4 * a ^ 4 * d * x ^ 2 - 2 * a ^ 4 * r ^ 2 * w
    * x ^ 4 + 2 * a ^ 4 * r ^ 2 * w * x ^ 2 - 6 * a ^ 4 * r ^ 2 * x ^ 4 + 18 * a ^ 4 * r ^ 2 * x ^
    2 - 8 * a ^ 4 * r ^ 2 + 4 * a ^ 4 * r * v * x ^ 4 - 5 * a ^ 4 * r * v * x ^ 2 - 8 * a ^ 2 * d *
    r ^ 2 * x ^ 2 + 8 * a ^ 2 * d * r ^ 2 - a ^ 2 * r ^ 4 * w * x ^ 2 + a ^ 2 * r ^ 4 * w + 4 * a ^
    2 * r ^ 4 * x ^ 2 - 2 * a ^ 2 * r ^ 4 + 3 * a ^ 2 * r ^ 3 * v * x ^ 2 - 5 * a ^ 2 * r ^ 3 * v +
    2 * d * r ^ 4 - r ^ 5 * v, 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4⟩

/-- The common denominator of the terms of `M_{rp,rp}`. -/
def M_rp_rp_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `C_{rp,tr} J_{tr,rp}` over the common denominator. -/
def M_rp_rp_n1 : ZExp 6 := -a ^ 2 * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) * (2 * a ^ 6 * x ^ 2 +
    a ^ 4 * d * w * x ^ 4 - 2 * a ^ 4 * d * x ^ 4 + 6 * a ^ 4 * r ^ 2 * x ^ 2 - 2 * a ^ 4 * r ^ 2 -
    a ^ 4 * r * v * x ^ 2 - 2 * a ^ 2 * d ^ 2 * x ^ 2 + 2 * a ^ 2 * d * r ^ 2 * w * x ^ 2 + 4 * a ^
    2 * d * r ^ 2 * x ^ 2 - 4 * a ^ 2 * d * r ^ 2 - 4 * a ^ 2 * d * r * v * x ^ 2 + 4 * a ^ 2 * r ^
    4 * x ^ 2 - 2 * a ^ 2 * r ^ 4 - a ^ 2 * r ^ 3 * v * x ^ 2 - a ^ 2 * r ^ 3 * v + 6 * d ^ 2 * r ^
    2 + d * r ^ 4 * w + 2 * d * r ^ 4 - 4 * d * r ^ 3 * v - r ^ 5 * v)
/-- `C_{rp,tr} J_{tr,rp}`, reduced to the common denominator. -/
theorem M_rp_rp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (C_rp_tr * J_tr_rp) (⟨M_rp_rp_n1, M_rp_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_rp_tr, J_tr_rp, M_rp_rp_n1, M_rp_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `C_{rp,rp} J_{rp,rp}` over the common denominator. -/
def M_rp_rp_n2 : ZExp 6 := -(a ^ 2 * x ^ 2 - a ^ 2 + d) * (-2 * a ^ 8 * x ^ 2 + a ^ 6 * d * w * x ^
    6 - a ^ 6 * d * w * x ^ 4 - 2 * a ^ 6 * d * x ^ 6 + 4 * a ^ 6 * d * x ^ 4 - 8 * a ^ 6 * r ^ 2 *
    x ^ 2 + 2 * a ^ 6 * r ^ 2 + a ^ 6 * r * v * x ^ 2 - 2 * a ^ 4 * d ^ 2 * x ^ 4 + 2 * a ^ 4 * d ^
    2 * x ^ 2 + 2 * a ^ 4 * d * r ^ 2 * w * x ^ 4 - 2 * a ^ 4 * d * r ^ 2 * w * x ^ 2 + 6 * a ^ 4 *
    d * r ^ 2 * x ^ 4 - 8 * a ^ 4 * d * r ^ 2 * x ^ 2 + 4 * a ^ 4 * d * r ^ 2 - 4 * a ^ 4 * d * r *
    v * x ^ 4 + 4 * a ^ 4 * d * r * v * x ^ 2 - 10 * a ^ 4 * r ^ 4 * x ^ 2 + 4 * a ^ 4 * r ^ 4 + 2
    * a ^ 4 * r ^ 3 * v * x ^ 2 + a ^ 4 * r ^ 3 * v + 6 * a ^ 2 * d ^ 2 * r ^ 2 * x ^ 2 - 6 * a ^ 2
    * d ^ 2 * r ^ 2 + a ^ 2 * d * r ^ 4 * w * x ^ 2 - a ^ 2 * d * r ^ 4 * w + 2 * a ^ 2 * d * r ^ 4
    * x ^ 2 - 4 * a ^ 2 * d * r ^ 4 - 4 * a ^ 2 * d * r ^ 3 * v * x ^ 2 + 4 * a ^ 2 * d * r ^ 3 * v
    - 4 * a ^ 2 * r ^ 6 * x ^ 2 + 2 * a ^ 2 * r ^ 6 + a ^ 2 * r ^ 5 * v * x ^ 2 + 2 * a ^ 2 * r ^ 5
    * v - 2 * d * r ^ 6 + r ^ 7 * v)
/-- `C_{rp,rp} J_{rp,rp}`, reduced to the common denominator. -/
theorem M_rp_rp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (C_rp_rp * J_rp_rp) (⟨M_rp_rp_n2, M_rp_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_rp_rp, J_rp_rp, M_rp_rp_n2, M_rp_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `M_{rp,rp} = Σ_J C_{rp,J} J_{J,rp}`: the reduced fraction. -/
theorem product_rp_rp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨M_rp_rp_n1 + M_rp_rp_n2, M_rp_rp_cd⟩) (M_rp_rp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [M_rp_rp_n1, M_rp_rp_n2, M_rp_rp_cd, M_rp_rp, δr_0, δr_1, δr_2, δr_3, δr_4,
        δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `M_{rp,xp}` -/

/-- `M_{rp,xp}`, reduced. -/
def M_rp_xp : Frac 6 := ⟨-a ^ 2 * x * (x - 1) * (x + 1) * (a ^ 2 + 2 * d + r ^ 2) * (2 * a ^ 2 * r
    * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v), 2 * d * (a ^
    2 * x ^ 2 + r ^ 2) ^ 4⟩

/-- The common denominator of the terms of `M_{rp,xp}`. -/
def M_rp_xp_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `C_{rp,tx} J_{tx,xp}` over the common denominator. -/
def M_rp_xp_n1 : ZExp 6 := a ^ 2 * x * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) * (2 * a ^ 2 * x ^ 2
    - 3 * a ^ 2 - r ^ 2) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r -
    2 * r ^ 3 - r ^ 2 * v)
/-- `C_{rp,tx} J_{tx,xp}`, reduced to the common denominator. -/
theorem M_rp_xp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (C_rp_tx * J_tx_xp) (⟨M_rp_xp_n1, M_rp_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_rp_tx, J_tx_xp, M_rp_xp_n1, M_rp_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `C_{rp,xp} J_{xp,xp}` over the common denominator. -/
def M_rp_xp_n2 : ZExp 6 := -3 * a ^ 2 * x * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 -
    a ^ 2 + d) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3
    - r ^ 2 * v)
/-- `C_{rp,xp} J_{xp,xp}`, reduced to the common denominator. -/
theorem M_rp_xp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (C_rp_xp * J_xp_xp) (⟨M_rp_xp_n2, M_rp_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_rp_xp, J_xp_xp, M_rp_xp_n2, M_rp_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `M_{rp,xp} = Σ_J C_{rp,J} J_{J,xp}`: the reduced fraction. -/
theorem product_rp_xp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨M_rp_xp_n1 + M_rp_xp_n2, M_rp_xp_cd⟩) (M_rp_xp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [M_rp_xp_n1, M_rp_xp_n2, M_rp_xp_cd, M_rp_xp, δr_0, δr_1, δr_2, δr_3, δr_4,
        δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `M_{xp,tr}` -/

/-- `M_{xp,tr}`, reduced. -/
def M_xp_tr : Frac 6 := ⟨a * x * (-2 * a ^ 4 + a ^ 2 * d * x ^ 2 - a ^ 2 * d - 4 * a ^ 2 * r ^ 2 -
    2 * r ^ 4) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3
    - r ^ 2 * v), 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4⟩

/-- The common denominator of the terms of `M_{xp,tr}`. -/
def M_xp_tr_cd : ZExp 6 := 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `C_{xp,tr} J_{tr,tr}` over the common denominator. -/
def M_xp_tr_n1 : ZExp 6 := a * x * (a ^ 2 * x ^ 2 - 3 * a ^ 2 - 2 * r ^ 2) * (a ^ 4 + a ^ 2 * d * x
    ^ 2 - a ^ 2 * d + 2 * a ^ 2 * r ^ 2 + r ^ 4) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 *
    v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v)
/-- `C_{xp,tr} J_{tr,tr}`, reduced to the common denominator. -/
theorem M_xp_tr_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (C_xp_tr * J_tr_tr) (⟨M_xp_tr_n1, M_xp_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_xp_tr, J_tr_tr, M_xp_tr_n1, M_xp_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `C_{xp,rp} J_{rp,tr}` over the common denominator. -/
def M_xp_tr_n2 : ZExp 6 := -3 * a ^ 3 * x * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 - d + r ^
    2) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2
    * v)
/-- `C_{xp,rp} J_{rp,tr}`, reduced to the common denominator. -/
theorem M_xp_tr_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (C_xp_rp * J_rp_tr) (⟨M_xp_tr_n2, M_xp_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_xp_rp, J_rp_tr, M_xp_tr_n2, M_xp_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `M_{xp,tr} = Σ_J C_{xp,J} J_{J,tr}`: the reduced fraction. -/
theorem product_xp_tr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨M_xp_tr_n1 + M_xp_tr_n2, M_xp_tr_cd⟩) (M_xp_tr))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [M_xp_tr_n1, M_xp_tr_n2, M_xp_tr_cd, M_xp_tr, δr_0, δr_1, δr_2, δr_3, δr_4,
        δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `M_{xp,tx}` -/

/-- `M_{xp,tx}`, reduced. -/
def M_xp_tx : Frac 6 := ⟨-a * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (8 * a ^ 4 * x ^ 2 - 8 * a ^ 2
    * d * x ^ 2 + 10 * a ^ 2 * r ^ 2 * x ^ 2 - 4 * a ^ 2 * r ^ 2 - a ^ 2 * r * v * x ^ 2 + 4 * d *
    r ^ 2 - 2 * r ^ 4 - r ^ 3 * v), 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4⟩

/-- The common denominator of the terms of `M_{xp,tx}`. -/
def M_xp_tx_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `C_{xp,tx} J_{tx,tx}` over the common denominator. -/
def M_xp_tx_n1 : ZExp 6 := -a * (x - 1) * (x + 1) * (a ^ 4 + a ^ 2 * d * x ^ 2 - a ^ 2 * d + 2 * a
    ^ 2 * r ^ 2 + r ^ 4) * (6 * a ^ 6 * x ^ 2 - 4 * a ^ 4 * d * x ^ 2 + 12 * a ^ 4 * r ^ 2 * x ^ 2
    - 2 * a ^ 4 * r ^ 2 - 2 * a ^ 2 * d ^ 2 * x ^ 2 - 2 * a ^ 2 * d * r ^ 2 * x ^ 2 - a ^ 2 * d * r
    * v * x ^ 2 + 6 * a ^ 2 * r ^ 4 * x ^ 2 - 4 * a ^ 2 * r ^ 4 + 2 * d ^ 2 * r ^ 2 + 2 * d * r ^ 4
    - d * r ^ 3 * v - 2 * r ^ 6)
/-- `C_{xp,tx} J_{tx,tx}`, reduced to the common denominator. -/
theorem M_xp_tx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (C_xp_tx * J_tx_tx) (⟨M_xp_tx_n1, M_xp_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_xp_tx, J_tx_tx, M_xp_tx_n1, M_xp_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `C_{xp,xp} J_{xp,tx}` over the common denominator. -/
def M_xp_tx_n2 : ZExp 6 := -a * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) * (-6 * a ^ 8 * x ^ 2 + 2 *
    a ^ 6 * d * x ^ 4 + 4 * a ^ 6 * d * x ^ 2 - 18 * a ^ 6 * r ^ 2 * x ^ 2 + 2 * a ^ 6 * r ^ 2 - 2
    * a ^ 4 * d ^ 2 * x ^ 4 + 2 * a ^ 4 * d ^ 2 * x ^ 2 + 4 * a ^ 4 * d * r ^ 2 * x ^ 4 + 6 * a ^ 4
    * d * r ^ 2 * x ^ 2 - a ^ 4 * d * r * v * x ^ 4 + a ^ 4 * d * r * v * x ^ 2 - 18 * a ^ 4 * r ^
    4 * x ^ 2 + 6 * a ^ 4 * r ^ 4 + 2 * a ^ 2 * d ^ 2 * r ^ 2 * x ^ 2 - 2 * a ^ 2 * d ^ 2 * r ^ 2 +
    6 * a ^ 2 * d * r ^ 4 * x ^ 2 - 4 * a ^ 2 * d * r ^ 4 - a ^ 2 * d * r ^ 3 * v * x ^ 2 + a ^ 2 *
    d * r ^ 3 * v - 6 * a ^ 2 * r ^ 6 * x ^ 2 + 6 * a ^ 2 * r ^ 6 - 2 * d * r ^ 6 + 2 * r ^ 8)
/-- `C_{xp,xp} J_{xp,tx}`, reduced to the common denominator. -/
theorem M_xp_tx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (C_xp_xp * J_xp_tx) (⟨M_xp_tx_n2, M_xp_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_xp_xp, J_xp_tx, M_xp_tx_n2, M_xp_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `M_{xp,tx} = Σ_J C_{xp,J} J_{J,tx}`: the reduced fraction. -/
theorem product_xp_tx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨M_xp_tx_n1 + M_xp_tx_n2, M_xp_tx_cd⟩) (M_xp_tx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [M_xp_tx_n1, M_xp_tx_n2, M_xp_tx_cd, M_xp_tx, δr_0, δr_1, δr_2, δr_3, δr_4,
        δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `M_{xp,rp}` -/

/-- `M_{xp,rp}`, reduced. -/
def M_xp_rp : Frac 6 := ⟨a ^ 2 * x * (2 * a ^ 2 + d + 2 * r ^ 2) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^
    2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v), 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4⟩

/-- The common denominator of the terms of `M_{xp,rp}`. -/
def M_xp_rp_cd : ZExp 6 := 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `C_{xp,tr} J_{tr,rp}` over the common denominator. -/
def M_xp_rp_n1 : ZExp 6 := -a ^ 2 * x * (a ^ 2 - d + r ^ 2) * (a ^ 2 * x ^ 2 - 3 * a ^ 2 - 2 * r ^
    2) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2
    * v)
/-- `C_{xp,tr} J_{tr,rp}`, reduced to the common denominator. -/
theorem M_xp_rp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (C_xp_tr * J_tr_rp) (⟨M_xp_rp_n1, M_xp_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_xp_tr, J_tr_rp, M_xp_rp_n1, M_xp_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `C_{xp,rp} J_{rp,rp}` over the common denominator. -/
def M_xp_rp_n2 : ZExp 6 := 3 * a ^ 2 * x * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 - a ^ 2 + d) * (2 * a ^
    2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v)
/-- `C_{xp,rp} J_{rp,rp}`, reduced to the common denominator. -/
theorem M_xp_rp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (C_xp_rp * J_rp_rp) (⟨M_xp_rp_n2, M_xp_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_xp_rp, J_rp_rp, M_xp_rp_n2, M_xp_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `M_{xp,rp} = Σ_J C_{xp,J} J_{J,rp}`: the reduced fraction. -/
theorem product_xp_rp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨M_xp_rp_n1 + M_xp_rp_n2, M_xp_rp_cd⟩) (M_xp_rp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [M_xp_rp_n1, M_xp_rp_n2, M_xp_rp_cd, M_xp_rp, δr_0, δr_1, δr_2, δr_3, δr_4,
        δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `M_{xp,xp}` -/

/-- `M_{xp,xp}`, reduced. -/
def M_xp_xp : Frac 6 := ⟨2 * a ^ 6 * x ^ 4 - 8 * a ^ 6 * x ^ 2 - 2 * a ^ 4 * d * x ^ 4 + 8 * a ^ 4
    * d * x ^ 2 + 4 * a ^ 4 * r ^ 2 * x ^ 4 - 18 * a ^ 4 * r ^ 2 * x ^ 2 + 4 * a ^ 4 * r ^ 2 - a ^
    4 * r * v * x ^ 4 + a ^ 4 * r * v * x ^ 2 + 8 * a ^ 2 * d * r ^ 2 * x ^ 2 - 4 * a ^ 2 * d * r ^
    2 - 6 * a ^ 2 * r ^ 4 * x ^ 2 + 4 * a ^ 2 * r ^ 4 - a ^ 2 * r ^ 3 * v * x ^ 2 + a ^ 2 * r ^ 3 *
    v - 2 * d * r ^ 4 + 2 * r ^ 6, 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4⟩

/-- The common denominator of the terms of `M_{xp,xp}`. -/
def M_xp_xp_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `C_{xp,tx} J_{tx,xp}` over the common denominator. -/
def M_xp_xp_n1 : ZExp 6 := a ^ 2 * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) * (6 * a ^ 6 * x ^ 2 - 4
    * a ^ 4 * d * x ^ 2 + 12 * a ^ 4 * r ^ 2 * x ^ 2 - 2 * a ^ 4 * r ^ 2 - 2 * a ^ 2 * d ^ 2 * x ^
    2 - 2 * a ^ 2 * d * r ^ 2 * x ^ 2 - a ^ 2 * d * r * v * x ^ 2 + 6 * a ^ 2 * r ^ 4 * x ^ 2 - 4 *
    a ^ 2 * r ^ 4 + 2 * d ^ 2 * r ^ 2 + 2 * d * r ^ 4 - d * r ^ 3 * v - 2 * r ^ 6)
/-- `C_{xp,tx} J_{tx,xp}`, reduced to the common denominator. -/
theorem M_xp_xp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (C_xp_tx * J_tx_xp) (⟨M_xp_xp_n1, M_xp_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_xp_tx, J_tx_xp, M_xp_xp_n1, M_xp_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `C_{xp,xp} J_{xp,xp}` over the common denominator. -/
def M_xp_xp_n2 : ZExp 6 := (a ^ 2 * x ^ 2 - a ^ 2 + d) * (-6 * a ^ 8 * x ^ 2 + 2 * a ^ 6 * d * x ^
    4 + 4 * a ^ 6 * d * x ^ 2 - 18 * a ^ 6 * r ^ 2 * x ^ 2 + 2 * a ^ 6 * r ^ 2 - 2 * a ^ 4 * d ^ 2
    * x ^ 4 + 2 * a ^ 4 * d ^ 2 * x ^ 2 + 4 * a ^ 4 * d * r ^ 2 * x ^ 4 + 6 * a ^ 4 * d * r ^ 2 * x
    ^ 2 - a ^ 4 * d * r * v * x ^ 4 + a ^ 4 * d * r * v * x ^ 2 - 18 * a ^ 4 * r ^ 4 * x ^ 2 + 6 *
    a ^ 4 * r ^ 4 + 2 * a ^ 2 * d ^ 2 * r ^ 2 * x ^ 2 - 2 * a ^ 2 * d ^ 2 * r ^ 2 + 6 * a ^ 2 * d *
    r ^ 4 * x ^ 2 - 4 * a ^ 2 * d * r ^ 4 - a ^ 2 * d * r ^ 3 * v * x ^ 2 + a ^ 2 * d * r ^ 3 * v -
    6 * a ^ 2 * r ^ 6 * x ^ 2 + 6 * a ^ 2 * r ^ 6 - 2 * d * r ^ 6 + 2 * r ^ 8)
/-- `C_{xp,xp} J_{xp,xp}`, reduced to the common denominator. -/
theorem M_xp_xp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (C_xp_xp * J_xp_xp) (⟨M_xp_xp_n2, M_xp_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_xp_xp, J_xp_xp, M_xp_xp_n2, M_xp_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `M_{xp,xp} = Σ_J C_{xp,J} J_{J,xp}`: the reduced fraction. -/
theorem product_xp_xp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨M_xp_xp_n1 + M_xp_xp_n2, M_xp_xp_cd⟩) (M_xp_xp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [M_xp_xp_n1, M_xp_xp_n2, M_xp_xp_cd, M_xp_xp, δr_0, δr_1, δr_2, δr_3, δr_4,
        δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

end LeanProofs.IPRA.Geometry.KerrNewmanPairProductB
