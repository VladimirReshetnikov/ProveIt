import IPRADerivations.Geometry.KerrNewmanPairMatrix

/-!
# The product `M = C J` of the pair matrices, part A (`four_metrics_ipra`)

Packet: `geometry/four_metrics_ipra_2026-11-15`, `eq:paircontract` (`𝒦 = 4 tr(C J C J)`): with the
    pair
matrix `C` and the pair inverse `J` of `Geometry/KerrNewmanPairMatrix`, `product_IK` with `M_I_K_tn`
certifies each entry `M_{IK} = Σ_J C_{IJ} J_{JK}` (terms reduced over a common denominator, the sum
equal to the reduced fraction `M_I_K` or `0`). The entries are split between
`Geometry/KerrNewmanPairProductA` and `…B` (this is part A);
the trace is `Geometry/KerrNewmanKretschmann`.

The reduced fractions and numerators were proposed by a computer algebra script; every identity
is checked by Lean as an identity of fractions cleared of denominators, a closed sentence of iPRA
certified in every commutative ring.
-/

namespace LeanProofs.IPRA.Geometry.KerrNewmanPairProductA

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

/-! ### `M_{tr,tr}` -/

/-- `M_{tr,tr}`, reduced. -/
def M_tr_tr : Frac 6 := ⟨-a ^ 6 * w * x ^ 4 + 4 * a ^ 6 * x ^ 4 - 4 * a ^ 6 * x ^ 2 - 2 * a ^ 4 * d
    * x ^ 4 + 4 * a ^ 4 * d * x ^ 2 - a ^ 4 * r ^ 2 * w * x ^ 4 - 2 * a ^ 4 * r ^ 2 * w * x ^ 2 + 6
    * a ^ 4 * r ^ 2 * x ^ 4 - 14 * a ^ 4 * r ^ 2 * x ^ 2 + 8 * a ^ 4 * r ^ 2 - a ^ 4 * r * v * x ^
    4 + 5 * a ^ 4 * r * v * x ^ 2 + 4 * a ^ 2 * d * r ^ 2 * x ^ 2 - 8 * a ^ 2 * d * r ^ 2 - 2 * a ^
    2 * r ^ 4 * w * x ^ 2 - a ^ 2 * r ^ 4 * w - 6 * a ^ 2 * r ^ 4 * x ^ 2 + 6 * a ^ 2 * r ^ 4 + 3 *
    a ^ 2 * r ^ 3 * v * x ^ 2 + 5 * a ^ 2 * r ^ 3 * v - 6 * d * r ^ 4 - r ^ 6 * w + 4 * r ^ 5 * v,
    2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4⟩

/-- The common denominator of the terms of `M_{tr,tr}`. -/
def M_tr_tr_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `C_{tr,tr} J_{tr,tr}` over the common denominator. -/
def M_tr_tr_n1 : ZExp 6 := (a ^ 4 + a ^ 2 * d * x ^ 2 - a ^ 2 * d + 2 * a ^ 2 * r ^ 2 + r ^ 4) * (2
    * a ^ 6 * x ^ 4 - 2 * a ^ 6 * x ^ 2 - a ^ 4 * d * w * x ^ 4 + 4 * a ^ 4 * r ^ 2 * x ^ 4 - 6 * a
    ^ 4 * r ^ 2 * x ^ 2 + 2 * a ^ 4 * r ^ 2 - a ^ 4 * r * v * x ^ 4 + a ^ 4 * r * v * x ^ 2 + 2 * a
    ^ 2 * d ^ 2 * x ^ 2 - 2 * a ^ 2 * d * r ^ 2 * w * x ^ 2 - 4 * a ^ 2 * d * r ^ 2 * x ^ 2 + 4 * a
    ^ 2 * d * r ^ 2 + 4 * a ^ 2 * d * r * v * x ^ 2 - a ^ 2 * r ^ 3 * v * x ^ 2 + a ^ 2 * r ^ 3 * v
    - 6 * d ^ 2 * r ^ 2 - d * r ^ 4 * w + 4 * d * r ^ 3 * v)
/-- `C_{tr,tr} J_{tr,tr}`, reduced to the common denominator. -/
theorem M_tr_tr_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (C_tr_tr * J_tr_tr) (⟨M_tr_tr_n1, M_tr_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_tr_tr, J_tr_tr, M_tr_tr_n1, M_tr_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `C_{tr,rp} J_{rp,tr}` over the common denominator. -/
def M_tr_tr_n2 : ZExp 6 := -a ^ 2 * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) * (2 * a ^ 6 * x ^ 2 +
    a ^ 4 * d * w * x ^ 4 - 2 * a ^ 4 * d * x ^ 4 + 6 * a ^ 4 * r ^ 2 * x ^ 2 - 2 * a ^ 4 * r ^ 2 -
    a ^ 4 * r * v * x ^ 2 - 2 * a ^ 2 * d ^ 2 * x ^ 2 + 2 * a ^ 2 * d * r ^ 2 * w * x ^ 2 + 4 * a ^
    2 * d * r ^ 2 * x ^ 2 - 4 * a ^ 2 * d * r ^ 2 - 4 * a ^ 2 * d * r * v * x ^ 2 + 4 * a ^ 2 * r ^
    4 * x ^ 2 - 2 * a ^ 2 * r ^ 4 - a ^ 2 * r ^ 3 * v * x ^ 2 - a ^ 2 * r ^ 3 * v + 6 * d ^ 2 * r ^
    2 + d * r ^ 4 * w + 2 * d * r ^ 4 - 4 * d * r ^ 3 * v - r ^ 5 * v)
/-- `C_{tr,rp} J_{rp,tr}`, reduced to the common denominator. -/
theorem M_tr_tr_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (C_tr_rp * J_rp_tr) (⟨M_tr_tr_n2, M_tr_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_tr_rp, J_rp_tr, M_tr_tr_n2, M_tr_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `M_{tr,tr} = Σ_J C_{tr,J} J_{J,tr}`: the reduced fraction. -/
theorem product_tr_tr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨M_tr_tr_n1 + M_tr_tr_n2, M_tr_tr_cd⟩) (M_tr_tr))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [M_tr_tr_n1, M_tr_tr_n2, M_tr_tr_cd, M_tr_tr, δr_0, δr_1, δr_2, δr_3, δr_4,
        δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `M_{tr,tx}` -/

/-- `M_{tr,tx}`, reduced. -/
def M_tr_tx : Frac 6 := ⟨a ^ 2 * x * (x - 1) * (x + 1) * (a ^ 2 + 2 * d + r ^ 2) * (2 * a ^ 2 * r *
    x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v), 2 * d * (a ^ 2
    * x ^ 2 + r ^ 2) ^ 4⟩

/-- The common denominator of the terms of `M_{tr,tx}`. -/
def M_tr_tx_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `C_{tr,tx} J_{tx,tx}` over the common denominator. -/
def M_tr_tx_n1 : ZExp 6 := 3 * a ^ 2 * x * (x - 1) * (x + 1) * (a ^ 4 + a ^ 2 * d * x ^ 2 - a ^ 2 *
    d + 2 * a ^ 2 * r ^ 2 + r ^ 4) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4
    * d * r - 2 * r ^ 3 - r ^ 2 * v)
/-- `C_{tr,tx} J_{tx,tx}`, reduced to the common denominator. -/
theorem M_tr_tx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (C_tr_tx * J_tx_tx) (⟨M_tr_tx_n1, M_tr_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_tr_tx, J_tx_tx, M_tr_tx_n1, M_tr_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `C_{tr,xp} J_{xp,tx}` over the common denominator. -/
def M_tr_tx_n2 : ZExp 6 := a ^ 2 * x * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) * (a ^ 2 * x ^ 2 - 3
    * a ^ 2 - 2 * r ^ 2) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r -
    2 * r ^ 3 - r ^ 2 * v)
/-- `C_{tr,xp} J_{xp,tx}`, reduced to the common denominator. -/
theorem M_tr_tx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (C_tr_xp * J_xp_tx) (⟨M_tr_tx_n2, M_tr_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_tr_xp, J_xp_tx, M_tr_tx_n2, M_tr_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `M_{tr,tx} = Σ_J C_{tr,J} J_{J,tx}`: the reduced fraction. -/
theorem product_tr_tx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨M_tr_tx_n1 + M_tr_tx_n2, M_tr_tx_cd⟩) (M_tr_tx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [M_tr_tx_n1, M_tr_tx_n2, M_tr_tx_cd, M_tr_tx, δr_0, δr_1, δr_2, δr_3, δr_4,
        δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `M_{tr,rp}` -/

/-- `M_{tr,rp}`, reduced. -/
def M_tr_rp : Frac 6 := ⟨a * (a ^ 4 * w * x ^ 4 - 2 * a ^ 4 * x ^ 4 + 4 * a ^ 4 * x ^ 2 - 4 * a ^ 2
    * d * x ^ 2 + 2 * a ^ 2 * r ^ 2 * w * x ^ 2 + 10 * a ^ 2 * r ^ 2 * x ^ 2 - 8 * a ^ 2 * r ^ 2 -
    5 * a ^ 2 * r * v * x ^ 2 + 8 * d * r ^ 2 + r ^ 4 * w - 5 * r ^ 3 * v), 2 * (a ^ 2 * x ^ 2 + r
    ^ 2) ^ 4⟩

/-- The common denominator of the terms of `M_{tr,rp}`. -/
def M_tr_rp_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `C_{tr,tr} J_{tr,rp}` over the common denominator. -/
def M_tr_rp_n1 : ZExp 6 := -a * (a ^ 2 - d + r ^ 2) * (2 * a ^ 6 * x ^ 4 - 2 * a ^ 6 * x ^ 2 - a ^
    4 * d * w * x ^ 4 + 4 * a ^ 4 * r ^ 2 * x ^ 4 - 6 * a ^ 4 * r ^ 2 * x ^ 2 + 2 * a ^ 4 * r ^ 2 -
    a ^ 4 * r * v * x ^ 4 + a ^ 4 * r * v * x ^ 2 + 2 * a ^ 2 * d ^ 2 * x ^ 2 - 2 * a ^ 2 * d * r ^
    2 * w * x ^ 2 - 4 * a ^ 2 * d * r ^ 2 * x ^ 2 + 4 * a ^ 2 * d * r ^ 2 + 4 * a ^ 2 * d * r * v *
    x ^ 2 - a ^ 2 * r ^ 3 * v * x ^ 2 + a ^ 2 * r ^ 3 * v - 6 * d ^ 2 * r ^ 2 - d * r ^ 4 * w + 4 *
    d * r ^ 3 * v)
/-- `C_{tr,tr} J_{tr,rp}`, reduced to the common denominator. -/
theorem M_tr_rp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (C_tr_tr * J_tr_rp) (⟨M_tr_rp_n1, M_tr_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_tr_tr, J_tr_rp, M_tr_rp_n1, M_tr_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `C_{tr,rp} J_{rp,rp}` over the common denominator. -/
def M_tr_rp_n2 : ZExp 6 := a * (a ^ 2 * x ^ 2 - a ^ 2 + d) * (2 * a ^ 6 * x ^ 2 + a ^ 4 * d * w * x
    ^ 4 - 2 * a ^ 4 * d * x ^ 4 + 6 * a ^ 4 * r ^ 2 * x ^ 2 - 2 * a ^ 4 * r ^ 2 - a ^ 4 * r * v * x
    ^ 2 - 2 * a ^ 2 * d ^ 2 * x ^ 2 + 2 * a ^ 2 * d * r ^ 2 * w * x ^ 2 + 4 * a ^ 2 * d * r ^ 2 * x
    ^ 2 - 4 * a ^ 2 * d * r ^ 2 - 4 * a ^ 2 * d * r * v * x ^ 2 + 4 * a ^ 2 * r ^ 4 * x ^ 2 - 2 * a
    ^ 2 * r ^ 4 - a ^ 2 * r ^ 3 * v * x ^ 2 - a ^ 2 * r ^ 3 * v + 6 * d ^ 2 * r ^ 2 + d * r ^ 4 * w
    + 2 * d * r ^ 4 - 4 * d * r ^ 3 * v - r ^ 5 * v)
/-- `C_{tr,rp} J_{rp,rp}`, reduced to the common denominator. -/
theorem M_tr_rp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (C_tr_rp * J_rp_rp) (⟨M_tr_rp_n2, M_tr_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_tr_rp, J_rp_rp, M_tr_rp_n2, M_tr_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `M_{tr,rp} = Σ_J C_{tr,J} J_{J,rp}`: the reduced fraction. -/
theorem product_tr_rp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨M_tr_rp_n1 + M_tr_rp_n2, M_tr_rp_cd⟩) (M_tr_rp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [M_tr_rp_n1, M_tr_rp_n2, M_tr_rp_cd, M_tr_rp, δr_0, δr_1, δr_2, δr_3, δr_4,
        δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `M_{tr,xp}` -/

/-- `M_{tr,xp}`, reduced. -/
def M_tr_xp : Frac 6 := ⟨-a * x * (a ^ 2 * x ^ 2 - a ^ 2 - 2 * d) * (2 * a ^ 2 * r * x ^ 2 - 4 * a
    ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v), 2 * d * (a ^ 2 * x ^ 2 + r ^
    2) ^ 4⟩

/-- The common denominator of the terms of `M_{tr,xp}`. -/
def M_tr_xp_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `C_{tr,tx} J_{tx,xp}` over the common denominator. -/
def M_tr_xp_n1 : ZExp 6 := -3 * a ^ 3 * x * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) * (2 * a ^ 2 *
    r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v)
/-- `C_{tr,tx} J_{tx,xp}`, reduced to the common denominator. -/
theorem M_tr_xp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (C_tr_tx * J_tx_xp) (⟨M_tr_xp_n1, M_tr_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_tr_tx, J_tx_xp, M_tr_xp_n1, M_tr_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `C_{tr,xp} J_{xp,xp}` over the common denominator. -/
def M_tr_xp_n2 : ZExp 6 := -a * x * (a ^ 2 * x ^ 2 - 3 * a ^ 2 - 2 * r ^ 2) * (a ^ 2 * x ^ 2 - a ^
    2 + d) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r
    ^ 2 * v)
/-- `C_{tr,xp} J_{xp,xp}`, reduced to the common denominator. -/
theorem M_tr_xp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (C_tr_xp * J_xp_xp) (⟨M_tr_xp_n2, M_tr_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_tr_xp, J_xp_xp, M_tr_xp_n2, M_tr_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `M_{tr,xp} = Σ_J C_{tr,J} J_{J,xp}`: the reduced fraction. -/
theorem product_tr_xp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨M_tr_xp_n1 + M_tr_xp_n2, M_tr_xp_cd⟩) (M_tr_xp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [M_tr_xp_n1, M_tr_xp_n2, M_tr_xp_cd, M_tr_xp, δr_0, δr_1, δr_2, δr_3, δr_4,
        δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `M_{tx,tr}` -/

/-- `M_{tx,tr}`, reduced. -/
def M_tx_tr : Frac 6 := ⟨-a ^ 2 * x * (2 * a ^ 2 + d + 2 * r ^ 2) * (2 * a ^ 2 * r * x ^ 2 - 4 * a
    ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v), 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^
    4⟩

/-- The common denominator of the terms of `M_{tx,tr}`. -/
def M_tx_tr_cd : ZExp 6 := 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `C_{tx,tr} J_{tr,tr}` over the common denominator. -/
def M_tx_tr_n1 : ZExp 6 := -3 * a ^ 2 * x * (a ^ 4 + a ^ 2 * d * x ^ 2 - a ^ 2 * d + 2 * a ^ 2 * r
    ^ 2 + r ^ 4) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^
    3 - r ^ 2 * v)
/-- `C_{tx,tr} J_{tr,tr}`, reduced to the common denominator. -/
theorem M_tx_tr_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (C_tx_tr * J_tr_tr) (⟨M_tx_tr_n1, M_tx_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_tx_tr, J_tr_tr, M_tx_tr_n1, M_tx_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `C_{tx,rp} J_{rp,tr}` over the common denominator. -/
def M_tx_tr_n2 : ZExp 6 := -a ^ 2 * x * (a ^ 2 - d + r ^ 2) * (2 * a ^ 2 * x ^ 2 - 3 * a ^ 2 - r ^
    2) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2
    * v)
/-- `C_{tx,rp} J_{rp,tr}`, reduced to the common denominator. -/
theorem M_tx_tr_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (C_tx_rp * J_rp_tr) (⟨M_tx_tr_n2, M_tx_tr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_tx_rp, J_rp_tr, M_tx_tr_n2, M_tx_tr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `M_{tx,tr} = Σ_J C_{tx,J} J_{J,tr}`: the reduced fraction. -/
theorem product_tx_tr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨M_tx_tr_n1 + M_tx_tr_n2, M_tx_tr_cd⟩) (M_tx_tr))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [M_tx_tr_n1, M_tx_tr_n2, M_tx_tr_cd, M_tx_tr, δr_0, δr_1, δr_2, δr_3, δr_4,
        δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `M_{tx,tx}` -/

/-- `M_{tx,tx}`, reduced. -/
def M_tx_tx : Frac 6 := ⟨-6 * a ^ 6 * x ^ 4 + 8 * a ^ 6 * x ^ 2 + 6 * a ^ 4 * d * x ^ 4 - 8 * a ^ 4
    * d * x ^ 2 - 6 * a ^ 4 * r ^ 2 * x ^ 4 + 14 * a ^ 4 * r ^ 2 * x ^ 2 - 4 * a ^ 4 * r ^ 2 - a ^
    4 * r * v * x ^ 2 - 4 * a ^ 2 * d * r ^ 2 * x ^ 2 + 4 * a ^ 2 * d * r ^ 2 + 6 * a ^ 2 * r ^ 4 *
    x ^ 2 - 4 * a ^ 2 * r ^ 4 - a ^ 2 * r ^ 3 * v * x ^ 2 - a ^ 2 * r ^ 3 * v + 2 * d * r ^ 4 - r ^
    5 * v, 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4⟩

/-- The common denominator of the terms of `M_{tx,tx}`. -/
def M_tx_tx_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `C_{tx,tx} J_{tx,tx}` over the common denominator. -/
def M_tx_tx_n1 : ZExp 6 := -(a ^ 4 + a ^ 2 * d * x ^ 2 - a ^ 2 * d + 2 * a ^ 2 * r ^ 2 + r ^ 4) *
    (6 * a ^ 6 * x ^ 4 - 6 * a ^ 6 * x ^ 2 - 6 * a ^ 4 * d * x ^ 4 + 4 * a ^ 4 * d * x ^ 2 + 6 * a
    ^ 4 * r ^ 2 * x ^ 4 - 8 * a ^ 4 * r ^ 2 * x ^ 2 + 2 * a ^ 4 * r ^ 2 + 2 * a ^ 2 * d ^ 2 * x ^ 2
    - 2 * a ^ 2 * d * r ^ 2 * x ^ 2 + a ^ 2 * d * r * v * x ^ 2 - 2 * a ^ 2 * r ^ 4 * x ^ 2 + 2 * a
    ^ 2 * r ^ 4 - 2 * d ^ 2 * r ^ 2 + d * r ^ 3 * v)
/-- `C_{tx,tx} J_{tx,tx}`, reduced to the common denominator. -/
theorem M_tx_tx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (C_tx_tx * J_tx_tx) (⟨M_tx_tx_n1, M_tx_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_tx_tx, J_tx_tx, M_tx_tx_n1, M_tx_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `C_{tx,xp} J_{xp,tx}` over the common denominator. -/
def M_tx_tx_n2 : ZExp 6 := a ^ 2 * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) * (6 * a ^ 6 * x ^ 2 - 4
    * a ^ 4 * d * x ^ 2 + 12 * a ^ 4 * r ^ 2 * x ^ 2 - 2 * a ^ 4 * r ^ 2 - 2 * a ^ 2 * d ^ 2 * x ^
    2 - 2 * a ^ 2 * d * r ^ 2 * x ^ 2 - a ^ 2 * d * r * v * x ^ 2 + 6 * a ^ 2 * r ^ 4 * x ^ 2 - 4 *
    a ^ 2 * r ^ 4 + 2 * d ^ 2 * r ^ 2 + 2 * d * r ^ 4 - d * r ^ 3 * v - 2 * r ^ 6)
/-- `C_{tx,xp} J_{xp,tx}`, reduced to the common denominator. -/
theorem M_tx_tx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (C_tx_xp * J_xp_tx) (⟨M_tx_tx_n2, M_tx_tx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_tx_xp, J_xp_tx, M_tx_tx_n2, M_tx_tx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `M_{tx,tx} = Σ_J C_{tx,J} J_{J,tx}`: the reduced fraction. -/
theorem product_tx_tx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨M_tx_tx_n1 + M_tx_tx_n2, M_tx_tx_cd⟩) (M_tx_tx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [M_tx_tx_n1, M_tx_tx_n2, M_tx_tx_cd, M_tx_tx, δr_0, δr_1, δr_2, δr_3, δr_4,
        δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `M_{tx,rp}` -/

/-- `M_{tx,rp}`, reduced. -/
def M_tx_rp : Frac 6 := ⟨a * x * (2 * a ^ 2 * x ^ 2 - 2 * a ^ 2 - d) * (2 * a ^ 2 * r * x ^ 2 - 4 *
    a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v), 2 * (x - 1) * (x + 1) * (a
    ^ 2 * x ^ 2 + r ^ 2) ^ 4⟩

/-- The common denominator of the terms of `M_{tx,rp}`. -/
def M_tx_rp_cd : ZExp 6 := 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `C_{tx,tr} J_{tr,rp}` over the common denominator. -/
def M_tx_rp_n1 : ZExp 6 := 3 * a ^ 3 * x * (x - 1) * (x + 1) * (a ^ 2 - d + r ^ 2) * (2 * a ^ 2 * r
    * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v)
/-- `C_{tx,tr} J_{tr,rp}`, reduced to the common denominator. -/
theorem M_tx_rp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (C_tx_tr * J_tr_rp) (⟨M_tx_rp_n1, M_tx_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_tx_tr, J_tr_rp, M_tx_rp_n1, M_tx_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `C_{tx,rp} J_{rp,rp}` over the common denominator. -/
def M_tx_rp_n2 : ZExp 6 := a * x * (a ^ 2 * x ^ 2 - a ^ 2 + d) * (2 * a ^ 2 * x ^ 2 - 3 * a ^ 2 - r
    ^ 2) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^
    2 * v)
/-- `C_{tx,rp} J_{rp,rp}`, reduced to the common denominator. -/
theorem M_tx_rp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (C_tx_rp * J_rp_rp) (⟨M_tx_rp_n2, M_tx_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_tx_rp, J_rp_rp, M_tx_rp_n2, M_tx_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `M_{tx,rp} = Σ_J C_{tx,J} J_{J,rp}`: the reduced fraction. -/
theorem product_tx_rp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨M_tx_rp_n1 + M_tx_rp_n2, M_tx_rp_cd⟩) (M_tx_rp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [M_tx_rp_n1, M_tx_rp_n2, M_tx_rp_cd, M_tx_rp, δr_0, δr_1, δr_2, δr_3, δr_4,
        δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `M_{tx,xp}` -/

/-- `M_{tx,xp}`, reduced. -/
def M_tx_xp : Frac 6 := ⟨-a * (8 * a ^ 4 * x ^ 2 - 8 * a ^ 2 * d * x ^ 2 + 10 * a ^ 2 * r ^ 2 * x ^
    2 - 4 * a ^ 2 * r ^ 2 - a ^ 2 * r * v * x ^ 2 + 4 * d * r ^ 2 - 2 * r ^ 4 - r ^ 3 * v), 2 * (a
    ^ 2 * x ^ 2 + r ^ 2) ^ 4⟩

/-- The common denominator of the terms of `M_{tx,xp}`. -/
def M_tx_xp_cd : ZExp 6 := 2 * d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `C_{tx,tx} J_{tx,xp}` over the common denominator. -/
def M_tx_xp_n1 : ZExp 6 := a * (a ^ 2 - d + r ^ 2) * (6 * a ^ 6 * x ^ 4 - 6 * a ^ 6 * x ^ 2 - 6 * a
    ^ 4 * d * x ^ 4 + 4 * a ^ 4 * d * x ^ 2 + 6 * a ^ 4 * r ^ 2 * x ^ 4 - 8 * a ^ 4 * r ^ 2 * x ^ 2
    + 2 * a ^ 4 * r ^ 2 + 2 * a ^ 2 * d ^ 2 * x ^ 2 - 2 * a ^ 2 * d * r ^ 2 * x ^ 2 + a ^ 2 * d * r
    * v * x ^ 2 - 2 * a ^ 2 * r ^ 4 * x ^ 2 + 2 * a ^ 2 * r ^ 4 - 2 * d ^ 2 * r ^ 2 + d * r ^ 3 * v)
/-- `C_{tx,tx} J_{tx,xp}`, reduced to the common denominator. -/
theorem M_tx_xp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (C_tx_tx * J_tx_xp) (⟨M_tx_xp_n1, M_tx_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_tx_tx, J_tx_xp, M_tx_xp_n1, M_tx_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- The numerator of `C_{tx,xp} J_{xp,xp}` over the common denominator. -/
def M_tx_xp_n2 : ZExp 6 := -a * (a ^ 2 * x ^ 2 - a ^ 2 + d) * (6 * a ^ 6 * x ^ 2 - 4 * a ^ 4 * d *
    x ^ 2 + 12 * a ^ 4 * r ^ 2 * x ^ 2 - 2 * a ^ 4 * r ^ 2 - 2 * a ^ 2 * d ^ 2 * x ^ 2 - 2 * a ^ 2
    * d * r ^ 2 * x ^ 2 - a ^ 2 * d * r * v * x ^ 2 + 6 * a ^ 2 * r ^ 4 * x ^ 2 - 4 * a ^ 2 * r ^ 4
    + 2 * d ^ 2 * r ^ 2 + 2 * d * r ^ 4 - d * r ^ 3 * v - 2 * r ^ 6)
/-- `C_{tx,xp} J_{xp,xp}`, reduced to the common denominator. -/
theorem M_tx_xp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (C_tx_xp * J_xp_xp) (⟨M_tx_xp_n2, M_tx_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_tx_xp, J_xp_xp, M_tx_xp_n2, M_tx_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `M_{tx,xp} = Σ_J C_{tx,J} J_{J,xp}`: the reduced fraction. -/
theorem product_tx_xp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨M_tx_xp_n1 + M_tx_xp_n2, M_tx_xp_cd⟩) (M_tx_xp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [M_tx_xp_n1, M_tx_xp_n2, M_tx_xp_cd, M_tx_xp, δr_0, δr_1, δr_2, δr_3, δr_4,
        δr_5, δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-! ### `M_{tp,tp}` -/

/-- `M_{tp,tp}`, reduced. -/
def M_tp_tp : Frac 6 := ⟨2 * a ^ 4 * x ^ 2 - 2 * a ^ 2 * d * x ^ 2 + 4 * a ^ 2 * r ^ 2 * x ^ 2 - 2
    * a ^ 2 * r ^ 2 - a ^ 2 * r * v * x ^ 2 + 2 * d * r ^ 2 - r ^ 3 * v, 2 * (a ^ 2 * x ^ 2 + r ^
    2) ^ 3⟩

/-- The common denominator of the terms of `M_{tp,tp}`. -/
def M_tp_tp_cd : ZExp 6 := 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3

/-- The numerator of `C_{tp,tp} J_{tp,tp}` over the common denominator. -/
def M_tp_tp_n1 : ZExp 6 := 2 * a ^ 4 * x ^ 2 - 2 * a ^ 2 * d * x ^ 2 + 4 * a ^ 2 * r ^ 2 * x ^ 2 -
    2 * a ^ 2 * r ^ 2 - a ^ 2 * r * v * x ^ 2 + 2 * d * r ^ 2 - r ^ 3 * v
/-- `C_{tp,tp} J_{tp,tp}`, reduced to the common denominator. -/
theorem M_tp_tp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (C_tp_tp * J_tp_tp) (⟨M_tp_tp_n1, M_tp_tp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_tp_tp, J_tp_tp, M_tp_tp_n1, M_tp_tp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `M_{tp,tp} = Σ_J C_{tp,J} J_{J,tp}`: the reduced fraction. -/
theorem product_tp_tp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨M_tp_tp_n1, M_tp_tp_cd⟩) (M_tp_tp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [M_tp_tp_n1, M_tp_tp_cd, M_tp_tp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5])

/-! ### `M_{tp,rx}` -/

/-- `M_{tp,rx}`, reduced. -/
def M_tp_rx : Frac 6 := ⟨a * d * x * (x - 1) * (x + 1) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a
    ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v), 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4⟩

/-- The common denominator of the terms of `M_{tp,rx}`. -/
def M_tp_rx_cd : ZExp 6 := 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4

/-- The numerator of `C_{tp,rx} J_{rx,rx}` over the common denominator. -/
def M_tp_rx_n1 : ZExp 6 := a * d * x * (x - 1) * (x + 1) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r -
    a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v)
/-- `C_{tp,rx} J_{rx,rx}`, reduced to the common denominator. -/
theorem M_tp_rx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (C_tp_rx * J_rx_rx) (⟨M_tp_rx_n1, M_tp_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [C_tp_rx, J_rx_rx, M_tp_rx_n1, M_tp_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
        δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]
    ring)

/-- `M_{tp,rx} = Σ_J C_{tp,J} J_{J,rx}`: the reduced fraction. -/
theorem product_tp_rx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (⟨M_tp_rx_n1, M_tp_rx_cd⟩) (M_tp_rx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [M_tp_rx_n1, M_tp_rx_cd, M_tp_rx, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0,
        δx_1, δx_2, δx_3, δx_4, δx_5])

end LeanProofs.IPRA.Geometry.KerrNewmanPairProductA
