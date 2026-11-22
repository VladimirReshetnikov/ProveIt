import IPRADerivations.Geometry.KerrNewmanIngoingConnection

/-!
# The Ricci tensor of the Kerr–Newman metric in the ingoing chart (`four_metrics_ipra`)

Packet: `geometry/four_metrics_ipra_2026-11-15`, `prop:regular` ("Field equations at
`Δ = 0`"), direct proof, second third: the Ricci tensor of the ingoing metric `eq:ingoing`
from the convention `eq:ricci`,

`R_{μν} = Σ_λ ∂_λ Γ^λ_{μν} − ∂_ν Σ_λ Γ^λ_{μλ} + Σ_{λ,ρ} (Γ^λ_{μν} Γ^ρ_{λρ} − Γ^ρ_{μλ} Γ^λ_{νρ})`,

with the connection coefficients of `Geometry/KerrNewmanIngoingConnection` (reduced fractions
`Gλ_μν`, each certified there as the value of `eq:gamma`) and `∂_v = ∂_ψ = 0`, in the
coordinates `(v, r, x, ψ)` (index `p` for `ψ`). For each of the ten entries `R_{μν}`
(`μ ≤ ν`):

* `Rμν_tk`: the `k`-th term whose factors are nonzero coefficients (a derivative `∂_λ Γ` taken
  by `Foundations/FormalDerivation`, or a product `Γ Γ`) equals the numerator `Rμν_nk` over the
  common denominator `Rμν_cd`;
* `ricci_μν`: the signed sum of these numerators over the common denominator is the entry of

  `Ric(g₊) = (q²/Σ²) ((Δ/Σ) p₊² − 2 p₊ dr + (Σ/s) dx² + (s/Σ) b₊²)`,

  that is, with `K = q²/Σ²`: `R_vv = K (Δ + a² s)/Σ`, `R_vr = −K`,
  `R_vψ = −K a s (Δ + P)/Σ`, `R_rψ = K a s`, `R_ψψ = K s (Δ a² s + P²)/Σ`, `R_xx = K Σ/s`, and
  `R_vx = R_rr = R_rx = R_xψ = 0`.

This tensor is the transform of `eq:offshell` at `U = V = q²/Σ²` under `p = p₊ − (Σ/Δ) dr`,
`b = b₊`: the terms in `dr²/Δ` cancel. Here it is computed directly in the ingoing chart, and
no denominator contains `Δ` (every common denominator is a product of `2`, `Σ` and `s`), so
the identities need only `Σ s ≠ 0` and hold at `Δ = 0`.

`Geometry/KerrNewmanIngoingMaxwell` proves that the stress tensor of `eq:EM` has the same
entries (`stress_μν`, with literally the same right-hand sides), which is the Einstein–Maxwell
equation in the ingoing chart.

The numerators were proposed by a computer algebra script; every identity is checked by Lean
as an identity of fractions cleared of denominators, a closed sentence of iPRA certified in
every commutative ring.
-/

namespace LeanProofs.IPRA.Geometry.KerrNewmanIngoingRicci

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Geometry.KerrNewmanIngoingConnection
open ZExp

local notation "r" => (ZExp.var 0 : ZExp 5)
local notation "x" => (ZExp.var 1 : ZExp 5)
local notation "a" => (ZExp.var 2 : ZExp 5)
local notation "m" => (ZExp.var 3 : ZExp 5)
local notation "q" => (ZExp.var 4 : ZExp 5)

/-! ## The entry `R_{vv}` -/

/-- The common denominator of the terms of `R_{vv}`. -/
def Rvv_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 6

/-- The numerator of `∂_r Γ^r_{vv}` over the common denominator. -/
def Rvv_n1 : ZExp 5 := -(a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (-2 * a ^ 4 * m ^ 2 * x ^ 4 + 2 * a ^ 4 * m *
    r * x ^ 4 - 8 * a ^ 4 * m * r * x ^ 2 + a ^ 4 * q ^ 2 * x ^ 2 + 16 * a ^ 2 * m ^ 2 * r ^ 2 * x
    ^ 2 - 12 * a ^ 2 * m * q ^ 2 * r * x ^ 2 - 8 * a ^ 2 * m * r ^ 3 * x ^ 2 + 4 * a ^ 2 * m * r ^
    3 + a ^ 2 * q ^ 4 * x ^ 2 + 3 * a ^ 2 * q ^ 2 * r ^ 2 * x ^ 2 - 5 * a ^ 2 * q ^ 2 * r ^ 2 - 6 *
    m ^ 2 * r ^ 4 + 12 * m * q ^ 2 * r ^ 3 + 2 * m * r ^ 5 - 5 * q ^ 4 * r ^ 2 - 3 * q ^ 2 * r ^ 4)
/-- `∂_r Γ^r_{vv}`, reduced to the common denominator. -/
theorem Rvv_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.d δr Gr_vv) (⟨Rvv_n1, Rvv_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_vv, Rvv_n1, Rvv_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `∂_x Γ^x_{vv}` over the common denominator. -/
def Rvv_n2 : ZExp 5 := -a ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (-2 * m * r + q ^ 2) * (3 * a ^ 2 * x
    ^ 4 - 5 * a ^ 2 * x ^ 2 - 3 * r ^ 2 * x ^ 2 + r ^ 2)
/-- `∂_x Γ^x_{vv}`, reduced to the common denominator. -/
theorem Rvv_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.d δx Gx_vv) (⟨Rvv_n2, Rvv_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_vv, Rvv_n2, Rvv_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `Γ^v_{vv} Γ^v_{vv}` over the common denominator. -/
def Rvv_n3 : ZExp 5 := (a ^ 2 + r ^ 2) ^ 2 * (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^ 2 * r) ^ 2
/-- `Γ^v_{vv} Γ^v_{vv}`, reduced to the common denominator. -/
theorem Rvv_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_vv * Gv_vv) (⟨Rvv_n3, Rvv_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_vv, Rvv_n3, Rvv_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `Γ^v_{vv} Γ^r_{vr}` over the common denominator. -/
def Rvv_n4 : ZExp 5 := -(a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 * m * x ^ 2 - m * r ^ 2
    + q ^ 2 * r) ^ 2
/-- `Γ^v_{vv} Γ^r_{vr}`, reduced to the common denominator. -/
theorem Rvv_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_vv * Gr_vr) (⟨Rvv_n4, Rvv_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_vr, Gv_vv, Rvv_n4, Rvv_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^v_{vv} Γ^p_{vp}` over the common denominator. -/
def Rvv_n5 : ZExp 5 := a ^ 2 * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 * m * x ^ 2 - m * r ^ 2
    + q ^ 2 * r) ^ 2
/-- `Γ^v_{vv} Γ^p_{vp}`, reduced to the common denominator. -/
theorem Rvv_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_vv * Gp_vp) (⟨Rvv_n5, Rvv_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vp, Gv_vv, Rvv_n5, Rvv_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^r_{vv} Γ^x_{rx}` over the common denominator. -/
def Rvv_n6 : ZExp 5 := -r * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^ 2 *
    r) * (a ^ 2 - 2 * m * r + q ^ 2 + r ^ 2)
/-- `Γ^r_{vv} Γ^x_{rx}`, reduced to the common denominator. -/
theorem Rvv_t6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gr_vv * Gx_rx) (⟨Rvv_n6, Rvv_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_vv, Gx_rx, Rvv_n6, Rvv_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^r_{vv} Γ^p_{rp}` over the common denominator. -/
def Rvv_n7 : ZExp 5 := -r * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^ 2 *
    r) * (a ^ 2 - 2 * m * r + q ^ 2 + r ^ 2)
/-- `Γ^r_{vv} Γ^p_{rp}`, reduced to the common denominator. -/
theorem Rvv_t7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gr_vv * Gp_rp) (⟨Rvv_n7, Rvv_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rp, Gr_vv, Rvv_n7, Rvv_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^x_{vv} Γ^v_{xv}` over the common denominator. -/
def Rvv_n8 : ZExp 5 := -a ^ 4 * x ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (-2 * m * r +
    q ^ 2) ^ 2
/-- `Γ^x_{vv} Γ^v_{xv}`, reduced to the common denominator. -/
theorem Rvv_t8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_vv * Gv_vx) (⟨Rvv_n8, Rvv_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_vx, Gx_vv, Rvv_n8, Rvv_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^x_{vv} Γ^r_{xr}` over the common denominator. -/
def Rvv_n9 : ZExp 5 := a ^ 4 * x ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (-2 * m *
    r + q ^ 2)
/-- `Γ^x_{vv} Γ^r_{xr}`, reduced to the common denominator. -/
theorem Rvv_t9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_vv * Gr_rx) (⟨Rvv_n9, Rvv_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Gx_vv, Rvv_n9, Rvv_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^x_{vv} Γ^x_{xx}` over the common denominator. -/
def Rvv_n10 : ZExp 5 := -a ^ 2 * x ^ 2 * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (-2 * m *
    r + q ^ 2)
/-- `Γ^x_{vv} Γ^x_{xx}`, reduced to the common denominator. -/
theorem Rvv_t10 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_vv * Gx_xx) (⟨Rvv_n10, Rvv_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_vv, Gx_xx, Rvv_n10, Rvv_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^x_{vv} Γ^p_{xp}` over the common denominator. -/
def Rvv_n11 : ZExp 5 := a ^ 2 * x ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) * (-2 * m * r + q ^ 2) * (a ^ 4 * x
    ^ 4 - 2 * a ^ 2 * m * r * x ^ 2 + 2 * a ^ 2 * m * r + a ^ 2 * q ^ 2 * x ^ 2 - a ^ 2 * q ^ 2 + 2
    * a ^ 2 * r ^ 2 * x ^ 2 + r ^ 4)
/-- `Γ^x_{vv} Γ^p_{xp}`, reduced to the common denominator. -/
theorem Rvv_t11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_vv * Gp_xp) (⟨Rvv_n11, Rvv_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_xp, Gx_vv, Rvv_n11, Rvv_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{vv} Γ^v_{pv}` over the common denominator. -/
def Rvv_n12 : ZExp 5 := a ^ 2 * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 * m * x ^ 2 - m * r ^
    2 + q ^ 2 * r) ^ 2
/-- `Γ^p_{vv} Γ^v_{pv}`, reduced to the common denominator. -/
theorem Rvv_t12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_vv * Gv_vp) (⟨Rvv_n12, Rvv_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vv, Gv_vp, Rvv_n12, Rvv_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{vv} Γ^r_{pr}` over the common denominator. -/
def Rvv_n13 : ZExp 5 := a ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 * m * x ^ 2 -
    m * r ^ 2 + q ^ 2 * r) * (-a ^ 2 * m * x ^ 2 + a ^ 2 * r * x ^ 2 + m * r ^ 2 - q ^ 2 * r + r ^
    3)
/-- `Γ^p_{vv} Γ^r_{pr}`, reduced to the common denominator. -/
theorem Rvv_t13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_vv * Gr_rp) (⟨Rvv_n13, Rvv_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vv, Gr_rp, Rvv_n13, Rvv_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{vv} Γ^p_{pp}` over the common denominator. -/
def Rvv_n14 : ZExp 5 := -a ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^ 2 * r) *
    (-a ^ 4 * m * x ^ 4 + a ^ 4 * m * x ^ 2 + a ^ 4 * r * x ^ 4 + a ^ 2 * m * r ^ 2 * x ^ 2 - a ^ 2
    * m * r ^ 2 - a ^ 2 * q ^ 2 * r * x ^ 2 + a ^ 2 * q ^ 2 * r + 2 * a ^ 2 * r ^ 3 * x ^ 2 + r ^ 5)
/-- `Γ^p_{vv} Γ^p_{pp}`, reduced to the common denominator. -/
theorem Rvv_t14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_vv * Gp_pp) (⟨Rvv_n14, Rvv_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_pp, Gp_vv, Rvv_n14, Rvv_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^v_{vv} Γ^v_{vv}` over the common denominator. -/
def Rvv_n15 : ZExp 5 := (a ^ 2 + r ^ 2) ^ 2 * (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^ 2 * r) ^ 2
/-- `Γ^v_{vv} Γ^v_{vv}`, reduced to the common denominator. -/
theorem Rvv_t15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_vv * Gv_vv) (⟨Rvv_n15, Rvv_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_vv, Rvv_n15, Rvv_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `Γ^x_{vv} Γ^v_{vx}` over the common denominator. -/
def Rvv_n16 : ZExp 5 := -a ^ 4 * x ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (-2 * m * r
    + q ^ 2) ^ 2
/-- `Γ^x_{vv} Γ^v_{vx}`, reduced to the common denominator. -/
theorem Rvv_t16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_vv * Gv_vx) (⟨Rvv_n16, Rvv_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_vx, Gx_vv, Rvv_n16, Rvv_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{vv} Γ^v_{vp}` over the common denominator. -/
def Rvv_n17 : ZExp 5 := a ^ 2 * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 * m * x ^ 2 - m * r ^
    2 + q ^ 2 * r) ^ 2
/-- `Γ^p_{vv} Γ^v_{vp}`, reduced to the common denominator. -/
theorem Rvv_t17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_vv * Gv_vp) (⟨Rvv_n17, Rvv_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vv, Gv_vp, Rvv_n17, Rvv_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^r_{vr} Γ^r_{vr}` over the common denominator. -/
def Rvv_n18 : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^ 2 * r) ^
    2
/-- `Γ^r_{vr} Γ^r_{vr}`, reduced to the common denominator. -/
theorem Rvv_t18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gr_vr * Gr_vr) (⟨Rvv_n18, Rvv_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_vr, Rvv_n18, Rvv_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `Γ^v_{vx} Γ^x_{vv}` over the common denominator. -/
def Rvv_n19 : ZExp 5 := -a ^ 4 * x ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (-2 * m * r
    + q ^ 2) ^ 2
/-- `Γ^v_{vx} Γ^x_{vv}`, reduced to the common denominator. -/
theorem Rvv_t19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_vx * Gx_vv) (⟨Rvv_n19, Rvv_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_vx, Gx_vv, Rvv_n19, Rvv_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{vx} Γ^x_{vp}` over the common denominator. -/
def Rvv_n20 : ZExp 5 := -a ^ 2 * x ^ 2 * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) * (-2 * m * r +
    q ^ 2) ^ 2
/-- `Γ^p_{vx} Γ^x_{vp}`, reduced to the common denominator. -/
theorem Rvv_t20 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_vx * Gx_vp) (⟨Rvv_n20, Rvv_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vx, Gx_vp, Rvv_n20, Rvv_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^v_{vp} Γ^p_{vv}` over the common denominator. -/
def Rvv_n21 : ZExp 5 := a ^ 2 * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 * m * x ^ 2 - m * r ^
    2 + q ^ 2 * r) ^ 2
/-- `Γ^v_{vp} Γ^p_{vv}`, reduced to the common denominator. -/
theorem Rvv_t21 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_vp * Gp_vv) (⟨Rvv_n21, Rvv_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vv, Gv_vp, Rvv_n21, Rvv_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^x_{vp} Γ^p_{vx}` over the common denominator. -/
def Rvv_n22 : ZExp 5 := -a ^ 2 * x ^ 2 * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) * (-2 * m * r +
    q ^ 2) ^ 2
/-- `Γ^x_{vp} Γ^p_{vx}`, reduced to the common denominator. -/
theorem Rvv_t22 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_vp * Gp_vx) (⟨Rvv_n22, Rvv_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vx, Gx_vp, Rvv_n22, Rvv_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{vp} Γ^p_{vp}` over the common denominator. -/
def Rvv_n23 : ZExp 5 := a ^ 4 * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^ 2
    * r) ^ 2
/-- `Γ^p_{vp} Γ^p_{vp}`, reduced to the common denominator. -/
theorem Rvv_t23 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_vp * Gp_vp) (⟨Rvv_n23, Rvv_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vp, Rvv_n23, Rvv_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- `R_{vv}`: the signed sum of its terms is `Kf * ⟨Dl + a ^ 2 * sx, Sg⟩`. -/
theorem ricci_vv :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Rvv_n1 + Rvv_n2 + Rvv_n3 + Rvv_n4 + Rvv_n5 + Rvv_n6 + Rvv_n7 + Rvv_n8 +
          Rvv_n9 + Rvv_n10 + Rvv_n11 + Rvv_n12 + Rvv_n13 + Rvv_n14 - Rvv_n15 - Rvv_n16 - Rvv_n17 -
          Rvv_n18 - Rvv_n19 - Rvv_n20 - Rvv_n21 - Rvv_n22 - Rvv_n23, Rvv_cd⟩) (Kf * ⟨Dl + a ^ 2 *
          sx, Sg⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Rvv_n1, Rvv_n2, Rvv_n3, Rvv_n4, Rvv_n5, Rvv_n6, Rvv_n7, Rvv_n8, Rvv_n9,
        Rvv_n10, Rvv_n11, Rvv_n12, Rvv_n13, Rvv_n14, Rvv_n15, Rvv_n16, Rvv_n17, Rvv_n18, Rvv_n19,
        Rvv_n20, Rvv_n21, Rvv_n22, Rvv_n23, Rvv_cd, Kf, Sg, sx, Pp, Dl, δr_0, δr_1, δr_2, δr_3,
        δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ## The entry `R_{vr}` -/

/-- The common denominator of the terms of `R_{vr}`. -/
def Rvr_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 4

/-- The numerator of `∂_r Γ^r_{vr}` over the common denominator. -/
def Rvr_n1 : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) * (-6 * a ^ 2 * m * r * x ^ 2 + a ^ 2 * q ^ 2 * x ^
    2 + 2 * m * r ^ 3 - 3 * q ^ 2 * r ^ 2)
/-- `∂_r Γ^r_{vr}`, reduced to the common denominator. -/
theorem Rvr_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.d δr Gr_vr) (⟨Rvr_n1, Rvr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_vr, Rvr_n1, Rvr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `∂_r Γ^v_{vv}` over the common denominator. -/
def Rvr_n2 : ZExp 5 := -2 * a ^ 4 * m * r * x ^ 4 + 8 * a ^ 4 * m * r * x ^ 2 - a ^ 4 * q ^ 2 * x ^
    2 + 8 * a ^ 2 * m * r ^ 3 * x ^ 2 - 4 * a ^ 2 * m * r ^ 3 - 3 * a ^ 2 * q ^ 2 * r ^ 2 * x ^ 2 +
    5 * a ^ 2 * q ^ 2 * r ^ 2 - 2 * m * r ^ 5 + 3 * q ^ 2 * r ^ 4
/-- `∂_r Γ^v_{vv}`, reduced to the common denominator. -/
theorem Rvr_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.d δr Gv_vv) (⟨Rvr_n2, Rvr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_vv, Rvr_n2, Rvr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `∂_r Γ^r_{vr}` over the common denominator. -/
def Rvr_n3 : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) * (-6 * a ^ 2 * m * r * x ^ 2 + a ^ 2 * q ^ 2 * x ^
    2 + 2 * m * r ^ 3 - 3 * q ^ 2 * r ^ 2)
/-- `∂_r Γ^r_{vr}`, reduced to the common denominator. -/
theorem Rvr_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.d δr Gr_vr) (⟨Rvr_n3, Rvr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_vr, Rvr_n3, Rvr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `∂_r Γ^p_{vp}` over the common denominator. -/
def Rvr_n4 : ZExp 5 := -a ^ 2 * (x - 1) * (x + 1) * (-8 * a ^ 2 * m * r * x ^ 2 + a ^ 2 * q ^ 2 * x
    ^ 2 + 4 * m * r ^ 3 - 5 * q ^ 2 * r ^ 2)
/-- `∂_r Γ^p_{vp}`, reduced to the common denominator. -/
theorem Rvr_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.d δr Gp_vp) (⟨Rvr_n4, Rvr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vp, Rvr_n4, Rvr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `Γ^r_{vr} Γ^x_{rx}` over the common denominator. -/
def Rvr_n5 : ZExp 5 := r * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^ 2 * r)
/-- `Γ^r_{vr} Γ^x_{rx}`, reduced to the common denominator. -/
theorem Rvr_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gr_vr * Gx_rx) (⟨Rvr_n5, Rvr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_vr, Gx_rx, Rvr_n5, Rvr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^r_{vr} Γ^p_{rp}` over the common denominator. -/
def Rvr_n6 : ZExp 5 := r * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^ 2 * r)
/-- `Γ^r_{vr} Γ^p_{rp}`, reduced to the common denominator. -/
theorem Rvr_t6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gr_vr * Gp_rp) (⟨Rvr_n6, Rvr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rp, Gr_vr, Rvr_n6, Rvr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^x_{vv} Γ^v_{rx}` over the common denominator. -/
def Rvr_n7 : ZExp 5 := a ^ 4 * x ^ 2 * (x - 1) * (x + 1) * (-2 * m * r + q ^ 2)
/-- `Γ^x_{vv} Γ^v_{rx}`, reduced to the common denominator. -/
theorem Rvr_t7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_vv * Gv_rx) (⟨Rvr_n7, Rvr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_rx, Gx_vv, Rvr_n7, Rvr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{vv} Γ^v_{rp}` over the common denominator. -/
def Rvr_n8 : ZExp 5 := a ^ 2 * r * (x - 1) * (x + 1) * (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^ 2 * r)
/-- `Γ^p_{vv} Γ^v_{rp}`, reduced to the common denominator. -/
theorem Rvr_t8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_vv * Gv_rp) (⟨Rvr_n8, Rvr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vv, Gv_rp, Rvr_n8, Rvr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{vx} Γ^x_{rp}` over the common denominator. -/
def Rvr_n9 : ZExp 5 := a ^ 2 * x ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) * (-2 * m * r + q ^ 2)
/-- `Γ^p_{vx} Γ^x_{rp}`, reduced to the common denominator. -/
theorem Rvr_t9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_vx * Gx_rp) (⟨Rvr_n9, Rvr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vx, Gx_rp, Rvr_n9, Rvr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^x_{vp} Γ^p_{rx}` over the common denominator. -/
def Rvr_n10 : ZExp 5 := a ^ 2 * x ^ 2 * (a ^ 2 + r ^ 2) * (-2 * m * r + q ^ 2)
/-- `Γ^x_{vp} Γ^p_{rx}`, reduced to the common denominator. -/
theorem Rvr_t10 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_vp * Gp_rx) (⟨Rvr_n10, Rvr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rx, Gx_vp, Rvr_n10, Rvr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{vp} Γ^p_{rp}` over the common denominator. -/
def Rvr_n11 : ZExp 5 := -a ^ 2 * r * (x - 1) * (x + 1) * (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^ 2 * r)
/-- `Γ^p_{vp} Γ^p_{rp}`, reduced to the common denominator. -/
theorem Rvr_t11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_vp * Gp_rp) (⟨Rvr_n11, Rvr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rp, Gp_vp, Rvr_n11, Rvr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- `R_{vr}`: the signed sum of its terms is `-Kf`. -/
theorem ricci_vr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Rvr_n1 - Rvr_n2 - Rvr_n3 - Rvr_n4 + Rvr_n5 + Rvr_n6 - Rvr_n7 - Rvr_n8 -
          Rvr_n9 - Rvr_n10 - Rvr_n11, Rvr_cd⟩) (-Kf))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Rvr_n1, Rvr_n2, Rvr_n3, Rvr_n4, Rvr_n5, Rvr_n6, Rvr_n7, Rvr_n8, Rvr_n9,
        Rvr_n10, Rvr_n11, Rvr_cd, Kf, Sg, sx, Pp, Dl, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-! ## The entry `R_{vx}` -/

/-- The common denominator of the terms of `R_{vx}`. -/
def Rvx_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `∂_x Γ^v_{vv}` over the common denominator. -/
def Rvx_n1 : ZExp 5 := 2 * a ^ 2 * x * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) * (2 * a ^ 2 * m *
    x ^ 2 - 4 * m * r ^ 2 + 3 * q ^ 2 * r)
/-- `∂_x Γ^v_{vv}`, reduced to the common denominator. -/
theorem Rvx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.d δx Gv_vv) (⟨Rvx_n1, Rvx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_vv, Rvx_n1, Rvx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `∂_x Γ^r_{vr}` over the common denominator. -/
def Rvx_n2 : ZExp 5 := -2 * a ^ 2 * x * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^ 2 * m * x ^ 2 - 3 * m *
    r ^ 2 + 2 * q ^ 2 * r)
/-- `∂_x Γ^r_{vr}`, reduced to the common denominator. -/
theorem Rvx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.d δx Gr_vr) (⟨Rvx_n2, Rvx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_vr, Rvx_n2, Rvx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `∂_x Γ^p_{vp}` over the common denominator. -/
def Rvx_n3 : ZExp 5 := 2 * a ^ 2 * x * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 4 * m * x ^ 4 - 2 * a ^ 4 * m
    * x ^ 2 - 4 * a ^ 2 * m * r ^ 2 * x ^ 2 + 4 * a ^ 2 * m * r ^ 2 + 2 * a ^ 2 * q ^ 2 * r * x ^ 2
    - 3 * a ^ 2 * q ^ 2 * r + m * r ^ 4 - q ^ 2 * r ^ 3)
/-- `∂_x Γ^p_{vp}`, reduced to the common denominator. -/
theorem Rvx_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.d δx Gp_vp) (⟨Rvx_n3, Rvx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vp, Rvx_n3, Rvx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `Γ^v_{vx} Γ^v_{vv}` over the common denominator. -/
def Rvx_n4 : ZExp 5 := a ^ 2 * x * (a ^ 2 + r ^ 2) * (-2 * m * r + q ^ 2) * (a ^ 2 * m * x ^ 2 - m
    * r ^ 2 + q ^ 2 * r)
/-- `Γ^v_{vx} Γ^v_{vv}`, reduced to the common denominator. -/
theorem Rvx_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_vx * Gv_vv) (⟨Rvx_n4, Rvx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_vv, Gv_vx, Rvx_n4, Rvx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^v_{vx} Γ^r_{vr}` over the common denominator. -/
def Rvx_n5 : ZExp 5 := -a ^ 2 * x * (a ^ 2 * x ^ 2 + r ^ 2) * (-2 * m * r + q ^ 2) * (a ^ 2 * m * x
    ^ 2 - m * r ^ 2 + q ^ 2 * r)
/-- `Γ^v_{vx} Γ^r_{vr}`, reduced to the common denominator. -/
theorem Rvx_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_vx * Gr_vr) (⟨Rvx_n5, Rvx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_vr, Gv_vx, Rvx_n5, Rvx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^v_{vx} Γ^p_{vp}` over the common denominator. -/
def Rvx_n6 : ZExp 5 := a ^ 4 * x * (x - 1) * (x + 1) * (-2 * m * r + q ^ 2) * (a ^ 2 * m * x ^ 2 -
    m * r ^ 2 + q ^ 2 * r)
/-- `Γ^v_{vx} Γ^p_{vp}`, reduced to the common denominator. -/
theorem Rvx_t6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_vx * Gp_vp) (⟨Rvx_n6, Rvx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vp, Gv_vx, Rvx_n6, Rvx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{vx} Γ^v_{pv}` over the common denominator. -/
def Rvx_n7 : ZExp 5 := -a ^ 2 * x * (a ^ 2 + r ^ 2) * (-2 * m * r + q ^ 2) * (a ^ 2 * m * x ^ 2 - m
    * r ^ 2 + q ^ 2 * r)
/-- `Γ^p_{vx} Γ^v_{pv}`, reduced to the common denominator. -/
theorem Rvx_t7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_vx * Gv_vp) (⟨Rvx_n7, Rvx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vx, Gv_vp, Rvx_n7, Rvx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{vx} Γ^r_{pr}` over the common denominator. -/
def Rvx_n8 : ZExp 5 := -a ^ 2 * x * (a ^ 2 * x ^ 2 + r ^ 2) * (-2 * m * r + q ^ 2) * (-a ^ 2 * m *
    x ^ 2 + a ^ 2 * r * x ^ 2 + m * r ^ 2 - q ^ 2 * r + r ^ 3)
/-- `Γ^p_{vx} Γ^r_{pr}`, reduced to the common denominator. -/
theorem Rvx_t8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_vx * Gr_rp) (⟨Rvx_n8, Rvx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vx, Gr_rp, Rvx_n8, Rvx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{vx} Γ^p_{pp}` over the common denominator. -/
def Rvx_n9 : ZExp 5 := a ^ 2 * x * (-2 * m * r + q ^ 2) * (-a ^ 4 * m * x ^ 4 + a ^ 4 * m * x ^ 2 +
    a ^ 4 * r * x ^ 4 + a ^ 2 * m * r ^ 2 * x ^ 2 - a ^ 2 * m * r ^ 2 - a ^ 2 * q ^ 2 * r * x ^ 2 +
    a ^ 2 * q ^ 2 * r + 2 * a ^ 2 * r ^ 3 * x ^ 2 + r ^ 5)
/-- `Γ^p_{vx} Γ^p_{pp}`, reduced to the common denominator. -/
theorem Rvx_t9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_vx * Gp_pp) (⟨Rvx_n9, Rvx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_pp, Gp_vx, Rvx_n9, Rvx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^v_{vv} Γ^v_{xv}` over the common denominator. -/
def Rvx_n10 : ZExp 5 := a ^ 2 * x * (a ^ 2 + r ^ 2) * (-2 * m * r + q ^ 2) * (a ^ 2 * m * x ^ 2 - m
    * r ^ 2 + q ^ 2 * r)
/-- `Γ^v_{vv} Γ^v_{xv}`, reduced to the common denominator. -/
theorem Rvx_t10 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_vv * Gv_vx) (⟨Rvx_n10, Rvx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_vv, Gv_vx, Rvx_n10, Rvx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^r_{vv} Γ^v_{xr}` over the common denominator. -/
def Rvx_n11 : ZExp 5 := -a ^ 2 * x * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^
    2 * r) * (a ^ 2 - 2 * m * r + q ^ 2 + r ^ 2)
/-- `Γ^r_{vv} Γ^v_{xr}`, reduced to the common denominator. -/
theorem Rvx_t11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gr_vv * Gv_rx) (⟨Rvx_n11, Rvx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_vv, Gv_rx, Rvx_n11, Rvx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^x_{vv} Γ^v_{xx}` over the common denominator. -/
def Rvx_n12 : ZExp 5 := a ^ 2 * r * x * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) * (-2 * m * r + q
    ^ 2)
/-- `Γ^x_{vv} Γ^v_{xx}`, reduced to the common denominator. -/
theorem Rvx_t12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_vv * Gv_xx) (⟨Rvx_n12, Rvx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_xx, Gx_vv, Rvx_n12, Rvx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{vv} Γ^v_{xp}` over the common denominator. -/
def Rvx_n13 : ZExp 5 := a ^ 4 * x * (x - 1) * (x + 1) * (-2 * m * r + q ^ 2) * (a ^ 2 * m * x ^ 2 -
    m * r ^ 2 + q ^ 2 * r)
/-- `Γ^p_{vv} Γ^v_{xp}`, reduced to the common denominator. -/
theorem Rvx_t13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_vv * Gv_xp) (⟨Rvx_n13, Rvx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vv, Gv_xp, Rvx_n13, Rvx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^r_{vr} Γ^r_{xr}` over the common denominator. -/
def Rvx_n14 : ZExp 5 := a ^ 2 * x * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^ 2 * m * x ^ 2 - m * r ^ 2 +
    q ^ 2 * r)
/-- `Γ^r_{vr} Γ^r_{xr}`, reduced to the common denominator. -/
theorem Rvx_t14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gr_vr * Gr_rx) (⟨Rvx_n14, Rvx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Gr_vr, Rvx_n14, Rvx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^v_{vp} Γ^p_{xv}` over the common denominator. -/
def Rvx_n15 : ZExp 5 := -a ^ 2 * x * (a ^ 2 + r ^ 2) * (-2 * m * r + q ^ 2) * (a ^ 2 * m * x ^ 2 -
    m * r ^ 2 + q ^ 2 * r)
/-- `Γ^v_{vp} Γ^p_{xv}`, reduced to the common denominator. -/
theorem Rvx_t15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_vp * Gp_vx) (⟨Rvx_n15, Rvx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vx, Gv_vp, Rvx_n15, Rvx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^r_{vp} Γ^p_{xr}` over the common denominator. -/
def Rvx_n16 : ZExp 5 := a ^ 2 * x * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^
    2 * r) * (a ^ 2 - 2 * m * r + q ^ 2 + r ^ 2)
/-- `Γ^r_{vp} Γ^p_{xr}`, reduced to the common denominator. -/
theorem Rvx_t16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gr_vp * Gp_rx) (⟨Rvx_n16, Rvx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rx, Gr_vp, Rvx_n16, Rvx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^x_{vp} Γ^p_{xx}` over the common denominator. -/
def Rvx_n17 : ZExp 5 := -a ^ 2 * r * x * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) * (-2 * m * r +
    q ^ 2)
/-- `Γ^x_{vp} Γ^p_{xx}`, reduced to the common denominator. -/
theorem Rvx_t17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_vp * Gp_xx) (⟨Rvx_n17, Rvx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_xx, Gx_vp, Rvx_n17, Rvx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{vp} Γ^p_{xp}` over the common denominator. -/
def Rvx_n18 : ZExp 5 := -a ^ 2 * x * (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^ 2 * r) * (a ^ 4 * x ^ 4 -
    2 * a ^ 2 * m * r * x ^ 2 + 2 * a ^ 2 * m * r + a ^ 2 * q ^ 2 * x ^ 2 - a ^ 2 * q ^ 2 + 2 * a ^
    2 * r ^ 2 * x ^ 2 + r ^ 4)
/-- `Γ^p_{vp} Γ^p_{xp}`, reduced to the common denominator. -/
theorem Rvx_t18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_vp * Gp_xp) (⟨Rvx_n18, Rvx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vp, Gp_xp, Rvx_n18, Rvx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- `R_{vx}`: the signed sum of its terms is `Frac.ofZ 0`. -/
theorem ricci_vx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨0 - Rvx_n1 - Rvx_n2 - Rvx_n3 + Rvx_n4 + Rvx_n5 + Rvx_n6 + Rvx_n7 + Rvx_n8
          + Rvx_n9 - Rvx_n10 - Rvx_n11 - Rvx_n12 - Rvx_n13 - Rvx_n14 - Rvx_n15 - Rvx_n16 - Rvx_n17
          - Rvx_n18, Rvx_cd⟩) (Frac.ofZ 0))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Rvx_n1, Rvx_n2, Rvx_n3, Rvx_n4, Rvx_n5, Rvx_n6, Rvx_n7, Rvx_n8, Rvx_n9,
        Rvx_n10, Rvx_n11, Rvx_n12, Rvx_n13, Rvx_n14, Rvx_n15, Rvx_n16, Rvx_n17, Rvx_n18, Rvx_cd,
        δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ## The entry `R_{vp}` -/

/-- The common denominator of the terms of `R_{vp}`. -/
def Rvp_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 6

/-- The numerator of `∂_r Γ^r_{vp}` over the common denominator. -/
def Rvp_n1 : ZExp 5 := -a * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (-2 * a ^ 4 * m ^ 2 *
    x ^ 4 + 2 * a ^ 4 * m * r * x ^ 4 - 8 * a ^ 4 * m * r * x ^ 2 + a ^ 4 * q ^ 2 * x ^ 2 + 16 * a
    ^ 2 * m ^ 2 * r ^ 2 * x ^ 2 - 12 * a ^ 2 * m * q ^ 2 * r * x ^ 2 - 8 * a ^ 2 * m * r ^ 3 * x ^
    2 + 4 * a ^ 2 * m * r ^ 3 + a ^ 2 * q ^ 4 * x ^ 2 + 3 * a ^ 2 * q ^ 2 * r ^ 2 * x ^ 2 - 5 * a ^
    2 * q ^ 2 * r ^ 2 - 6 * m ^ 2 * r ^ 4 + 12 * m * q ^ 2 * r ^ 3 + 2 * m * r ^ 5 - 5 * q ^ 4 * r
    ^ 2 - 3 * q ^ 2 * r ^ 4)
/-- `∂_r Γ^r_{vp}`, reduced to the common denominator. -/
theorem Rvp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.d δr Gr_vp) (⟨Rvp_n1, Rvp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_vp, Rvp_n1, Rvp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `∂_x Γ^x_{vp}` over the common denominator. -/
def Rvp_n2 : ZExp 5 := a * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (-2 * m * r + q ^ 2) *
    (3 * a ^ 2 * x ^ 4 - 5 * a ^ 2 * x ^ 2 - 3 * r ^ 2 * x ^ 2 + r ^ 2)
/-- `∂_x Γ^x_{vp}`, reduced to the common denominator. -/
theorem Rvp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.d δx Gx_vp) (⟨Rvp_n2, Rvp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_vp, Rvp_n2, Rvp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `Γ^v_{vp} Γ^v_{vv}` over the common denominator. -/
def Rvp_n3 : ZExp 5 := a * (a ^ 2 + r ^ 2) ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * m * x ^ 2 - m * r ^ 2
    + q ^ 2 * r) ^ 2
/-- `Γ^v_{vp} Γ^v_{vv}`, reduced to the common denominator. -/
theorem Rvp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_vp * Gv_vv) (⟨Rvp_n3, Rvp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_vp, Gv_vv, Rvp_n3, Rvp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^v_{vp} Γ^r_{vr}` over the common denominator. -/
def Rvp_n4 : ZExp 5 := -a * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2
    * m * x ^ 2 - m * r ^ 2 + q ^ 2 * r) ^ 2
/-- `Γ^v_{vp} Γ^r_{vr}`, reduced to the common denominator. -/
theorem Rvp_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_vp * Gr_vr) (⟨Rvp_n4, Rvp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_vr, Gv_vp, Rvp_n4, Rvp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^v_{vp} Γ^p_{vp}` over the common denominator. -/
def Rvp_n5 : ZExp 5 := a ^ 3 * (a ^ 2 + r ^ 2) * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * m * x ^ 2 - m
    * r ^ 2 + q ^ 2 * r) ^ 2
/-- `Γ^v_{vp} Γ^p_{vp}`, reduced to the common denominator. -/
theorem Rvp_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_vp * Gp_vp) (⟨Rvp_n5, Rvp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vp, Gv_vp, Rvp_n5, Rvp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^r_{vp} Γ^x_{rx}` over the common denominator. -/
def Rvp_n6 : ZExp 5 := -a * r * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^ 2 * m * x ^
    2 - m * r ^ 2 + q ^ 2 * r) * (a ^ 2 - 2 * m * r + q ^ 2 + r ^ 2)
/-- `Γ^r_{vp} Γ^x_{rx}`, reduced to the common denominator. -/
theorem Rvp_t6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gr_vp * Gx_rx) (⟨Rvp_n6, Rvp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_vp, Gx_rx, Rvp_n6, Rvp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^r_{vp} Γ^p_{rp}` over the common denominator. -/
def Rvp_n7 : ZExp 5 := -a * r * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^ 2 * m * x ^
    2 - m * r ^ 2 + q ^ 2 * r) * (a ^ 2 - 2 * m * r + q ^ 2 + r ^ 2)
/-- `Γ^r_{vp} Γ^p_{rp}`, reduced to the common denominator. -/
theorem Rvp_t7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gr_vp * Gp_rp) (⟨Rvp_n7, Rvp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rp, Gr_vp, Rvp_n7, Rvp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^x_{vp} Γ^v_{xv}` over the common denominator. -/
def Rvp_n8 : ZExp 5 := a ^ 3 * x ^ 2 * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^
    2) * (-2 * m * r + q ^ 2) ^ 2
/-- `Γ^x_{vp} Γ^v_{xv}`, reduced to the common denominator. -/
theorem Rvp_t8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_vp * Gv_vx) (⟨Rvp_n8, Rvp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_vx, Gx_vp, Rvp_n8, Rvp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^x_{vp} Γ^r_{xr}` over the common denominator. -/
def Rvp_n9 : ZExp 5 := -a ^ 3 * x ^ 2 * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^
    2) ^ 2 * (-2 * m * r + q ^ 2)
/-- `Γ^x_{vp} Γ^r_{xr}`, reduced to the common denominator. -/
theorem Rvp_t9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_vp * Gr_rx) (⟨Rvp_n9, Rvp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Gx_vp, Rvp_n9, Rvp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^x_{vp} Γ^x_{xx}` over the common denominator. -/
def Rvp_n10 : ZExp 5 := a * x ^ 2 * (a ^ 2 + r ^ 2) ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (-2 * m * r
    + q ^ 2)
/-- `Γ^x_{vp} Γ^x_{xx}`, reduced to the common denominator. -/
theorem Rvp_t10 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_vp * Gx_xx) (⟨Rvp_n10, Rvp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_vp, Gx_xx, Rvp_n10, Rvp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^x_{vp} Γ^p_{xp}` over the common denominator. -/
def Rvp_n11 : ZExp 5 := -a * x ^ 2 * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) * (-2 * m * r + q ^
    2) * (a ^ 4 * x ^ 4 - 2 * a ^ 2 * m * r * x ^ 2 + 2 * a ^ 2 * m * r + a ^ 2 * q ^ 2 * x ^ 2 - a
    ^ 2 * q ^ 2 + 2 * a ^ 2 * r ^ 2 * x ^ 2 + r ^ 4)
/-- `Γ^x_{vp} Γ^p_{xp}`, reduced to the common denominator. -/
theorem Rvp_t11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_vp * Gp_xp) (⟨Rvp_n11, Rvp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_xp, Gx_vp, Rvp_n11, Rvp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{vp} Γ^v_{pv}` over the common denominator. -/
def Rvp_n12 : ZExp 5 := a ^ 3 * (a ^ 2 + r ^ 2) * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * m * x ^ 2 -
    m * r ^ 2 + q ^ 2 * r) ^ 2
/-- `Γ^p_{vp} Γ^v_{pv}`, reduced to the common denominator. -/
theorem Rvp_t12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_vp * Gv_vp) (⟨Rvp_n12, Rvp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vp, Gv_vp, Rvp_n12, Rvp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{vp} Γ^r_{pr}` over the common denominator. -/
def Rvp_n13 : ZExp 5 := a ^ 3 * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 * m *
    x ^ 2 - m * r ^ 2 + q ^ 2 * r) * (-a ^ 2 * m * x ^ 2 + a ^ 2 * r * x ^ 2 + m * r ^ 2 - q ^ 2 *
    r + r ^ 3)
/-- `Γ^p_{vp} Γ^r_{pr}`, reduced to the common denominator. -/
theorem Rvp_t13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_vp * Gr_rp) (⟨Rvp_n13, Rvp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vp, Gr_rp, Rvp_n13, Rvp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{vp} Γ^p_{pp}` over the common denominator. -/
def Rvp_n14 : ZExp 5 := -a ^ 3 * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^ 2
    * r) * (-a ^ 4 * m * x ^ 4 + a ^ 4 * m * x ^ 2 + a ^ 4 * r * x ^ 4 + a ^ 2 * m * r ^ 2 * x ^ 2
    - a ^ 2 * m * r ^ 2 - a ^ 2 * q ^ 2 * r * x ^ 2 + a ^ 2 * q ^ 2 * r + 2 * a ^ 2 * r ^ 3 * x ^ 2
    + r ^ 5)
/-- `Γ^p_{vp} Γ^p_{pp}`, reduced to the common denominator. -/
theorem Rvp_t14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_vp * Gp_pp) (⟨Rvp_n14, Rvp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_pp, Gp_vp, Rvp_n14, Rvp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^v_{vv} Γ^v_{pv}` over the common denominator. -/
def Rvp_n15 : ZExp 5 := a * (a ^ 2 + r ^ 2) ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * m * x ^ 2 - m * r ^
    2 + q ^ 2 * r) ^ 2
/-- `Γ^v_{vv} Γ^v_{pv}`, reduced to the common denominator. -/
theorem Rvp_t15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_vv * Gv_vp) (⟨Rvp_n15, Rvp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_vp, Gv_vv, Rvp_n15, Rvp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^r_{vv} Γ^v_{pr}` over the common denominator. -/
def Rvp_n16 : ZExp 5 := a * r * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^ 2 * m * x ^
    2 - m * r ^ 2 + q ^ 2 * r) * (a ^ 2 - 2 * m * r + q ^ 2 + r ^ 2)
/-- `Γ^r_{vv} Γ^v_{pr}`, reduced to the common denominator. -/
theorem Rvp_t16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gr_vv * Gv_rp) (⟨Rvp_n16, Rvp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_vv, Gv_rp, Rvp_n16, Rvp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^x_{vv} Γ^v_{px}` over the common denominator. -/
def Rvp_n17 : ZExp 5 := -a ^ 5 * x ^ 2 * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) * (-2
    * m * r + q ^ 2) ^ 2
/-- `Γ^x_{vv} Γ^v_{px}`, reduced to the common denominator. -/
theorem Rvp_t17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_vv * Gv_xp) (⟨Rvp_n17, Rvp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_xp, Gx_vv, Rvp_n17, Rvp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{vv} Γ^v_{pp}` over the common denominator. -/
def Rvp_n18 : ZExp 5 := -a * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 * m * x ^ 2 - m * r ^ 2 +
    q ^ 2 * r) * (-a ^ 4 * m * x ^ 4 + a ^ 4 * m * x ^ 2 + a ^ 4 * r * x ^ 4 + a ^ 2 * m * r ^ 2 *
    x ^ 2 - a ^ 2 * m * r ^ 2 - a ^ 2 * q ^ 2 * r * x ^ 2 + a ^ 2 * q ^ 2 * r + 2 * a ^ 2 * r ^ 3 *
    x ^ 2 + r ^ 5)
/-- `Γ^p_{vv} Γ^v_{pp}`, reduced to the common denominator. -/
theorem Rvp_t18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_vv * Gv_pp) (⟨Rvp_n18, Rvp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vv, Gv_pp, Rvp_n18, Rvp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^r_{vr} Γ^r_{pr}` over the common denominator. -/
def Rvp_n19 : ZExp 5 := -a * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^ 2 * m * x ^ 2 -
    m * r ^ 2 + q ^ 2 * r) * (-a ^ 2 * m * x ^ 2 + a ^ 2 * r * x ^ 2 + m * r ^ 2 - q ^ 2 * r + r ^
    3)
/-- `Γ^r_{vr} Γ^r_{pr}`, reduced to the common denominator. -/
theorem Rvp_t19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gr_vr * Gr_rp) (⟨Rvp_n19, Rvp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rp, Gr_vr, Rvp_n19, Rvp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^v_{vx} Γ^x_{pv}` over the common denominator. -/
def Rvp_n20 : ZExp 5 := a ^ 3 * x ^ 2 * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^
    2) * (-2 * m * r + q ^ 2) ^ 2
/-- `Γ^v_{vx} Γ^x_{pv}`, reduced to the common denominator. -/
theorem Rvp_t20 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_vx * Gx_vp) (⟨Rvp_n20, Rvp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_vx, Gx_vp, Rvp_n20, Rvp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{vx} Γ^x_{pp}` over the common denominator. -/
def Rvp_n21 : ZExp 5 := -a * x ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) * (-2 * m * r + q ^ 2) * (a ^ 6 * x ^
    4 - 2 * a ^ 4 * m * r * x ^ 4 + 2 * a ^ 4 * m * r + a ^ 4 * q ^ 2 * x ^ 4 - a ^ 4 * q ^ 2 + a ^
    4 * r ^ 2 * x ^ 4 + 2 * a ^ 4 * r ^ 2 * x ^ 2 - 4 * a ^ 2 * m * r ^ 3 * x ^ 2 + 4 * a ^ 2 * m *
    r ^ 3 + 2 * a ^ 2 * q ^ 2 * r ^ 2 * x ^ 2 - 2 * a ^ 2 * q ^ 2 * r ^ 2 + 2 * a ^ 2 * r ^ 4 * x ^
    2 + a ^ 2 * r ^ 4 + r ^ 6)
/-- `Γ^p_{vx} Γ^x_{pp}`, reduced to the common denominator. -/
theorem Rvp_t21 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_vx * Gx_pp) (⟨Rvp_n21, Rvp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vx, Gx_pp, Rvp_n21, Rvp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^v_{vp} Γ^p_{pv}` over the common denominator. -/
def Rvp_n22 : ZExp 5 := a ^ 3 * (a ^ 2 + r ^ 2) * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * m * x ^ 2 -
    m * r ^ 2 + q ^ 2 * r) ^ 2
/-- `Γ^v_{vp} Γ^p_{pv}`, reduced to the common denominator. -/
theorem Rvp_t22 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_vp * Gp_vp) (⟨Rvp_n22, Rvp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vp, Gv_vp, Rvp_n22, Rvp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^r_{vp} Γ^p_{pr}` over the common denominator. -/
def Rvp_n23 : ZExp 5 := -a * r * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^ 2 * m * x ^
    2 - m * r ^ 2 + q ^ 2 * r) * (a ^ 2 - 2 * m * r + q ^ 2 + r ^ 2)
/-- `Γ^r_{vp} Γ^p_{pr}`, reduced to the common denominator. -/
theorem Rvp_t23 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gr_vp * Gp_rp) (⟨Rvp_n23, Rvp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rp, Gr_vp, Rvp_n23, Rvp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^x_{vp} Γ^p_{px}` over the common denominator. -/
def Rvp_n24 : ZExp 5 := -a * x ^ 2 * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) * (-2 * m * r + q ^
    2) * (a ^ 4 * x ^ 4 - 2 * a ^ 2 * m * r * x ^ 2 + 2 * a ^ 2 * m * r + a ^ 2 * q ^ 2 * x ^ 2 - a
    ^ 2 * q ^ 2 + 2 * a ^ 2 * r ^ 2 * x ^ 2 + r ^ 4)
/-- `Γ^x_{vp} Γ^p_{px}`, reduced to the common denominator. -/
theorem Rvp_t24 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_vp * Gp_xp) (⟨Rvp_n24, Rvp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_xp, Gx_vp, Rvp_n24, Rvp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{vp} Γ^p_{pp}` over the common denominator. -/
def Rvp_n25 : ZExp 5 := -a ^ 3 * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^ 2
    * r) * (-a ^ 4 * m * x ^ 4 + a ^ 4 * m * x ^ 2 + a ^ 4 * r * x ^ 4 + a ^ 2 * m * r ^ 2 * x ^ 2
    - a ^ 2 * m * r ^ 2 - a ^ 2 * q ^ 2 * r * x ^ 2 + a ^ 2 * q ^ 2 * r + 2 * a ^ 2 * r ^ 3 * x ^ 2
    + r ^ 5)
/-- `Γ^p_{vp} Γ^p_{pp}`, reduced to the common denominator. -/
theorem Rvp_t25 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_vp * Gp_pp) (⟨Rvp_n25, Rvp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_pp, Gp_vp, Rvp_n25, Rvp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- `R_{vp}`: the signed sum of its terms is `-(Kf * ⟨a * sx * (Dl + Pp), Sg⟩)`. -/
theorem ricci_vp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Rvp_n1 + Rvp_n2 + Rvp_n3 + Rvp_n4 + Rvp_n5 + Rvp_n6 + Rvp_n7 + Rvp_n8 +
          Rvp_n9 + Rvp_n10 + Rvp_n11 + Rvp_n12 + Rvp_n13 + Rvp_n14 - Rvp_n15 - Rvp_n16 - Rvp_n17 -
          Rvp_n18 - Rvp_n19 - Rvp_n20 - Rvp_n21 - Rvp_n22 - Rvp_n23 - Rvp_n24 - Rvp_n25, Rvp_cd⟩)
          (-(Kf * ⟨a * sx * (Dl + Pp), Sg⟩)))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Rvp_n1, Rvp_n2, Rvp_n3, Rvp_n4, Rvp_n5, Rvp_n6, Rvp_n7, Rvp_n8, Rvp_n9,
        Rvp_n10, Rvp_n11, Rvp_n12, Rvp_n13, Rvp_n14, Rvp_n15, Rvp_n16, Rvp_n17, Rvp_n18, Rvp_n19,
        Rvp_n20, Rvp_n21, Rvp_n22, Rvp_n23, Rvp_n24, Rvp_n25, Rvp_cd, Kf, Sg, sx, Pp, Dl, δr_0,
        δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ## The entry `R_{rr}` -/

/-- The common denominator of the terms of `R_{rr}`. -/
def Rrr_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 2

/-- The numerator of `∂_r Γ^x_{rx}` over the common denominator. -/
def Rrr_n1 : ZExp 5 := (a * x - r) * (a * x + r)
/-- `∂_r Γ^x_{rx}`, reduced to the common denominator. -/
theorem Rrr_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.d δr Gx_rx) (⟨Rrr_n1, Rrr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rx, Rrr_n1, Rrr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `∂_r Γ^p_{rp}` over the common denominator. -/
def Rrr_n2 : ZExp 5 := (a * x - r) * (a * x + r)
/-- `∂_r Γ^p_{rp}`, reduced to the common denominator. -/
theorem Rrr_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.d δr Gp_rp) (⟨Rrr_n2, Rrr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rp, Rrr_n2, Rrr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `Γ^x_{rx} Γ^x_{rx}` over the common denominator. -/
def Rrr_n3 : ZExp 5 := r ^ 2
/-- `Γ^x_{rx} Γ^x_{rx}`, reduced to the common denominator. -/
theorem Rrr_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_rx * Gx_rx) (⟨Rrr_n3, Rrr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rx, Rrr_n3, Rrr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `Γ^p_{rx} Γ^x_{rp}` over the common denominator. -/
def Rrr_n4 : ZExp 5 := -a ^ 2 * x ^ 2
/-- `Γ^p_{rx} Γ^x_{rp}`, reduced to the common denominator. -/
theorem Rrr_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_rx * Gx_rp) (⟨Rrr_n4, Rrr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rx, Gx_rp, Rrr_n4, Rrr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^x_{rp} Γ^p_{rx}` over the common denominator. -/
def Rrr_n5 : ZExp 5 := -a ^ 2 * x ^ 2
/-- `Γ^x_{rp} Γ^p_{rx}`, reduced to the common denominator. -/
theorem Rrr_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_rp * Gp_rx) (⟨Rrr_n5, Rrr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rx, Gx_rp, Rrr_n5, Rrr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{rp} Γ^p_{rp}` over the common denominator. -/
def Rrr_n6 : ZExp 5 := r ^ 2
/-- `Γ^p_{rp} Γ^p_{rp}`, reduced to the common denominator. -/
theorem Rrr_t6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_rp * Gp_rp) (⟨Rrr_n6, Rrr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rp, Rrr_n6, Rrr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- `R_{rr}`: the signed sum of its terms is `Frac.ofZ 0`. -/
theorem ricci_rr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨0 - Rrr_n1 - Rrr_n2 - Rrr_n3 - Rrr_n4 - Rrr_n5 - Rrr_n6, Rrr_cd⟩)
          (Frac.ofZ 0))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Rrr_n1, Rrr_n2, Rrr_n3, Rrr_n4, Rrr_n5, Rrr_n6, Rrr_cd, δr_0, δr_1, δr_2,
        δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ## The entry `R_{rx}` -/

/-- The common denominator of the terms of `R_{rx}`. -/
def Rrx_cd : ZExp 5 := (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4

/-- The numerator of `∂_r Γ^r_{rx}` over the common denominator. -/
def Rrx_n1 : ZExp 5 := -2 * a ^ 2 * r * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `∂_r Γ^r_{rx}`, reduced to the common denominator. -/
theorem Rrx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.d δr Gr_rx) (⟨Rrx_n1, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Rrx_n1, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `∂_x Γ^x_{rx}` over the common denominator. -/
def Rrx_n2 : ZExp 5 := -2 * a ^ 2 * r * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `∂_x Γ^x_{rx}`, reduced to the common denominator. -/
theorem Rrx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.d δx Gx_rx) (⟨Rrx_n2, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rx, Rrx_n2, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `∂_x Γ^x_{rx}` over the common denominator. -/
def Rrx_n3 : ZExp 5 := -2 * a ^ 2 * r * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `∂_x Γ^x_{rx}`, reduced to the common denominator. -/
theorem Rrx_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.d δx Gx_rx) (⟨Rrx_n3, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rx, Rrx_n3, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `∂_x Γ^p_{rp}` over the common denominator. -/
def Rrx_n4 : ZExp 5 := -2 * a ^ 2 * r * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `∂_x Γ^p_{rp}`, reduced to the common denominator. -/
theorem Rrx_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.d δx Gp_rp) (⟨Rrx_n4, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rp, Rrx_n4, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `Γ^v_{rx} Γ^v_{vv}` over the common denominator. -/
def Rrx_n5 : ZExp 5 := -a ^ 2 * x * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 * m * x ^ 2 - m *
    r ^ 2 + q ^ 2 * r)
/-- `Γ^v_{rx} Γ^v_{vv}`, reduced to the common denominator. -/
theorem Rrx_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_rx * Gv_vv) (⟨Rrx_n5, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_rx, Gv_vv, Rrx_n5, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^v_{rx} Γ^r_{vr}` over the common denominator. -/
def Rrx_n6 : ZExp 5 := a ^ 2 * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 * m * x ^ 2
    - m * r ^ 2 + q ^ 2 * r)
/-- `Γ^v_{rx} Γ^r_{vr}`, reduced to the common denominator. -/
theorem Rrx_t6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_rx * Gr_vr) (⟨Rrx_n6, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_vr, Gv_rx, Rrx_n6, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^v_{rx} Γ^p_{vp}` over the common denominator. -/
def Rrx_n7 : ZExp 5 := -a ^ 4 * x * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q
    ^ 2 * r)
/-- `Γ^v_{rx} Γ^p_{vp}`, reduced to the common denominator. -/
theorem Rrx_t7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_rx * Gp_vp) (⟨Rrx_n7, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vp, Gv_rx, Rrx_n7, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^r_{rx} Γ^x_{rx}` over the common denominator. -/
def Rrx_n8 : ZExp 5 := a ^ 2 * r * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `Γ^r_{rx} Γ^x_{rx}`, reduced to the common denominator. -/
theorem Rrx_t8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gr_rx * Gx_rx) (⟨Rrx_n8, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Gx_rx, Rrx_n8, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^r_{rx} Γ^p_{rp}` over the common denominator. -/
def Rrx_n9 : ZExp 5 := a ^ 2 * r * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `Γ^r_{rx} Γ^p_{rp}`, reduced to the common denominator. -/
theorem Rrx_t9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gr_rx * Gp_rp) (⟨Rrx_n9, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rp, Gr_rx, Rrx_n9, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^x_{rx} Γ^v_{xv}` over the common denominator. -/
def Rrx_n10 : ZExp 5 := -a ^ 2 * r * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (-2 * m * r
    + q ^ 2)
/-- `Γ^x_{rx} Γ^v_{xv}`, reduced to the common denominator. -/
theorem Rrx_t10 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_rx * Gv_vx) (⟨Rrx_n10, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_vx, Gx_rx, Rrx_n10, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^x_{rx} Γ^r_{xr}` over the common denominator. -/
def Rrx_n11 : ZExp 5 := a ^ 2 * r * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `Γ^x_{rx} Γ^r_{xr}`, reduced to the common denominator. -/
theorem Rrx_t11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_rx * Gr_rx) (⟨Rrx_n11, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Gx_rx, Rrx_n11, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^x_{rx} Γ^x_{xx}` over the common denominator. -/
def Rrx_n12 : ZExp 5 := -r * x * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `Γ^x_{rx} Γ^x_{xx}`, reduced to the common denominator. -/
theorem Rrx_t12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_rx * Gx_xx) (⟨Rrx_n12, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rx, Gx_xx, Rrx_n12, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^x_{rx} Γ^p_{xp}` over the common denominator. -/
def Rrx_n13 : ZExp 5 := r * x * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 4 * x ^ 4 - 2 * a ^ 2 * m * r * x ^
    2 + 2 * a ^ 2 * m * r + a ^ 2 * q ^ 2 * x ^ 2 - a ^ 2 * q ^ 2 + 2 * a ^ 2 * r ^ 2 * x ^ 2 + r ^
    4)
/-- `Γ^x_{rx} Γ^p_{xp}`, reduced to the common denominator. -/
theorem Rrx_t13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_rx * Gp_xp) (⟨Rrx_n13, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_xp, Gx_rx, Rrx_n13, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{rx} Γ^v_{pv}` over the common denominator. -/
def Rrx_n14 : ZExp 5 := a ^ 2 * x * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 * m * x ^ 2 - m *
    r ^ 2 + q ^ 2 * r)
/-- `Γ^p_{rx} Γ^v_{pv}`, reduced to the common denominator. -/
theorem Rrx_t14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_rx * Gv_vp) (⟨Rrx_n14, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rx, Gv_vp, Rrx_n14, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{rx} Γ^r_{pr}` over the common denominator. -/
def Rrx_n15 : ZExp 5 := a ^ 2 * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (-a ^ 2 * m * x ^
    2 + a ^ 2 * r * x ^ 2 + m * r ^ 2 - q ^ 2 * r + r ^ 3)
/-- `Γ^p_{rx} Γ^r_{pr}`, reduced to the common denominator. -/
theorem Rrx_t15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_rx * Gr_rp) (⟨Rrx_n15, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rx, Gr_rp, Rrx_n15, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{rx} Γ^p_{pp}` over the common denominator. -/
def Rrx_n16 : ZExp 5 := -a ^ 2 * x * (x - 1) * (x + 1) * (-a ^ 4 * m * x ^ 4 + a ^ 4 * m * x ^ 2 +
    a ^ 4 * r * x ^ 4 + a ^ 2 * m * r ^ 2 * x ^ 2 - a ^ 2 * m * r ^ 2 - a ^ 2 * q ^ 2 * r * x ^ 2 +
    a ^ 2 * q ^ 2 * r + 2 * a ^ 2 * r ^ 3 * x ^ 2 + r ^ 5)
/-- `Γ^p_{rx} Γ^p_{pp}`, reduced to the common denominator. -/
theorem Rrx_t16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_rx * Gp_pp) (⟨Rrx_n16, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_pp, Gp_rx, Rrx_n16, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^r_{rv} Γ^v_{xr}` over the common denominator. -/
def Rrx_n17 : ZExp 5 := a ^ 2 * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 * m * x ^
    2 - m * r ^ 2 + q ^ 2 * r)
/-- `Γ^r_{rv} Γ^v_{xr}`, reduced to the common denominator. -/
theorem Rrx_t17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gr_vr * Gv_rx) (⟨Rrx_n17, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_vr, Gv_rx, Rrx_n17, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^r_{rx} Γ^x_{xr}` over the common denominator. -/
def Rrx_n18 : ZExp 5 := a ^ 2 * r * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `Γ^r_{rx} Γ^x_{xr}`, reduced to the common denominator. -/
theorem Rrx_t18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gr_rx * Gx_rx) (⟨Rrx_n18, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Gx_rx, Rrx_n18, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^x_{rx} Γ^x_{xx}` over the common denominator. -/
def Rrx_n19 : ZExp 5 := -r * x * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `Γ^x_{rx} Γ^x_{xx}`, reduced to the common denominator. -/
theorem Rrx_t19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_rx * Gx_xx) (⟨Rrx_n19, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rx, Gx_xx, Rrx_n19, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^v_{rp} Γ^p_{xv}` over the common denominator. -/
def Rrx_n20 : ZExp 5 := -a ^ 2 * r * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (-2 * m * r
    + q ^ 2)
/-- `Γ^v_{rp} Γ^p_{xv}`, reduced to the common denominator. -/
theorem Rrx_t20 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_rp * Gp_vx) (⟨Rrx_n20, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vx, Gv_rp, Rrx_n20, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^r_{rp} Γ^p_{xr}` over the common denominator. -/
def Rrx_n21 : ZExp 5 := a ^ 2 * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (-a ^ 2 * m * x ^
    2 + a ^ 2 * r * x ^ 2 + m * r ^ 2 - q ^ 2 * r + r ^ 3)
/-- `Γ^r_{rp} Γ^p_{xr}`, reduced to the common denominator. -/
theorem Rrx_t21 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gr_rp * Gp_rx) (⟨Rrx_n21, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rx, Gr_rp, Rrx_n21, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^x_{rp} Γ^p_{xx}` over the common denominator. -/
def Rrx_n22 : ZExp 5 := a ^ 2 * r * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `Γ^x_{rp} Γ^p_{xx}`, reduced to the common denominator. -/
theorem Rrx_t22 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_rp * Gp_xx) (⟨Rrx_n22, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_xx, Gx_rp, Rrx_n22, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{rp} Γ^p_{xp}` over the common denominator. -/
def Rrx_n23 : ZExp 5 := r * x * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 4 * x ^ 4 - 2 * a ^ 2 * m * r * x ^
    2 + 2 * a ^ 2 * m * r + a ^ 2 * q ^ 2 * x ^ 2 - a ^ 2 * q ^ 2 + 2 * a ^ 2 * r ^ 2 * x ^ 2 + r ^
    4)
/-- `Γ^p_{rp} Γ^p_{xp}`, reduced to the common denominator. -/
theorem Rrx_t23 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_rp * Gp_xp) (⟨Rrx_n23, Rrx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rp, Gp_xp, Rrx_n23, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- `R_{rx}`: the signed sum of its terms is `Frac.ofZ 0`. -/
theorem ricci_rx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Rrx_n1 + Rrx_n2 - Rrx_n3 - Rrx_n4 + Rrx_n5 + Rrx_n6 + Rrx_n7 + Rrx_n8 +
          Rrx_n9 + Rrx_n10 + Rrx_n11 + Rrx_n12 + Rrx_n13 + Rrx_n14 + Rrx_n15 + Rrx_n16 - Rrx_n17 -
          Rrx_n18 - Rrx_n19 - Rrx_n20 - Rrx_n21 - Rrx_n22 - Rrx_n23, Rrx_cd⟩) (Frac.ofZ 0))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Rrx_n1, Rrx_n2, Rrx_n3, Rrx_n4, Rrx_n5, Rrx_n6, Rrx_n7, Rrx_n8, Rrx_n9,
        Rrx_n10, Rrx_n11, Rrx_n12, Rrx_n13, Rrx_n14, Rrx_n15, Rrx_n16, Rrx_n17, Rrx_n18, Rrx_n19,
        Rrx_n20, Rrx_n21, Rrx_n22, Rrx_n23, Rrx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-! ## The entry `R_{rp}` -/

/-- The common denominator of the terms of `R_{rp}`. -/
def Rrp_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 4

/-- The numerator of `∂_r Γ^r_{rp}` over the common denominator. -/
def Rrp_n1 : ZExp 5 := -a * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 4 * x ^ 4 + 6 * a ^
    2 * m * r * x ^ 2 - a ^ 2 * q ^ 2 * x ^ 2 - 2 * m * r ^ 3 + 3 * q ^ 2 * r ^ 2 - r ^ 4)
/-- `∂_r Γ^r_{rp}`, reduced to the common denominator. -/
theorem Rrp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.d δr Gr_rp) (⟨Rrp_n1, Rrp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rp, Rrp_n1, Rrp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `∂_x Γ^x_{rp}` over the common denominator. -/
def Rrp_n2 : ZExp 5 := a * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^ 2 * x ^ 4 + a ^ 2 * x ^ 2 + 3 * r ^ 2
    * x ^ 2 - r ^ 2)
/-- `∂_x Γ^x_{rp}`, reduced to the common denominator. -/
theorem Rrp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.d δx Gx_rp) (⟨Rrp_n2, Rrp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rp, Rrp_n2, Rrp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `Γ^v_{rp} Γ^v_{vv}` over the common denominator. -/
def Rrp_n3 : ZExp 5 := a * r * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 * m * x ^ 2 - m * r ^ 2
    + q ^ 2 * r)
/-- `Γ^v_{rp} Γ^v_{vv}`, reduced to the common denominator. -/
theorem Rrp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_rp * Gv_vv) (⟨Rrp_n3, Rrp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_rp, Gv_vv, Rrp_n3, Rrp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^v_{rp} Γ^r_{vr}` over the common denominator. -/
def Rrp_n4 : ZExp 5 := -a * r * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 * m * x ^ 2 -
    m * r ^ 2 + q ^ 2 * r)
/-- `Γ^v_{rp} Γ^r_{vr}`, reduced to the common denominator. -/
theorem Rrp_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_rp * Gr_vr) (⟨Rrp_n4, Rrp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_vr, Gv_rp, Rrp_n4, Rrp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^v_{rp} Γ^p_{vp}` over the common denominator. -/
def Rrp_n5 : ZExp 5 := a ^ 3 * r * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^
    2 * r)
/-- `Γ^v_{rp} Γ^p_{vp}`, reduced to the common denominator. -/
theorem Rrp_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_rp * Gp_vp) (⟨Rrp_n5, Rrp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vp, Gv_rp, Rrp_n5, Rrp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^r_{rp} Γ^x_{rx}` over the common denominator. -/
def Rrp_n6 : ZExp 5 := -a * r * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (-a ^ 2 * m * x ^ 2 +
    a ^ 2 * r * x ^ 2 + m * r ^ 2 - q ^ 2 * r + r ^ 3)
/-- `Γ^r_{rp} Γ^x_{rx}`, reduced to the common denominator. -/
theorem Rrp_t6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gr_rp * Gx_rx) (⟨Rrp_n6, Rrp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rp, Gx_rx, Rrp_n6, Rrp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^r_{rp} Γ^p_{rp}` over the common denominator. -/
def Rrp_n7 : ZExp 5 := -a * r * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (-a ^ 2 * m * x ^ 2 +
    a ^ 2 * r * x ^ 2 + m * r ^ 2 - q ^ 2 * r + r ^ 3)
/-- `Γ^r_{rp} Γ^p_{rp}`, reduced to the common denominator. -/
theorem Rrp_t7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gr_rp * Gp_rp) (⟨Rrp_n7, Rrp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rp, Gr_rp, Rrp_n7, Rrp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^x_{rp} Γ^v_{xv}` over the common denominator. -/
def Rrp_n8 : ZExp 5 := -a ^ 3 * x ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (-2 * m * r +
    q ^ 2)
/-- `Γ^x_{rp} Γ^v_{xv}`, reduced to the common denominator. -/
theorem Rrp_t8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_rp * Gv_vx) (⟨Rrp_n8, Rrp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_vx, Gx_rp, Rrp_n8, Rrp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^x_{rp} Γ^r_{xr}` over the common denominator. -/
def Rrp_n9 : ZExp 5 := a ^ 3 * x ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `Γ^x_{rp} Γ^r_{xr}`, reduced to the common denominator. -/
theorem Rrp_t9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_rp * Gr_rx) (⟨Rrp_n9, Rrp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Gx_rp, Rrp_n9, Rrp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^x_{rp} Γ^x_{xx}` over the common denominator. -/
def Rrp_n10 : ZExp 5 := -a * x ^ 2 * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `Γ^x_{rp} Γ^x_{xx}`, reduced to the common denominator. -/
theorem Rrp_t10 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_rp * Gx_xx) (⟨Rrp_n10, Rrp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rp, Gx_xx, Rrp_n10, Rrp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^x_{rp} Γ^p_{xp}` over the common denominator. -/
def Rrp_n11 : ZExp 5 := a * x ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 4 * x ^ 4 - 2 * a ^ 2 * m * r *
    x ^ 2 + 2 * a ^ 2 * m * r + a ^ 2 * q ^ 2 * x ^ 2 - a ^ 2 * q ^ 2 + 2 * a ^ 2 * r ^ 2 * x ^ 2 +
    r ^ 4)
/-- `Γ^x_{rp} Γ^p_{xp}`, reduced to the common denominator. -/
theorem Rrp_t11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_rp * Gp_xp) (⟨Rrp_n11, Rrp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_xp, Gx_rp, Rrp_n11, Rrp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{rp} Γ^v_{pv}` over the common denominator. -/
def Rrp_n12 : ZExp 5 := -a * r * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 * m * x ^ 2 - m * r ^
    2 + q ^ 2 * r)
/-- `Γ^p_{rp} Γ^v_{pv}`, reduced to the common denominator. -/
theorem Rrp_t12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_rp * Gv_vp) (⟨Rrp_n12, Rrp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rp, Gv_vp, Rrp_n12, Rrp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{rp} Γ^r_{pr}` over the common denominator. -/
def Rrp_n13 : ZExp 5 := -a * r * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (-a ^ 2 * m * x ^ 2
    + a ^ 2 * r * x ^ 2 + m * r ^ 2 - q ^ 2 * r + r ^ 3)
/-- `Γ^p_{rp} Γ^r_{pr}`, reduced to the common denominator. -/
theorem Rrp_t13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_rp * Gr_rp) (⟨Rrp_n13, Rrp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rp, Gr_rp, Rrp_n13, Rrp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{rp} Γ^p_{pp}` over the common denominator. -/
def Rrp_n14 : ZExp 5 := a * r * (x - 1) * (x + 1) * (-a ^ 4 * m * x ^ 4 + a ^ 4 * m * x ^ 2 + a ^ 4
    * r * x ^ 4 + a ^ 2 * m * r ^ 2 * x ^ 2 - a ^ 2 * m * r ^ 2 - a ^ 2 * q ^ 2 * r * x ^ 2 + a ^ 2
    * q ^ 2 * r + 2 * a ^ 2 * r ^ 3 * x ^ 2 + r ^ 5)
/-- `Γ^p_{rp} Γ^p_{pp}`, reduced to the common denominator. -/
theorem Rrp_t14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_rp * Gp_pp) (⟨Rrp_n14, Rrp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_pp, Gp_rp, Rrp_n14, Rrp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^r_{rv} Γ^v_{pr}` over the common denominator. -/
def Rrp_n15 : ZExp 5 := -a * r * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 * m * x ^ 2 -
    m * r ^ 2 + q ^ 2 * r)
/-- `Γ^r_{rv} Γ^v_{pr}`, reduced to the common denominator. -/
theorem Rrp_t15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gr_vr * Gv_rp) (⟨Rrp_n15, Rrp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_vr, Gv_rp, Rrp_n15, Rrp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^v_{rx} Γ^x_{pv}` over the common denominator. -/
def Rrp_n16 : ZExp 5 := -a ^ 3 * x ^ 2 * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (-2 * m * r + q ^ 2)
/-- `Γ^v_{rx} Γ^x_{pv}`, reduced to the common denominator. -/
theorem Rrp_t16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_rx * Gx_vp) (⟨Rrp_n16, Rrp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_rx, Gx_vp, Rrp_n16, Rrp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^r_{rx} Γ^x_{pr}` over the common denominator. -/
def Rrp_n17 : ZExp 5 := a ^ 3 * x ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `Γ^r_{rx} Γ^x_{pr}`, reduced to the common denominator. -/
theorem Rrp_t17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gr_rx * Gx_rp) (⟨Rrp_n17, Rrp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Gx_rp, Rrp_n17, Rrp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{rx} Γ^x_{pp}` over the common denominator. -/
def Rrp_n18 : ZExp 5 := a * x ^ 2 * (a ^ 6 * x ^ 4 - 2 * a ^ 4 * m * r * x ^ 4 + 2 * a ^ 4 * m * r
    + a ^ 4 * q ^ 2 * x ^ 4 - a ^ 4 * q ^ 2 + a ^ 4 * r ^ 2 * x ^ 4 + 2 * a ^ 4 * r ^ 2 * x ^ 2 - 4
    * a ^ 2 * m * r ^ 3 * x ^ 2 + 4 * a ^ 2 * m * r ^ 3 + 2 * a ^ 2 * q ^ 2 * r ^ 2 * x ^ 2 - 2 * a
    ^ 2 * q ^ 2 * r ^ 2 + 2 * a ^ 2 * r ^ 4 * x ^ 2 + a ^ 2 * r ^ 4 + r ^ 6)
/-- `Γ^p_{rx} Γ^x_{pp}`, reduced to the common denominator. -/
theorem Rrp_t18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_rx * Gx_pp) (⟨Rrp_n18, Rrp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rx, Gx_pp, Rrp_n18, Rrp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^v_{rp} Γ^p_{pv}` over the common denominator. -/
def Rrp_n19 : ZExp 5 := a ^ 3 * r * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q
    ^ 2 * r)
/-- `Γ^v_{rp} Γ^p_{pv}`, reduced to the common denominator. -/
theorem Rrp_t19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_rp * Gp_vp) (⟨Rrp_n19, Rrp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vp, Gv_rp, Rrp_n19, Rrp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^r_{rp} Γ^p_{pr}` over the common denominator. -/
def Rrp_n20 : ZExp 5 := -a * r * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (-a ^ 2 * m * x ^ 2
    + a ^ 2 * r * x ^ 2 + m * r ^ 2 - q ^ 2 * r + r ^ 3)
/-- `Γ^r_{rp} Γ^p_{pr}`, reduced to the common denominator. -/
theorem Rrp_t20 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gr_rp * Gp_rp) (⟨Rrp_n20, Rrp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rp, Gr_rp, Rrp_n20, Rrp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^x_{rp} Γ^p_{px}` over the common denominator. -/
def Rrp_n21 : ZExp 5 := a * x ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 4 * x ^ 4 - 2 * a ^ 2 * m * r *
    x ^ 2 + 2 * a ^ 2 * m * r + a ^ 2 * q ^ 2 * x ^ 2 - a ^ 2 * q ^ 2 + 2 * a ^ 2 * r ^ 2 * x ^ 2 +
    r ^ 4)
/-- `Γ^x_{rp} Γ^p_{px}`, reduced to the common denominator. -/
theorem Rrp_t21 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_rp * Gp_xp) (⟨Rrp_n21, Rrp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_xp, Gx_rp, Rrp_n21, Rrp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{rp} Γ^p_{pp}` over the common denominator. -/
def Rrp_n22 : ZExp 5 := a * r * (x - 1) * (x + 1) * (-a ^ 4 * m * x ^ 4 + a ^ 4 * m * x ^ 2 + a ^ 4
    * r * x ^ 4 + a ^ 2 * m * r ^ 2 * x ^ 2 - a ^ 2 * m * r ^ 2 - a ^ 2 * q ^ 2 * r * x ^ 2 + a ^ 2
    * q ^ 2 * r + 2 * a ^ 2 * r ^ 3 * x ^ 2 + r ^ 5)
/-- `Γ^p_{rp} Γ^p_{pp}`, reduced to the common denominator. -/
theorem Rrp_t22 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_rp * Gp_pp) (⟨Rrp_n22, Rrp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_pp, Gp_rp, Rrp_n22, Rrp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- `R_{rp}`: the signed sum of its terms is `Kf * Frac.ofZ (a * sx)`. -/
theorem ricci_rp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Rrp_n1 + Rrp_n2 + Rrp_n3 + Rrp_n4 + Rrp_n5 + Rrp_n6 + Rrp_n7 + Rrp_n8 +
          Rrp_n9 + Rrp_n10 + Rrp_n11 + Rrp_n12 + Rrp_n13 + Rrp_n14 - Rrp_n15 - Rrp_n16 - Rrp_n17 -
          Rrp_n18 - Rrp_n19 - Rrp_n20 - Rrp_n21 - Rrp_n22, Rrp_cd⟩) (Kf * Frac.ofZ (a * sx)))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Rrp_n1, Rrp_n2, Rrp_n3, Rrp_n4, Rrp_n5, Rrp_n6, Rrp_n7, Rrp_n8, Rrp_n9,
        Rrp_n10, Rrp_n11, Rrp_n12, Rrp_n13, Rrp_n14, Rrp_n15, Rrp_n16, Rrp_n17, Rrp_n18, Rrp_n19,
        Rrp_n20, Rrp_n21, Rrp_n22, Rrp_cd, Kf, Sg, sx, Pp, Dl, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0,
        δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ## The entry `R_{xx}` -/

/-- The common denominator of the terms of `R_{xx}`. -/
def Rxx_cd : ZExp 5 := (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4

/-- The numerator of `∂_r Γ^r_{xx}` over the common denominator. -/
def Rxx_n1 : ZExp 5 := (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^ 4 * x ^ 2 - 4 * a ^ 2
    * m * r * x ^ 2 + a ^ 2 * q ^ 2 * x ^ 2 + 3 * a ^ 2 * r ^ 2 * x ^ 2 - a ^ 2 * r ^ 2 - q ^ 2 * r
    ^ 2 + r ^ 4)
/-- `∂_r Γ^r_{xx}`, reduced to the common denominator. -/
theorem Rxx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.d δr Gr_xx) (⟨Rxx_n1, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_xx, Rxx_n1, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `∂_x Γ^x_{xx}` over the common denominator. -/
def Rxx_n2 : ZExp 5 := (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (3 * a ^ 2 * x ^ 4 - a ^ 2 *
    x ^ 2 + r ^ 2 * x ^ 2 + r ^ 2)
/-- `∂_x Γ^x_{xx}`, reduced to the common denominator. -/
theorem Rxx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.d δx Gx_xx) (⟨Rxx_n2, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_xx, Rxx_n2, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `∂_x Γ^v_{xv}` over the common denominator. -/
def Rxx_n3 : ZExp 5 := a ^ 2 * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) * (3 * a ^ 2 * x
    ^ 2 - r ^ 2) * (-2 * m * r + q ^ 2)
/-- `∂_x Γ^v_{xv}`, reduced to the common denominator. -/
theorem Rxx_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.d δx Gv_vx) (⟨Rxx_n3, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_vx, Rxx_n3, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `∂_x Γ^r_{xr}` over the common denominator. -/
def Rxx_n4 : ZExp 5 := -a ^ 2 * (x - 1) ^ 2 * (x + 1) ^ 2 * (a * x - r) * (a * x + r) * (a ^ 2 * x
    ^ 2 + r ^ 2) ^ 2
/-- `∂_x Γ^r_{xr}`, reduced to the common denominator. -/
theorem Rxx_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.d δx Gr_rx) (⟨Rxx_n4, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Rxx_n4, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `∂_x Γ^x_{xx}` over the common denominator. -/
def Rxx_n5 : ZExp 5 := (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (3 * a ^ 2 * x ^ 4 - a ^ 2 *
    x ^ 2 + r ^ 2 * x ^ 2 + r ^ 2)
/-- `∂_x Γ^x_{xx}`, reduced to the common denominator. -/
theorem Rxx_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.d δx Gx_xx) (⟨Rxx_n5, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_xx, Rxx_n5, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `∂_x Γ^p_{xp}` over the common denominator. -/
def Rxx_n6 : ZExp 5 := -(a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 6 * x ^ 8 + a ^ 6 * x ^ 6 - 6 * a ^ 4 * m *
    r * x ^ 6 + 12 * a ^ 4 * m * r * x ^ 4 - 6 * a ^ 4 * m * r * x ^ 2 + 3 * a ^ 4 * q ^ 2 * x ^ 6
    - 6 * a ^ 4 * q ^ 2 * x ^ 4 + 3 * a ^ 4 * q ^ 2 * x ^ 2 + 3 * a ^ 4 * r ^ 2 * x ^ 6 + 3 * a ^ 4
    * r ^ 2 * x ^ 4 + 2 * a ^ 2 * m * r ^ 3 * x ^ 4 - 4 * a ^ 2 * m * r ^ 3 * x ^ 2 + 2 * a ^ 2 * m
    * r ^ 3 - a ^ 2 * q ^ 2 * r ^ 2 * x ^ 4 + 2 * a ^ 2 * q ^ 2 * r ^ 2 * x ^ 2 - a ^ 2 * q ^ 2 * r
    ^ 2 + 3 * a ^ 2 * r ^ 4 * x ^ 4 + 3 * a ^ 2 * r ^ 4 * x ^ 2 + r ^ 6 * x ^ 2 + r ^ 6)
/-- `∂_x Γ^p_{xp}`, reduced to the common denominator. -/
theorem Rxx_t6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.d δx Gp_xp) (⟨Rxx_n6, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_xp, Rxx_n6, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `Γ^v_{xx} Γ^v_{vv}` over the common denominator. -/
def Rxx_n7 : ZExp 5 := -r * (a ^ 2 + r ^ 2) ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * m * x ^ 2 - m * r ^
    2 + q ^ 2 * r)
/-- `Γ^v_{xx} Γ^v_{vv}`, reduced to the common denominator. -/
theorem Rxx_t7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_xx * Gv_vv) (⟨Rxx_n7, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_vv, Gv_xx, Rxx_n7, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^v_{xx} Γ^r_{vr}` over the common denominator. -/
def Rxx_n8 : ZExp 5 := r * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 *
    m * x ^ 2 - m * r ^ 2 + q ^ 2 * r)
/-- `Γ^v_{xx} Γ^r_{vr}`, reduced to the common denominator. -/
theorem Rxx_t8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_xx * Gr_vr) (⟨Rxx_n8, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_vr, Gv_xx, Rxx_n8, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^v_{xx} Γ^p_{vp}` over the common denominator. -/
def Rxx_n9 : ZExp 5 := -a ^ 2 * r * (a ^ 2 + r ^ 2) * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * m * x ^
    2 - m * r ^ 2 + q ^ 2 * r)
/-- `Γ^v_{xx} Γ^p_{vp}`, reduced to the common denominator. -/
theorem Rxx_t9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_xx * Gp_vp) (⟨Rxx_n9, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vp, Gv_xx, Rxx_n9, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^r_{xx} Γ^x_{rx}` over the common denominator. -/
def Rxx_n10 : ZExp 5 := r ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^ 2 - 2 * m *
    r + q ^ 2 + r ^ 2)
/-- `Γ^r_{xx} Γ^x_{rx}`, reduced to the common denominator. -/
theorem Rxx_t10 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gr_xx * Gx_rx) (⟨Rxx_n10, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_xx, Gx_rx, Rxx_n10, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^r_{xx} Γ^p_{rp}` over the common denominator. -/
def Rxx_n11 : ZExp 5 := r ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^ 2 - 2 * m *
    r + q ^ 2 + r ^ 2)
/-- `Γ^r_{xx} Γ^p_{rp}`, reduced to the common denominator. -/
theorem Rxx_t11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gr_xx * Gp_rp) (⟨Rxx_n11, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rp, Gr_xx, Rxx_n11, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^x_{xx} Γ^v_{xv}` over the common denominator. -/
def Rxx_n12 : ZExp 5 := a ^ 2 * x ^ 2 * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^
    2) * (-2 * m * r + q ^ 2)
/-- `Γ^x_{xx} Γ^v_{xv}`, reduced to the common denominator. -/
theorem Rxx_t12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_xx * Gv_vx) (⟨Rxx_n12, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_vx, Gx_xx, Rxx_n12, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^x_{xx} Γ^r_{xr}` over the common denominator. -/
def Rxx_n13 : ZExp 5 := -a ^ 2 * x ^ 2 * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^
    2) ^ 2
/-- `Γ^x_{xx} Γ^r_{xr}`, reduced to the common denominator. -/
theorem Rxx_t13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_xx * Gr_rx) (⟨Rxx_n13, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Gx_xx, Rxx_n13, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^x_{xx} Γ^x_{xx}` over the common denominator. -/
def Rxx_n14 : ZExp 5 := x ^ 2 * (a ^ 2 + r ^ 2) ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `Γ^x_{xx} Γ^x_{xx}`, reduced to the common denominator. -/
theorem Rxx_t14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_xx * Gx_xx) (⟨Rxx_n14, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_xx, Rxx_n14, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `Γ^x_{xx} Γ^p_{xp}` over the common denominator. -/
def Rxx_n15 : ZExp 5 := -x ^ 2 * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 4 * x ^ 4 - 2 * a
    ^ 2 * m * r * x ^ 2 + 2 * a ^ 2 * m * r + a ^ 2 * q ^ 2 * x ^ 2 - a ^ 2 * q ^ 2 + 2 * a ^ 2 * r
    ^ 2 * x ^ 2 + r ^ 4)
/-- `Γ^x_{xx} Γ^p_{xp}`, reduced to the common denominator. -/
theorem Rxx_t15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_xx * Gp_xp) (⟨Rxx_n15, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_xp, Gx_xx, Rxx_n15, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{xx} Γ^v_{pv}` over the common denominator. -/
def Rxx_n16 : ZExp 5 := -a ^ 2 * r * (a ^ 2 + r ^ 2) * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * m * x ^
    2 - m * r ^ 2 + q ^ 2 * r)
/-- `Γ^p_{xx} Γ^v_{pv}`, reduced to the common denominator. -/
theorem Rxx_t16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_xx * Gv_vp) (⟨Rxx_n16, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_xx, Gv_vp, Rxx_n16, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{xx} Γ^r_{pr}` over the common denominator. -/
def Rxx_n17 : ZExp 5 := -a ^ 2 * r * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) * (-a ^ 2
    * m * x ^ 2 + a ^ 2 * r * x ^ 2 + m * r ^ 2 - q ^ 2 * r + r ^ 3)
/-- `Γ^p_{xx} Γ^r_{pr}`, reduced to the common denominator. -/
theorem Rxx_t17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_xx * Gr_rp) (⟨Rxx_n17, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_xx, Gr_rp, Rxx_n17, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{xx} Γ^p_{pp}` over the common denominator. -/
def Rxx_n18 : ZExp 5 := a ^ 2 * r * (x - 1) ^ 2 * (x + 1) ^ 2 * (-a ^ 4 * m * x ^ 4 + a ^ 4 * m * x
    ^ 2 + a ^ 4 * r * x ^ 4 + a ^ 2 * m * r ^ 2 * x ^ 2 - a ^ 2 * m * r ^ 2 - a ^ 2 * q ^ 2 * r * x
    ^ 2 + a ^ 2 * q ^ 2 * r + 2 * a ^ 2 * r ^ 3 * x ^ 2 + r ^ 5)
/-- `Γ^p_{xx} Γ^p_{pp}`, reduced to the common denominator. -/
theorem Rxx_t18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_xx * Gp_pp) (⟨Rxx_n18, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_pp, Gp_xx, Rxx_n18, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^v_{xv} Γ^v_{xv}` over the common denominator. -/
def Rxx_n19 : ZExp 5 := a ^ 4 * x ^ 2 * (x - 1) ^ 2 * (x + 1) ^ 2 * (-2 * m * r + q ^ 2) ^ 2
/-- `Γ^v_{xv} Γ^v_{xv}`, reduced to the common denominator. -/
theorem Rxx_t19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_vx * Gv_vx) (⟨Rxx_n19, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_vx, Rxx_n19, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `Γ^p_{xv} Γ^v_{xp}` over the common denominator. -/
def Rxx_n20 : ZExp 5 := -a ^ 4 * x ^ 2 * (x - 1) ^ 2 * (x + 1) ^ 2 * (-2 * m * r + q ^ 2) ^ 2
/-- `Γ^p_{xv} Γ^v_{xp}`, reduced to the common denominator. -/
theorem Rxx_t20 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_vx * Gv_xp) (⟨Rxx_n20, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vx, Gv_xp, Rxx_n20, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^r_{xr} Γ^r_{xr}` over the common denominator. -/
def Rxx_n21 : ZExp 5 := a ^ 4 * x ^ 2 * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `Γ^r_{xr} Γ^r_{xr}`, reduced to the common denominator. -/
theorem Rxx_t21 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gr_rx * Gr_rx) (⟨Rxx_n21, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Rxx_n21, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `Γ^x_{xr} Γ^r_{xx}` over the common denominator. -/
def Rxx_n22 : ZExp 5 := r ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^ 2 - 2 * m *
    r + q ^ 2 + r ^ 2)
/-- `Γ^x_{xr} Γ^r_{xx}`, reduced to the common denominator. -/
theorem Rxx_t22 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_rx * Gr_xx) (⟨Rxx_n22, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_xx, Gx_rx, Rxx_n22, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^r_{xx} Γ^x_{xr}` over the common denominator. -/
def Rxx_n23 : ZExp 5 := r ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^ 2 - 2 * m *
    r + q ^ 2 + r ^ 2)
/-- `Γ^r_{xx} Γ^x_{xr}`, reduced to the common denominator. -/
theorem Rxx_t23 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gr_xx * Gx_rx) (⟨Rxx_n23, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_xx, Gx_rx, Rxx_n23, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^x_{xx} Γ^x_{xx}` over the common denominator. -/
def Rxx_n24 : ZExp 5 := x ^ 2 * (a ^ 2 + r ^ 2) ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `Γ^x_{xx} Γ^x_{xx}`, reduced to the common denominator. -/
theorem Rxx_t24 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_xx * Gx_xx) (⟨Rxx_n24, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_xx, Rxx_n24, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `Γ^v_{xp} Γ^p_{xv}` over the common denominator. -/
def Rxx_n25 : ZExp 5 := -a ^ 4 * x ^ 2 * (x - 1) ^ 2 * (x + 1) ^ 2 * (-2 * m * r + q ^ 2) ^ 2
/-- `Γ^v_{xp} Γ^p_{xv}`, reduced to the common denominator. -/
theorem Rxx_t25 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_xp * Gp_vx) (⟨Rxx_n25, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vx, Gv_xp, Rxx_n25, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{xp} Γ^p_{xp}` over the common denominator. -/
def Rxx_n26 : ZExp 5 := x ^ 2 * (a ^ 4 * x ^ 4 - 2 * a ^ 2 * m * r * x ^ 2 + 2 * a ^ 2 * m * r + a
    ^ 2 * q ^ 2 * x ^ 2 - a ^ 2 * q ^ 2 + 2 * a ^ 2 * r ^ 2 * x ^ 2 + r ^ 4) ^ 2
/-- `Γ^p_{xp} Γ^p_{xp}`, reduced to the common denominator. -/
theorem Rxx_t26 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_xp * Gp_xp) (⟨Rxx_n26, Rxx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_xp, Rxx_n26, Rxx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- `R_{xx}`: the signed sum of its terms is `Kf * ⟨Sg, sx⟩`. -/
theorem ricci_xx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Rxx_n1 + Rxx_n2 - Rxx_n3 - Rxx_n4 - Rxx_n5 - Rxx_n6 + Rxx_n7 + Rxx_n8 +
          Rxx_n9 + Rxx_n10 + Rxx_n11 + Rxx_n12 + Rxx_n13 + Rxx_n14 + Rxx_n15 + Rxx_n16 + Rxx_n17 +
          Rxx_n18 - Rxx_n19 - Rxx_n20 - Rxx_n21 - Rxx_n22 - Rxx_n23 - Rxx_n24 - Rxx_n25 - Rxx_n26,
          Rxx_cd⟩) (Kf * ⟨Sg, sx⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Rxx_n1, Rxx_n2, Rxx_n3, Rxx_n4, Rxx_n5, Rxx_n6, Rxx_n7, Rxx_n8, Rxx_n9,
        Rxx_n10, Rxx_n11, Rxx_n12, Rxx_n13, Rxx_n14, Rxx_n15, Rxx_n16, Rxx_n17, Rxx_n18, Rxx_n19,
        Rxx_n20, Rxx_n21, Rxx_n22, Rxx_n23, Rxx_n24, Rxx_n25, Rxx_n26, Rxx_cd, Kf, Sg, sx, Pp, Dl,
        δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ## The entry `R_{xp}` -/

/-- The common denominator of the terms of `R_{xp}`. -/
def Rxp_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `Γ^v_{xp} Γ^v_{vv}` over the common denominator. -/
def Rxp_n1 : ZExp 5 := a ^ 3 * x * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (-2 * m * r + q ^ 2) * (a
    ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^ 2 * r)
/-- `Γ^v_{xp} Γ^v_{vv}`, reduced to the common denominator. -/
theorem Rxp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_xp * Gv_vv) (⟨Rxp_n1, Rxp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_vv, Gv_xp, Rxp_n1, Rxp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^v_{xp} Γ^r_{vr}` over the common denominator. -/
def Rxp_n2 : ZExp 5 := -a ^ 3 * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (-2 * m * r + q ^
    2) * (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^ 2 * r)
/-- `Γ^v_{xp} Γ^r_{vr}`, reduced to the common denominator. -/
theorem Rxp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_xp * Gr_vr) (⟨Rxp_n2, Rxp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_vr, Gv_xp, Rxp_n2, Rxp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^v_{xp} Γ^p_{vp}` over the common denominator. -/
def Rxp_n3 : ZExp 5 := a ^ 5 * x * (x - 1) ^ 2 * (x + 1) ^ 2 * (-2 * m * r + q ^ 2) * (a ^ 2 * m *
    x ^ 2 - m * r ^ 2 + q ^ 2 * r)
/-- `Γ^v_{xp} Γ^p_{vp}`, reduced to the common denominator. -/
theorem Rxp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_xp * Gp_vp) (⟨Rxp_n3, Rxp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vp, Gv_xp, Rxp_n3, Rxp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{xp} Γ^v_{pv}` over the common denominator. -/
def Rxp_n4 : ZExp 5 := -a * x * (a ^ 2 + r ^ 2) * (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^ 2 * r) * (a
    ^ 4 * x ^ 4 - 2 * a ^ 2 * m * r * x ^ 2 + 2 * a ^ 2 * m * r + a ^ 2 * q ^ 2 * x ^ 2 - a ^ 2 * q
    ^ 2 + 2 * a ^ 2 * r ^ 2 * x ^ 2 + r ^ 4)
/-- `Γ^p_{xp} Γ^v_{pv}`, reduced to the common denominator. -/
theorem Rxp_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_xp * Gv_vp) (⟨Rxp_n4, Rxp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_xp, Gv_vp, Rxp_n4, Rxp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{xp} Γ^r_{pr}` over the common denominator. -/
def Rxp_n5 : ZExp 5 := -a * x * (a ^ 2 * x ^ 2 + r ^ 2) * (-a ^ 2 * m * x ^ 2 + a ^ 2 * r * x ^ 2 +
    m * r ^ 2 - q ^ 2 * r + r ^ 3) * (a ^ 4 * x ^ 4 - 2 * a ^ 2 * m * r * x ^ 2 + 2 * a ^ 2 * m * r
    + a ^ 2 * q ^ 2 * x ^ 2 - a ^ 2 * q ^ 2 + 2 * a ^ 2 * r ^ 2 * x ^ 2 + r ^ 4)
/-- `Γ^p_{xp} Γ^r_{pr}`, reduced to the common denominator. -/
theorem Rxp_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_xp * Gr_rp) (⟨Rxp_n5, Rxp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_xp, Gr_rp, Rxp_n5, Rxp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{xp} Γ^p_{pp}` over the common denominator. -/
def Rxp_n6 : ZExp 5 := a * x * (a ^ 4 * x ^ 4 - 2 * a ^ 2 * m * r * x ^ 2 + 2 * a ^ 2 * m * r + a ^
    2 * q ^ 2 * x ^ 2 - a ^ 2 * q ^ 2 + 2 * a ^ 2 * r ^ 2 * x ^ 2 + r ^ 4) * (-a ^ 4 * m * x ^ 4 +
    a ^ 4 * m * x ^ 2 + a ^ 4 * r * x ^ 4 + a ^ 2 * m * r ^ 2 * x ^ 2 - a ^ 2 * m * r ^ 2 - a ^ 2 *
    q ^ 2 * r * x ^ 2 + a ^ 2 * q ^ 2 * r + 2 * a ^ 2 * r ^ 3 * x ^ 2 + r ^ 5)
/-- `Γ^p_{xp} Γ^p_{pp}`, reduced to the common denominator. -/
theorem Rxp_t6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_xp * Gp_pp) (⟨Rxp_n6, Rxp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_pp, Gp_xp, Rxp_n6, Rxp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^v_{xv} Γ^v_{pv}` over the common denominator. -/
def Rxp_n7 : ZExp 5 := a ^ 3 * x * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (-2 * m * r + q ^ 2) * (a
    ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^ 2 * r)
/-- `Γ^v_{xv} Γ^v_{pv}`, reduced to the common denominator. -/
theorem Rxp_t7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_vx * Gv_vp) (⟨Rxp_n7, Rxp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_vp, Gv_vx, Rxp_n7, Rxp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{xv} Γ^v_{pp}` over the common denominator. -/
def Rxp_n8 : ZExp 5 := a * x * (a ^ 2 + r ^ 2) * (-2 * m * r + q ^ 2) * (-a ^ 4 * m * x ^ 4 + a ^ 4
    * m * x ^ 2 + a ^ 4 * r * x ^ 4 + a ^ 2 * m * r ^ 2 * x ^ 2 - a ^ 2 * m * r ^ 2 - a ^ 2 * q ^ 2
    * r * x ^ 2 + a ^ 2 * q ^ 2 * r + 2 * a ^ 2 * r ^ 3 * x ^ 2 + r ^ 5)
/-- `Γ^p_{xv} Γ^v_{pp}`, reduced to the common denominator. -/
theorem Rxp_t8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_vx * Gv_pp) (⟨Rxp_n8, Rxp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vx, Gv_pp, Rxp_n8, Rxp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^v_{xr} Γ^r_{pv}` over the common denominator. -/
def Rxp_n9 : ZExp 5 := -a ^ 3 * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 * m * x ^
    2 - m * r ^ 2 + q ^ 2 * r) * (a ^ 2 - 2 * m * r + q ^ 2 + r ^ 2)
/-- `Γ^v_{xr} Γ^r_{pv}`, reduced to the common denominator. -/
theorem Rxp_t9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_rx * Gr_vp) (⟨Rxp_n9, Rxp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_vp, Gv_rx, Rxp_n9, Rxp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^r_{xr} Γ^r_{pr}` over the common denominator. -/
def Rxp_n10 : ZExp 5 := -a ^ 3 * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (-a ^ 2 * m
    * x ^ 2 + a ^ 2 * r * x ^ 2 + m * r ^ 2 - q ^ 2 * r + r ^ 3)
/-- `Γ^r_{xr} Γ^r_{pr}`, reduced to the common denominator. -/
theorem Rxp_t10 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gr_rx * Gr_rp) (⟨Rxp_n10, Rxp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rp, Gr_rx, Rxp_n10, Rxp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{xr} Γ^r_{pp}` over the common denominator. -/
def Rxp_n11 : ZExp 5 := -a * x * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 - 2 * m * r + q ^ 2 + r ^ 2) *
    (-a ^ 4 * m * x ^ 4 + a ^ 4 * m * x ^ 2 + a ^ 4 * r * x ^ 4 + a ^ 2 * m * r ^ 2 * x ^ 2 - a ^ 2
    * m * r ^ 2 - a ^ 2 * q ^ 2 * r * x ^ 2 + a ^ 2 * q ^ 2 * r + 2 * a ^ 2 * r ^ 3 * x ^ 2 + r ^ 5)
/-- `Γ^p_{xr} Γ^r_{pp}`, reduced to the common denominator. -/
theorem Rxp_t11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_rx * Gr_pp) (⟨Rxp_n11, Rxp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rx, Gr_pp, Rxp_n11, Rxp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^v_{xx} Γ^x_{pv}` over the common denominator. -/
def Rxp_n12 : ZExp 5 := -a * r * x * (a ^ 2 + r ^ 2) ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) * (-2 * m * r +
    q ^ 2)
/-- `Γ^v_{xx} Γ^x_{pv}`, reduced to the common denominator. -/
theorem Rxp_t12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_xx * Gx_vp) (⟨Rxp_n12, Rxp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_xx, Gx_vp, Rxp_n12, Rxp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^r_{xx} Γ^x_{pr}` over the common denominator. -/
def Rxp_n13 : ZExp 5 := a * r * x * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3 * (a ^ 2 - 2 * m * r + q ^ 2 + r ^
    2)
/-- `Γ^r_{xx} Γ^x_{pr}`, reduced to the common denominator. -/
theorem Rxp_t13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gr_xx * Gx_rp) (⟨Rxp_n13, Rxp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_xx, Gx_rp, Rxp_n13, Rxp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{xx} Γ^x_{pp}` over the common denominator. -/
def Rxp_n14 : ZExp 5 := -a * r * x * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 6 * x ^ 4 - 2 * a ^ 4 * m * r *
    x ^ 4 + 2 * a ^ 4 * m * r + a ^ 4 * q ^ 2 * x ^ 4 - a ^ 4 * q ^ 2 + a ^ 4 * r ^ 2 * x ^ 4 + 2 *
    a ^ 4 * r ^ 2 * x ^ 2 - 4 * a ^ 2 * m * r ^ 3 * x ^ 2 + 4 * a ^ 2 * m * r ^ 3 + 2 * a ^ 2 * q ^
    2 * r ^ 2 * x ^ 2 - 2 * a ^ 2 * q ^ 2 * r ^ 2 + 2 * a ^ 2 * r ^ 4 * x ^ 2 + a ^ 2 * r ^ 4 + r ^
    6)
/-- `Γ^p_{xx} Γ^x_{pp}`, reduced to the common denominator. -/
theorem Rxp_t14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_xx * Gx_pp) (⟨Rxp_n14, Rxp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_xx, Gx_pp, Rxp_n14, Rxp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^v_{xp} Γ^p_{pv}` over the common denominator. -/
def Rxp_n15 : ZExp 5 := a ^ 5 * x * (x - 1) ^ 2 * (x + 1) ^ 2 * (-2 * m * r + q ^ 2) * (a ^ 2 * m *
    x ^ 2 - m * r ^ 2 + q ^ 2 * r)
/-- `Γ^v_{xp} Γ^p_{pv}`, reduced to the common denominator. -/
theorem Rxp_t15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_xp * Gp_vp) (⟨Rxp_n15, Rxp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vp, Gv_xp, Rxp_n15, Rxp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{xp} Γ^p_{pp}` over the common denominator. -/
def Rxp_n16 : ZExp 5 := a * x * (a ^ 4 * x ^ 4 - 2 * a ^ 2 * m * r * x ^ 2 + 2 * a ^ 2 * m * r + a
    ^ 2 * q ^ 2 * x ^ 2 - a ^ 2 * q ^ 2 + 2 * a ^ 2 * r ^ 2 * x ^ 2 + r ^ 4) * (-a ^ 4 * m * x ^ 4
    + a ^ 4 * m * x ^ 2 + a ^ 4 * r * x ^ 4 + a ^ 2 * m * r ^ 2 * x ^ 2 - a ^ 2 * m * r ^ 2 - a ^ 2
    * q ^ 2 * r * x ^ 2 + a ^ 2 * q ^ 2 * r + 2 * a ^ 2 * r ^ 3 * x ^ 2 + r ^ 5)
/-- `Γ^p_{xp} Γ^p_{pp}`, reduced to the common denominator. -/
theorem Rxp_t16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_xp * Gp_pp) (⟨Rxp_n16, Rxp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_pp, Gp_xp, Rxp_n16, Rxp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- `R_{xp}`: the signed sum of its terms is `Frac.ofZ 0`. -/
theorem ricci_xp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Rxp_n1 + Rxp_n2 + Rxp_n3 + Rxp_n4 + Rxp_n5 + Rxp_n6 - Rxp_n7 - Rxp_n8 -
          Rxp_n9 - Rxp_n10 - Rxp_n11 - Rxp_n12 - Rxp_n13 - Rxp_n14 - Rxp_n15 - Rxp_n16, Rxp_cd⟩)
          (Frac.ofZ 0))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Rxp_n1, Rxp_n2, Rxp_n3, Rxp_n4, Rxp_n5, Rxp_n6, Rxp_n7, Rxp_n8, Rxp_n9,
        Rxp_n10, Rxp_n11, Rxp_n12, Rxp_n13, Rxp_n14, Rxp_n15, Rxp_n16, Rxp_cd, δr_0, δr_1, δr_2,
        δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ## The entry `R_{pp}` -/

/-- The common denominator of the terms of `R_{pp}`. -/
def Rpp_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 6

/-- The numerator of `∂_r Γ^r_{pp}` over the common denominator. -/
def Rpp_n1 : ZExp 5 := (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^ 8 * x ^ 6 + 2 * a ^ 6
    * m ^ 2 * x ^ 6 - 2 * a ^ 6 * m ^ 2 * x ^ 4 - 6 * a ^ 6 * m * r * x ^ 6 + 10 * a ^ 6 * m * r *
    x ^ 4 - 8 * a ^ 6 * m * r * x ^ 2 + a ^ 6 * q ^ 2 * x ^ 6 - a ^ 6 * q ^ 2 * x ^ 4 + a ^ 6 * q ^
    2 * x ^ 2 + 3 * a ^ 6 * r ^ 2 * x ^ 6 + a ^ 6 * r ^ 2 * x ^ 4 - 16 * a ^ 4 * m ^ 2 * r ^ 2 * x
    ^ 4 + 16 * a ^ 4 * m ^ 2 * r ^ 2 * x ^ 2 + 12 * a ^ 4 * m * q ^ 2 * r * x ^ 4 - 12 * a ^ 4 * m
    * q ^ 2 * r * x ^ 2 - 12 * a ^ 4 * m * r ^ 3 * x ^ 2 + 4 * a ^ 4 * m * r ^ 3 - a ^ 4 * q ^ 4 *
    x ^ 4 + a ^ 4 * q ^ 4 * x ^ 2 - 2 * a ^ 4 * q ^ 2 * r ^ 2 * x ^ 4 + 8 * a ^ 4 * q ^ 2 * r ^ 2 *
    x ^ 2 - 5 * a ^ 4 * q ^ 2 * r ^ 2 + 7 * a ^ 4 * r ^ 4 * x ^ 4 - a ^ 4 * r ^ 4 * x ^ 2 + 6 * a ^
    2 * m ^ 2 * r ^ 4 * x ^ 2 - 6 * a ^ 2 * m ^ 2 * r ^ 4 - 12 * a ^ 2 * m * q ^ 2 * r ^ 3 * x ^ 2
    + 12 * a ^ 2 * m * q ^ 2 * r ^ 3 - 6 * a ^ 2 * m * r ^ 5 * x ^ 2 + 2 * a ^ 2 * m * r ^ 5 + 5 *
    a ^ 2 * q ^ 4 * r ^ 2 * x ^ 2 - 5 * a ^ 2 * q ^ 4 * r ^ 2 + 2 * a ^ 2 * q ^ 2 * r ^ 4 * x ^ 2 -
    3 * a ^ 2 * q ^ 2 * r ^ 4 + 5 * a ^ 2 * r ^ 6 * x ^ 2 - a ^ 2 * r ^ 6 - q ^ 2 * r ^ 6 + r ^ 8)
/-- `∂_r Γ^r_{pp}`, reduced to the common denominator. -/
theorem Rpp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.d δr Gr_pp) (⟨Rpp_n1, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_pp, Rpp_n1, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `∂_x Γ^x_{pp}` over the common denominator. -/
def Rpp_n2 : ZExp 5 := -(a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^ 8 * x ^ 8 + a ^ 8 * x ^ 6 - 2 * a ^ 6 *
    m * r * x ^ 8 - 2 * a ^ 6 * m * r * x ^ 6 - 6 * a ^ 6 * m * r * x ^ 4 + 10 * a ^ 6 * m * r * x
    ^ 2 + a ^ 6 * q ^ 2 * x ^ 8 + a ^ 6 * q ^ 2 * x ^ 6 + 3 * a ^ 6 * q ^ 2 * x ^ 4 - 5 * a ^ 6 * q
    ^ 2 * x ^ 2 + a ^ 6 * r ^ 2 * x ^ 8 + 6 * a ^ 6 * r ^ 2 * x ^ 6 + a ^ 6 * r ^ 2 * x ^ 4 - 10 *
    a ^ 4 * m * r ^ 3 * x ^ 6 - 14 * a ^ 4 * m * r ^ 3 * x ^ 4 + 26 * a ^ 4 * m * r ^ 3 * x ^ 2 - 2
    * a ^ 4 * m * r ^ 3 + 5 * a ^ 4 * q ^ 2 * r ^ 2 * x ^ 6 + 7 * a ^ 4 * q ^ 2 * r ^ 2 * x ^ 4 -
    13 * a ^ 4 * q ^ 2 * r ^ 2 * x ^ 2 + a ^ 4 * q ^ 2 * r ^ 2 + 5 * a ^ 4 * r ^ 4 * x ^ 6 + 8 * a
    ^ 4 * r ^ 4 * x ^ 4 - a ^ 4 * r ^ 4 * x ^ 2 - 20 * a ^ 2 * m * r ^ 5 * x ^ 4 + 24 * a ^ 2 * m *
    r ^ 5 * x ^ 2 - 4 * a ^ 2 * m * r ^ 5 + 10 * a ^ 2 * q ^ 2 * r ^ 4 * x ^ 4 - 12 * a ^ 2 * q ^ 2
    * r ^ 4 * x ^ 2 + 2 * a ^ 2 * q ^ 2 * r ^ 4 + 7 * a ^ 2 * r ^ 6 * x ^ 4 + 2 * a ^ 2 * r ^ 6 * x
    ^ 2 - a ^ 2 * r ^ 6 + 3 * r ^ 8 * x ^ 2 - r ^ 8)
/-- `∂_x Γ^x_{pp}`, reduced to the common denominator. -/
theorem Rpp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.d δx Gx_pp) (⟨Rpp_n2, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_pp, Rpp_n2, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `Γ^v_{pp} Γ^v_{vv}` over the common denominator. -/
def Rpp_n3 : ZExp 5 := -(a ^ 2 + r ^ 2) ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * m * x ^ 2 - m * r ^ 2 +
    q ^ 2 * r) * (-a ^ 4 * m * x ^ 4 + a ^ 4 * m * x ^ 2 + a ^ 4 * r * x ^ 4 + a ^ 2 * m * r ^ 2 *
    x ^ 2 - a ^ 2 * m * r ^ 2 - a ^ 2 * q ^ 2 * r * x ^ 2 + a ^ 2 * q ^ 2 * r + 2 * a ^ 2 * r ^ 3 *
    x ^ 2 + r ^ 5)
/-- `Γ^v_{pp} Γ^v_{vv}`, reduced to the common denominator. -/
theorem Rpp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_pp * Gv_vv) (⟨Rpp_n3, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_pp, Gv_vv, Rpp_n3, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^v_{pp} Γ^r_{vr}` over the common denominator. -/
def Rpp_n4 : ZExp 5 := (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 * m *
    x ^ 2 - m * r ^ 2 + q ^ 2 * r) * (-a ^ 4 * m * x ^ 4 + a ^ 4 * m * x ^ 2 + a ^ 4 * r * x ^ 4 +
    a ^ 2 * m * r ^ 2 * x ^ 2 - a ^ 2 * m * r ^ 2 - a ^ 2 * q ^ 2 * r * x ^ 2 + a ^ 2 * q ^ 2 * r +
    2 * a ^ 2 * r ^ 3 * x ^ 2 + r ^ 5)
/-- `Γ^v_{pp} Γ^r_{vr}`, reduced to the common denominator. -/
theorem Rpp_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_pp * Gr_vr) (⟨Rpp_n4, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_vr, Gv_pp, Rpp_n4, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^v_{pp} Γ^p_{vp}` over the common denominator. -/
def Rpp_n5 : ZExp 5 := -a ^ 2 * (a ^ 2 + r ^ 2) * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * m * x ^ 2 -
    m * r ^ 2 + q ^ 2 * r) * (-a ^ 4 * m * x ^ 4 + a ^ 4 * m * x ^ 2 + a ^ 4 * r * x ^ 4 + a ^ 2 *
    m * r ^ 2 * x ^ 2 - a ^ 2 * m * r ^ 2 - a ^ 2 * q ^ 2 * r * x ^ 2 + a ^ 2 * q ^ 2 * r + 2 * a ^
    2 * r ^ 3 * x ^ 2 + r ^ 5)
/-- `Γ^v_{pp} Γ^p_{vp}`, reduced to the common denominator. -/
theorem Rpp_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_pp * Gp_vp) (⟨Rpp_n5, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vp, Gv_pp, Rpp_n5, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^r_{pp} Γ^x_{rx}` over the common denominator. -/
def Rpp_n6 : ZExp 5 := r * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^ 2 - 2 * m * r + q
    ^ 2 + r ^ 2) * (-a ^ 4 * m * x ^ 4 + a ^ 4 * m * x ^ 2 + a ^ 4 * r * x ^ 4 + a ^ 2 * m * r ^ 2
    * x ^ 2 - a ^ 2 * m * r ^ 2 - a ^ 2 * q ^ 2 * r * x ^ 2 + a ^ 2 * q ^ 2 * r + 2 * a ^ 2 * r ^ 3
    * x ^ 2 + r ^ 5)
/-- `Γ^r_{pp} Γ^x_{rx}`, reduced to the common denominator. -/
theorem Rpp_t6 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gr_pp * Gx_rx) (⟨Rpp_n6, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_pp, Gx_rx, Rpp_n6, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^r_{pp} Γ^p_{rp}` over the common denominator. -/
def Rpp_n7 : ZExp 5 := r * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^ 2 - 2 * m * r + q
    ^ 2 + r ^ 2) * (-a ^ 4 * m * x ^ 4 + a ^ 4 * m * x ^ 2 + a ^ 4 * r * x ^ 4 + a ^ 2 * m * r ^ 2
    * x ^ 2 - a ^ 2 * m * r ^ 2 - a ^ 2 * q ^ 2 * r * x ^ 2 + a ^ 2 * q ^ 2 * r + 2 * a ^ 2 * r ^ 3
    * x ^ 2 + r ^ 5)
/-- `Γ^r_{pp} Γ^p_{rp}`, reduced to the common denominator. -/
theorem Rpp_t7 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gr_pp * Gp_rp) (⟨Rpp_n7, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rp, Gr_pp, Rpp_n7, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^x_{pp} Γ^v_{xv}` over the common denominator. -/
def Rpp_n8 : ZExp 5 := a ^ 2 * x ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (-2 * m * r +
    q ^ 2) * (a ^ 6 * x ^ 4 - 2 * a ^ 4 * m * r * x ^ 4 + 2 * a ^ 4 * m * r + a ^ 4 * q ^ 2 * x ^ 4
    - a ^ 4 * q ^ 2 + a ^ 4 * r ^ 2 * x ^ 4 + 2 * a ^ 4 * r ^ 2 * x ^ 2 - 4 * a ^ 2 * m * r ^ 3 * x
    ^ 2 + 4 * a ^ 2 * m * r ^ 3 + 2 * a ^ 2 * q ^ 2 * r ^ 2 * x ^ 2 - 2 * a ^ 2 * q ^ 2 * r ^ 2 + 2
    * a ^ 2 * r ^ 4 * x ^ 2 + a ^ 2 * r ^ 4 + r ^ 6)
/-- `Γ^x_{pp} Γ^v_{xv}`, reduced to the common denominator. -/
theorem Rpp_t8 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_pp * Gv_vx) (⟨Rpp_n8, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_vx, Gx_pp, Rpp_n8, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^x_{pp} Γ^r_{xr}` over the common denominator. -/
def Rpp_n9 : ZExp 5 := -a ^ 2 * x ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^ 6 *
    x ^ 4 - 2 * a ^ 4 * m * r * x ^ 4 + 2 * a ^ 4 * m * r + a ^ 4 * q ^ 2 * x ^ 4 - a ^ 4 * q ^ 2 +
    a ^ 4 * r ^ 2 * x ^ 4 + 2 * a ^ 4 * r ^ 2 * x ^ 2 - 4 * a ^ 2 * m * r ^ 3 * x ^ 2 + 4 * a ^ 2 *
    m * r ^ 3 + 2 * a ^ 2 * q ^ 2 * r ^ 2 * x ^ 2 - 2 * a ^ 2 * q ^ 2 * r ^ 2 + 2 * a ^ 2 * r ^ 4 *
    x ^ 2 + a ^ 2 * r ^ 4 + r ^ 6)
/-- `Γ^x_{pp} Γ^r_{xr}`, reduced to the common denominator. -/
theorem Rpp_t9 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_pp * Gr_rx) (⟨Rpp_n9, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, Gx_pp, Rpp_n9, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^x_{pp} Γ^x_{xx}` over the common denominator. -/
def Rpp_n10 : ZExp 5 := x ^ 2 * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^ 6 * x ^ 4 - 2
    * a ^ 4 * m * r * x ^ 4 + 2 * a ^ 4 * m * r + a ^ 4 * q ^ 2 * x ^ 4 - a ^ 4 * q ^ 2 + a ^ 4 * r
    ^ 2 * x ^ 4 + 2 * a ^ 4 * r ^ 2 * x ^ 2 - 4 * a ^ 2 * m * r ^ 3 * x ^ 2 + 4 * a ^ 2 * m * r ^ 3
    + 2 * a ^ 2 * q ^ 2 * r ^ 2 * x ^ 2 - 2 * a ^ 2 * q ^ 2 * r ^ 2 + 2 * a ^ 2 * r ^ 4 * x ^ 2 + a
    ^ 2 * r ^ 4 + r ^ 6)
/-- `Γ^x_{pp} Γ^x_{xx}`, reduced to the common denominator. -/
theorem Rpp_t10 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_pp * Gx_xx) (⟨Rpp_n10, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_pp, Gx_xx, Rpp_n10, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^x_{pp} Γ^p_{xp}` over the common denominator. -/
def Rpp_n11 : ZExp 5 := -x ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 4 * x ^ 4 - 2 * a ^ 2 * m * r * x ^
    2 + 2 * a ^ 2 * m * r + a ^ 2 * q ^ 2 * x ^ 2 - a ^ 2 * q ^ 2 + 2 * a ^ 2 * r ^ 2 * x ^ 2 + r ^
    4) * (a ^ 6 * x ^ 4 - 2 * a ^ 4 * m * r * x ^ 4 + 2 * a ^ 4 * m * r + a ^ 4 * q ^ 2 * x ^ 4 - a
    ^ 4 * q ^ 2 + a ^ 4 * r ^ 2 * x ^ 4 + 2 * a ^ 4 * r ^ 2 * x ^ 2 - 4 * a ^ 2 * m * r ^ 3 * x ^ 2
    + 4 * a ^ 2 * m * r ^ 3 + 2 * a ^ 2 * q ^ 2 * r ^ 2 * x ^ 2 - 2 * a ^ 2 * q ^ 2 * r ^ 2 + 2 * a
    ^ 2 * r ^ 4 * x ^ 2 + a ^ 2 * r ^ 4 + r ^ 6)
/-- `Γ^x_{pp} Γ^p_{xp}`, reduced to the common denominator. -/
theorem Rpp_t11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_pp * Gp_xp) (⟨Rpp_n11, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_xp, Gx_pp, Rpp_n11, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{pp} Γ^v_{pv}` over the common denominator. -/
def Rpp_n12 : ZExp 5 := -a ^ 2 * (a ^ 2 + r ^ 2) * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * m * x ^ 2 -
    m * r ^ 2 + q ^ 2 * r) * (-a ^ 4 * m * x ^ 4 + a ^ 4 * m * x ^ 2 + a ^ 4 * r * x ^ 4 + a ^ 2 *
    m * r ^ 2 * x ^ 2 - a ^ 2 * m * r ^ 2 - a ^ 2 * q ^ 2 * r * x ^ 2 + a ^ 2 * q ^ 2 * r + 2 * a ^
    2 * r ^ 3 * x ^ 2 + r ^ 5)
/-- `Γ^p_{pp} Γ^v_{pv}`, reduced to the common denominator. -/
theorem Rpp_t12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_pp * Gv_vp) (⟨Rpp_n12, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_pp, Gv_vp, Rpp_n12, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{pp} Γ^r_{pr}` over the common denominator. -/
def Rpp_n13 : ZExp 5 := -a ^ 2 * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) * (-a ^ 2 * m
    * x ^ 2 + a ^ 2 * r * x ^ 2 + m * r ^ 2 - q ^ 2 * r + r ^ 3) * (-a ^ 4 * m * x ^ 4 + a ^ 4 * m
    * x ^ 2 + a ^ 4 * r * x ^ 4 + a ^ 2 * m * r ^ 2 * x ^ 2 - a ^ 2 * m * r ^ 2 - a ^ 2 * q ^ 2 * r
    * x ^ 2 + a ^ 2 * q ^ 2 * r + 2 * a ^ 2 * r ^ 3 * x ^ 2 + r ^ 5)
/-- `Γ^p_{pp} Γ^r_{pr}`, reduced to the common denominator. -/
theorem Rpp_t13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_pp * Gr_rp) (⟨Rpp_n13, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_pp, Gr_rp, Rpp_n13, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{pp} Γ^p_{pp}` over the common denominator. -/
def Rpp_n14 : ZExp 5 := a ^ 2 * (x - 1) ^ 2 * (x + 1) ^ 2 * (-a ^ 4 * m * x ^ 4 + a ^ 4 * m * x ^ 2
    + a ^ 4 * r * x ^ 4 + a ^ 2 * m * r ^ 2 * x ^ 2 - a ^ 2 * m * r ^ 2 - a ^ 2 * q ^ 2 * r * x ^ 2
    + a ^ 2 * q ^ 2 * r + 2 * a ^ 2 * r ^ 3 * x ^ 2 + r ^ 5) ^ 2
/-- `Γ^p_{pp} Γ^p_{pp}`, reduced to the common denominator. -/
theorem Rpp_t14 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_pp * Gp_pp) (⟨Rpp_n14, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_pp, Rpp_n14, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `Γ^v_{pv} Γ^v_{pv}` over the common denominator. -/
def Rpp_n15 : ZExp 5 := a ^ 2 * (a ^ 2 + r ^ 2) ^ 2 * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * m * x ^
    2 - m * r ^ 2 + q ^ 2 * r) ^ 2
/-- `Γ^v_{pv} Γ^v_{pv}`, reduced to the common denominator. -/
theorem Rpp_t15 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_vp * Gv_vp) (⟨Rpp_n15, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_vp, Rpp_n15, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `Γ^r_{pv} Γ^v_{pr}` over the common denominator. -/
def Rpp_n16 : ZExp 5 := a ^ 2 * r * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^
    2 * m * x ^ 2 - m * r ^ 2 + q ^ 2 * r) * (a ^ 2 - 2 * m * r + q ^ 2 + r ^ 2)
/-- `Γ^r_{pv} Γ^v_{pr}`, reduced to the common denominator. -/
theorem Rpp_t16 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gr_vp * Gv_rp) (⟨Rpp_n16, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_vp, Gv_rp, Rpp_n16, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^x_{pv} Γ^v_{px}` over the common denominator. -/
def Rpp_n17 : ZExp 5 := a ^ 4 * x ^ 2 * (a ^ 2 + r ^ 2) * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * x ^
    2 + r ^ 2) * (-2 * m * r + q ^ 2) ^ 2
/-- `Γ^x_{pv} Γ^v_{px}`, reduced to the common denominator. -/
theorem Rpp_t17 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_vp * Gv_xp) (⟨Rpp_n17, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_xp, Gx_vp, Rpp_n17, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{pv} Γ^v_{pp}` over the common denominator. -/
def Rpp_n18 : ZExp 5 := -a ^ 2 * (a ^ 2 + r ^ 2) * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * m * x ^ 2 -
    m * r ^ 2 + q ^ 2 * r) * (-a ^ 4 * m * x ^ 4 + a ^ 4 * m * x ^ 2 + a ^ 4 * r * x ^ 4 + a ^ 2 *
    m * r ^ 2 * x ^ 2 - a ^ 2 * m * r ^ 2 - a ^ 2 * q ^ 2 * r * x ^ 2 + a ^ 2 * q ^ 2 * r + 2 * a ^
    2 * r ^ 3 * x ^ 2 + r ^ 5)
/-- `Γ^p_{pv} Γ^v_{pp}`, reduced to the common denominator. -/
theorem Rpp_t18 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_vp * Gv_pp) (⟨Rpp_n18, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vp, Gv_pp, Rpp_n18, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^v_{pr} Γ^r_{pv}` over the common denominator. -/
def Rpp_n19 : ZExp 5 := a ^ 2 * r * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^
    2 * m * x ^ 2 - m * r ^ 2 + q ^ 2 * r) * (a ^ 2 - 2 * m * r + q ^ 2 + r ^ 2)
/-- `Γ^v_{pr} Γ^r_{pv}`, reduced to the common denominator. -/
theorem Rpp_t19 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_rp * Gr_vp) (⟨Rpp_n19, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_vp, Gv_rp, Rpp_n19, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^r_{pr} Γ^r_{pr}` over the common denominator. -/
def Rpp_n20 : ZExp 5 := a ^ 2 * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (-a ^ 2 *
    m * x ^ 2 + a ^ 2 * r * x ^ 2 + m * r ^ 2 - q ^ 2 * r + r ^ 3) ^ 2
/-- `Γ^r_{pr} Γ^r_{pr}`, reduced to the common denominator. -/
theorem Rpp_t20 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gr_rp * Gr_rp) (⟨Rpp_n20, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rp, Rpp_n20, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- The numerator of `Γ^p_{pr} Γ^r_{pp}` over the common denominator. -/
def Rpp_n21 : ZExp 5 := r * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^ 2 - 2 * m * r +
    q ^ 2 + r ^ 2) * (-a ^ 4 * m * x ^ 4 + a ^ 4 * m * x ^ 2 + a ^ 4 * r * x ^ 4 + a ^ 2 * m * r ^
    2 * x ^ 2 - a ^ 2 * m * r ^ 2 - a ^ 2 * q ^ 2 * r * x ^ 2 + a ^ 2 * q ^ 2 * r + 2 * a ^ 2 * r ^
    3 * x ^ 2 + r ^ 5)
/-- `Γ^p_{pr} Γ^r_{pp}`, reduced to the common denominator. -/
theorem Rpp_t21 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_rp * Gr_pp) (⟨Rpp_n21, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rp, Gr_pp, Rpp_n21, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^v_{px} Γ^x_{pv}` over the common denominator. -/
def Rpp_n22 : ZExp 5 := a ^ 4 * x ^ 2 * (a ^ 2 + r ^ 2) * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * x ^
    2 + r ^ 2) * (-2 * m * r + q ^ 2) ^ 2
/-- `Γ^v_{px} Γ^x_{pv}`, reduced to the common denominator. -/
theorem Rpp_t22 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_xp * Gx_vp) (⟨Rpp_n22, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_xp, Gx_vp, Rpp_n22, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{px} Γ^x_{pp}` over the common denominator. -/
def Rpp_n23 : ZExp 5 := -x ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 4 * x ^ 4 - 2 * a ^ 2 * m * r * x ^
    2 + 2 * a ^ 2 * m * r + a ^ 2 * q ^ 2 * x ^ 2 - a ^ 2 * q ^ 2 + 2 * a ^ 2 * r ^ 2 * x ^ 2 + r ^
    4) * (a ^ 6 * x ^ 4 - 2 * a ^ 4 * m * r * x ^ 4 + 2 * a ^ 4 * m * r + a ^ 4 * q ^ 2 * x ^ 4 - a
    ^ 4 * q ^ 2 + a ^ 4 * r ^ 2 * x ^ 4 + 2 * a ^ 4 * r ^ 2 * x ^ 2 - 4 * a ^ 2 * m * r ^ 3 * x ^ 2
    + 4 * a ^ 2 * m * r ^ 3 + 2 * a ^ 2 * q ^ 2 * r ^ 2 * x ^ 2 - 2 * a ^ 2 * q ^ 2 * r ^ 2 + 2 * a
    ^ 2 * r ^ 4 * x ^ 2 + a ^ 2 * r ^ 4 + r ^ 6)
/-- `Γ^p_{px} Γ^x_{pp}`, reduced to the common denominator. -/
theorem Rpp_t23 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_xp * Gx_pp) (⟨Rpp_n23, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_xp, Gx_pp, Rpp_n23, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^v_{pp} Γ^p_{pv}` over the common denominator. -/
def Rpp_n24 : ZExp 5 := -a ^ 2 * (a ^ 2 + r ^ 2) * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * m * x ^ 2 -
    m * r ^ 2 + q ^ 2 * r) * (-a ^ 4 * m * x ^ 4 + a ^ 4 * m * x ^ 2 + a ^ 4 * r * x ^ 4 + a ^ 2 *
    m * r ^ 2 * x ^ 2 - a ^ 2 * m * r ^ 2 - a ^ 2 * q ^ 2 * r * x ^ 2 + a ^ 2 * q ^ 2 * r + 2 * a ^
    2 * r ^ 3 * x ^ 2 + r ^ 5)
/-- `Γ^v_{pp} Γ^p_{pv}`, reduced to the common denominator. -/
theorem Rpp_t24 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gv_pp * Gp_vp) (⟨Rpp_n24, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vp, Gv_pp, Rpp_n24, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^r_{pp} Γ^p_{pr}` over the common denominator. -/
def Rpp_n25 : ZExp 5 := r * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^ 2 - 2 * m * r +
    q ^ 2 + r ^ 2) * (-a ^ 4 * m * x ^ 4 + a ^ 4 * m * x ^ 2 + a ^ 4 * r * x ^ 4 + a ^ 2 * m * r ^
    2 * x ^ 2 - a ^ 2 * m * r ^ 2 - a ^ 2 * q ^ 2 * r * x ^ 2 + a ^ 2 * q ^ 2 * r + 2 * a ^ 2 * r ^
    3 * x ^ 2 + r ^ 5)
/-- `Γ^r_{pp} Γ^p_{pr}`, reduced to the common denominator. -/
theorem Rpp_t25 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gr_pp * Gp_rp) (⟨Rpp_n25, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rp, Gr_pp, Rpp_n25, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^x_{pp} Γ^p_{px}` over the common denominator. -/
def Rpp_n26 : ZExp 5 := -x ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 4 * x ^ 4 - 2 * a ^ 2 * m * r * x ^
    2 + 2 * a ^ 2 * m * r + a ^ 2 * q ^ 2 * x ^ 2 - a ^ 2 * q ^ 2 + 2 * a ^ 2 * r ^ 2 * x ^ 2 + r ^
    4) * (a ^ 6 * x ^ 4 - 2 * a ^ 4 * m * r * x ^ 4 + 2 * a ^ 4 * m * r + a ^ 4 * q ^ 2 * x ^ 4 - a
    ^ 4 * q ^ 2 + a ^ 4 * r ^ 2 * x ^ 4 + 2 * a ^ 4 * r ^ 2 * x ^ 2 - 4 * a ^ 2 * m * r ^ 3 * x ^ 2
    + 4 * a ^ 2 * m * r ^ 3 + 2 * a ^ 2 * q ^ 2 * r ^ 2 * x ^ 2 - 2 * a ^ 2 * q ^ 2 * r ^ 2 + 2 * a
    ^ 2 * r ^ 4 * x ^ 2 + a ^ 2 * r ^ 4 + r ^ 6)
/-- `Γ^x_{pp} Γ^p_{px}`, reduced to the common denominator. -/
theorem Rpp_t26 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gx_pp * Gp_xp) (⟨Rpp_n26, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_xp, Gx_pp, Rpp_n26, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-- The numerator of `Γ^p_{pp} Γ^p_{pp}` over the common denominator. -/
def Rpp_n27 : ZExp 5 := a ^ 2 * (x - 1) ^ 2 * (x + 1) ^ 2 * (-a ^ 4 * m * x ^ 4 + a ^ 4 * m * x ^ 2
    + a ^ 4 * r * x ^ 4 + a ^ 2 * m * r ^ 2 * x ^ 2 - a ^ 2 * m * r ^ 2 - a ^ 2 * q ^ 2 * r * x ^ 2
    + a ^ 2 * q ^ 2 * r + 2 * a ^ 2 * r ^ 3 * x ^ 2 + r ^ 5) ^ 2
/-- `Γ^p_{pp} Γ^p_{pp}`, reduced to the common denominator. -/
theorem Rpp_t27 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Gp_pp * Gp_pp) (⟨Rpp_n27, Rpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_pp, Rpp_n27, Rpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- `R_{pp}`: the signed sum of its terms is `Kf * ⟨sx * (Dl * a ^ 2 * sx + Pp ^ 2), Sg⟩`. -/
theorem ricci_pp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Rpp_n1 + Rpp_n2 + Rpp_n3 + Rpp_n4 + Rpp_n5 + Rpp_n6 + Rpp_n7 + Rpp_n8 +
          Rpp_n9 + Rpp_n10 + Rpp_n11 + Rpp_n12 + Rpp_n13 + Rpp_n14 - Rpp_n15 - Rpp_n16 - Rpp_n17 -
          Rpp_n18 - Rpp_n19 - Rpp_n20 - Rpp_n21 - Rpp_n22 - Rpp_n23 - Rpp_n24 - Rpp_n25 - Rpp_n26 -
          Rpp_n27, Rpp_cd⟩) (Kf * ⟨sx * (Dl * a ^ 2 * sx + Pp ^ 2), Sg⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Rpp_n1, Rpp_n2, Rpp_n3, Rpp_n4, Rpp_n5, Rpp_n6, Rpp_n7, Rpp_n8, Rpp_n9,
        Rpp_n10, Rpp_n11, Rpp_n12, Rpp_n13, Rpp_n14, Rpp_n15, Rpp_n16, Rpp_n17, Rpp_n18, Rpp_n19,
        Rpp_n20, Rpp_n21, Rpp_n22, Rpp_n23, Rpp_n24, Rpp_n25, Rpp_n26, Rpp_n27, Rpp_cd, Kf, Sg, sx,
        Pp, Dl, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

end LeanProofs.IPRA.Geometry.KerrNewmanIngoingRicci
