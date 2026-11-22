import IPRADerivations.Geometry.KerrNewmanConnection

/-!
# The derivatives of the connection coefficients of the radial-function metric

Packet: `geometry/four_metrics_ipra_2026-11-15`, the first stage of the supplementary certificate
for `eq:Kretschmann` ("A supplementary exact certificate computes the full Riemann tensor from
`eq:Riemann`"). For each nonzero connection coefficient `Γ^λ_{μν}` of
`Geometry/KerrNewmanConnection` (Boyer–Lindquist coordinates, index `p` for `φ`, radial function
`d` with `∂_r d = v`, `∂_r v = w`) and each direction `r`, `x` with a nonzero derivative,
`deriv_c_λ_μν` certifies the formal derivative `Frac.d δc Gλ_μν` (`Foundations/FormalDerivation`)
as the reduced fraction `dc_Gλ_μν`.

Reducing the derivatives once keeps the cleared identities of the Riemann tensor
(`Geometry/KerrNewmanRiemannT`, `…R`, `…X`, `…P`) small: the quotient rule squares the denominator,
and clearing that square against a common denominator of the Riemann terms is what makes a direct
certificate expensive.

The reduced fractions were proposed by a computer algebra script; every identity is checked by
Lean as an identity of fractions cleared of denominators, a closed sentence of iPRA certified in
every commutative ring.
-/

namespace LeanProofs.IPRA.Geometry.KerrNewmanConnectionDerivatives

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Geometry.KerrNewmanBase (δr δx δr_0 δr_1 δr_2 δr_3 δr_4 δr_5 δx_0 δx_1 δx_2
  δx_3 δx_4 δx_5 Sg sx)
open LeanProofs.IPRA.Geometry.KerrNewmanConnection
open ZExp

local notation "r" => (ZExp.var 0 : ZExp 6)
local notation "x" => (ZExp.var 1 : ZExp 6)
local notation "a" => (ZExp.var 2 : ZExp 6)
local notation "d" => (ZExp.var 3 : ZExp 6)
local notation "v" => (ZExp.var 4 : ZExp 6)
local notation "w" => (ZExp.var 5 : ZExp 6)

/-! ## The derivatives of the connection coefficients -/

/-- `∂_r Γ^p_{rp}`, reduced. -/
def dr_Gp_rp : Frac 6 := ⟨a ^ 6 * d * w * x ^ 6 - a ^ 6 * d * w * x ^ 4 + 2 * a ^ 6 * d * x ^ 4 - 2
    * a ^ 6 * d * x ^ 2 - 2 * a ^ 6 * r * v * x ^ 4 + 2 * a ^ 6 * r * v * x ^ 2 - a ^ 6 * v ^ 2 * x
    ^ 6 + a ^ 6 * v ^ 2 * x ^ 4 + 2 * a ^ 4 * d ^ 2 * x ^ 2 + 2 * a ^ 4 * d * r ^ 2 * w * x ^ 4 - 2
    * a ^ 4 * d * r ^ 2 * w * x ^ 2 + 6 * a ^ 4 * d * r ^ 2 * x ^ 4 - 12 * a ^ 4 * d * r ^ 2 * x ^
    2 + 6 * a ^ 4 * d * r ^ 2 - 2 * a ^ 4 * d * r * v * x ^ 4 + 2 * a ^ 4 * d * r * v * x ^ 2 - 2 *
    a ^ 4 * r ^ 3 * v * x ^ 4 + 2 * a ^ 4 * r ^ 3 * v - 2 * a ^ 4 * r ^ 2 * v ^ 2 * x ^ 4 + 2 * a ^
    4 * r ^ 2 * v ^ 2 * x ^ 2 + 6 * a ^ 2 * d ^ 2 * r ^ 2 * x ^ 2 - 6 * a ^ 2 * d ^ 2 * r ^ 2 + a ^
    2 * d * r ^ 4 * w * x ^ 2 - a ^ 2 * d * r ^ 4 * w - 2 * a ^ 2 * d * r ^ 4 * x ^ 2 + 2 * a ^ 2 *
    d * r ^ 4 - 2 * a ^ 2 * d * r ^ 3 * v * x ^ 2 + 2 * a ^ 2 * d * r ^ 3 * v - 2 * a ^ 2 * r ^ 5 *
    v * x ^ 2 + 2 * a ^ 2 * r ^ 5 * v - a ^ 2 * r ^ 4 * v ^ 2 * x ^ 2 + a ^ 2 * r ^ 4 * v ^ 2 - 2 *
    d ^ 2 * r ^ 4, 2 * d ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- `∂_r Γ^p_{rp}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_r_p_rp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δr Gp_rp) (dr_Gp_rp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rp, dr_Gp_rp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_x Γ^p_{rp}`, reduced. -/
def dx_Gp_rp : Frac 6 := ⟨-a ^ 2 * x * (a ^ 2 + r ^ 2) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a
    ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v), d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- `∂_x Γ^p_{rp}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_x_p_rp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx Gp_rp) (dx_Gp_rp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rp, dx_Gp_rp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_r Γ^p_{tr}`, reduced. -/
def dr_Gp_tr : Frac 6 := ⟨a * (a ^ 4 * d * w * x ^ 4 - 2 * a ^ 4 * d * x ^ 4 + 2 * a ^ 4 * d * x ^
    2 + 2 * a ^ 4 * r * v * x ^ 4 - 2 * a ^ 4 * r * v * x ^ 2 - a ^ 4 * v ^ 2 * x ^ 4 - 2 * a ^ 2 *
    d ^ 2 * x ^ 2 + 2 * a ^ 2 * d * r ^ 2 * w * x ^ 2 + 6 * a ^ 2 * d * r ^ 2 * x ^ 2 - 6 * a ^ 2 *
    d * r ^ 2 - 2 * a ^ 2 * d * r * v * x ^ 2 + 2 * a ^ 2 * r ^ 3 * v * x ^ 2 - 2 * a ^ 2 * r ^ 3 *
    v - 2 * a ^ 2 * r ^ 2 * v ^ 2 * x ^ 2 + 6 * d ^ 2 * r ^ 2 + d * r ^ 4 * w - 2 * d * r ^ 3 * v -
    r ^ 4 * v ^ 2), 2 * d ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- `∂_r Γ^p_{tr}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_r_p_tr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δr Gp_tr) (dr_Gp_tr))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_tr, dr_Gp_tr, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_x Γ^p_{tr}`, reduced. -/
def dx_Gp_tr : Frac 6 := ⟨a ^ 3 * x * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 +
    4 * d * r - 2 * r ^ 3 - r ^ 2 * v), d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- `∂_x Γ^p_{tr}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_x_p_tr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx Gp_tr) (dx_Gp_tr))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_tr, dx_Gp_tr, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_r Γ^p_{tx}`, reduced. -/
def dr_Gp_tx : Frac 6 := ⟨-a * x * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 + 4 *
    d * r - 2 * r ^ 3 - r ^ 2 * v), (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- `∂_r Γ^p_{tx}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_r_p_tx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δr Gp_tx) (dr_Gp_tx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_tx, dr_Gp_tx, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_x Γ^p_{tx}`, reduced. -/
def dx_Gp_tx : Frac 6 := ⟨a * (a ^ 2 - d + r ^ 2) * (5 * a ^ 2 * x ^ 4 - 3 * a ^ 2 * x ^ 2 + r ^ 2
    * x ^ 2 + r ^ 2), (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- `∂_x Γ^p_{tx}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_x_p_tx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx Gp_tx) (dx_Gp_tx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_tx, dx_Gp_tx, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_r Γ^p_{xp}`, reduced. -/
def dr_Gp_xp : Frac 6 := ⟨-a ^ 2 * x * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 +
    4 * d * r - 2 * r ^ 3 - r ^ 2 * v), (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- `∂_r Γ^p_{xp}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_r_p_xp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δr Gp_xp) (dr_Gp_xp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_xp, dr_Gp_xp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_x Γ^p_{xp}`, reduced. -/
def dx_Gp_xp : Frac 6 := ⟨-a ^ 6 * x ^ 8 + 2 * a ^ 6 * x ^ 6 - 6 * a ^ 6 * x ^ 4 + 3 * a ^ 6 * x ^
    2 - 3 * a ^ 4 * d * x ^ 6 + 6 * a ^ 4 * d * x ^ 4 - 3 * a ^ 4 * d * x ^ 2 - 10 * a ^ 4 * r ^ 2
    * x ^ 4 + 5 * a ^ 4 * r ^ 2 * x ^ 2 - a ^ 4 * r ^ 2 + a ^ 2 * d * r ^ 2 * x ^ 4 - 2 * a ^ 2 * d
    * r ^ 2 * x ^ 2 + a ^ 2 * d * r ^ 2 - 4 * a ^ 2 * r ^ 4 * x ^ 4 - a ^ 2 * r ^ 4 * x ^ 2 - a ^ 2
    * r ^ 4 - r ^ 6 * x ^ 2 - r ^ 6, (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- `∂_x Γ^p_{xp}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_x_p_xp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx Gp_xp) (dx_Gp_xp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_xp, dx_Gp_xp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_r Γ^r_{pp}`, reduced. -/
def dr_Gr_pp : Frac 6 := ⟨(x - 1) * (x + 1) * (a ^ 6 * d * w * x ^ 6 - a ^ 6 * d * w * x ^ 4 + 4 *
    a ^ 6 * d * x ^ 4 - 2 * a ^ 6 * d * x ^ 2 + 4 * a ^ 6 * r * v * x ^ 4 - 2 * a ^ 6 * r * v * x ^
    2 + a ^ 6 * v ^ 2 * x ^ 6 - a ^ 6 * v ^ 2 * x ^ 4 - 2 * a ^ 4 * d ^ 2 * x ^ 4 + 2 * a ^ 4 * d ^
    2 * x ^ 2 + 2 * a ^ 4 * d * r ^ 2 * w * x ^ 4 - 2 * a ^ 4 * d * r ^ 2 * w * x ^ 2 + 12 * a ^ 4
    * d * r ^ 2 * x ^ 4 - 20 * a ^ 4 * d * r ^ 2 * x ^ 2 + 10 * a ^ 4 * d * r ^ 2 - 8 * a ^ 4 * d *
    r * v * x ^ 4 + 8 * a ^ 4 * d * r * v * x ^ 2 + 4 * a ^ 4 * r ^ 3 * v * x ^ 4 + 4 * a ^ 4 * r ^
    3 * v * x ^ 2 - 2 * a ^ 4 * r ^ 3 * v + 2 * a ^ 4 * r ^ 2 * v ^ 2 * x ^ 4 - 2 * a ^ 4 * r ^ 2 *
    v ^ 2 * x ^ 2 + 10 * a ^ 2 * d ^ 2 * r ^ 2 * x ^ 2 - 10 * a ^ 2 * d ^ 2 * r ^ 2 + a ^ 2 * d * r
    ^ 4 * w * x ^ 2 - a ^ 2 * d * r ^ 4 * w - 2 * a ^ 2 * d * r ^ 4 * x ^ 2 - 8 * a ^ 2 * d * r ^ 3
    * v * x ^ 2 + 8 * a ^ 2 * d * r ^ 3 * v + 6 * a ^ 2 * r ^ 5 * v * x ^ 2 + a ^ 2 * r ^ 4 * v ^ 2
    * x ^ 2 - a ^ 2 * r ^ 4 * v ^ 2 - 2 * d * r ^ 6 + 2 * r ^ 7 * v), 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^
    4⟩

/-- `∂_r Γ^r_{pp}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_r_r_pp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δr Gr_pp) (dr_Gr_pp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_pp, dr_Gr_pp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_x Γ^r_{pp}`, reduced. -/
def dx_Gr_pp : Frac 6 := ⟨-2 * d * x * (2 * a ^ 6 * r * x ^ 4 - 6 * a ^ 6 * r * x ^ 2 + 3 * a ^ 6 *
    r - a ^ 6 * v * x ^ 4 + a ^ 6 * v * x ^ 2 - a ^ 4 * d * r * x ^ 4 + 4 * a ^ 4 * d * r * x ^ 2 -
    3 * a ^ 4 * d * r + 2 * a ^ 4 * r ^ 3 * x ^ 4 - 8 * a ^ 4 * r ^ 3 * x ^ 2 + 3 * a ^ 4 * r ^ 3 -
    a ^ 4 * r ^ 2 * v * x ^ 4 + a ^ 4 * r ^ 2 * v + 2 * a ^ 2 * d * r ^ 3 * x ^ 2 - 2 * a ^ 2 * d *
    r ^ 3 - 2 * a ^ 2 * r ^ 5 * x ^ 2 - a ^ 2 * r ^ 5 - a ^ 2 * r ^ 4 * v * x ^ 2 + a ^ 2 * r ^ 4 *
    v - r ^ 7), (a ^ 2 * x ^ 2 + r ^ 2) ^ 4⟩

/-- `∂_x Γ^r_{pp}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_x_r_pp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx Gr_pp) (dx_Gr_pp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_pp, dx_Gr_pp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_r Γ^r_{rr}`, reduced. -/
def dr_Gr_rr : Frac 6 := ⟨-a ^ 4 * d * w * x ^ 4 + a ^ 4 * v ^ 2 * x ^ 4 + 2 * a ^ 2 * d ^ 2 * x ^
    2 - 2 * a ^ 2 * d * r ^ 2 * w * x ^ 2 + 2 * a ^ 2 * r ^ 2 * v ^ 2 * x ^ 2 - 2 * d ^ 2 * r ^ 2 -
    d * r ^ 4 * w + r ^ 4 * v ^ 2, 2 * d ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2⟩

/-- `∂_r Γ^r_{rr}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_r_r_rr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δr Gr_rr) (dr_Gr_rr))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rr, dr_Gr_rr, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_x Γ^r_{rr}`, reduced. -/
def dx_Gr_rr : Frac 6 := ⟨-2 * a ^ 2 * r * x, (a ^ 2 * x ^ 2 + r ^ 2) ^ 2⟩

/-- `∂_x Γ^r_{rr}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_x_r_rr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx Gr_rr) (dx_Gr_rr))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rr, dx_Gr_rr, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_r Γ^r_{rx}`, reduced. -/
def dr_Gr_rx : Frac 6 := ⟨-2 * a ^ 2 * r * x, (a ^ 2 * x ^ 2 + r ^ 2) ^ 2⟩

/-- `∂_r Γ^r_{rx}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_r_r_rx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δr Gr_rx) (dr_Gr_rx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, dr_Gr_rx, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_x Γ^r_{rx}`, reduced. -/
def dx_Gr_rx : Frac 6 := ⟨-a ^ 2 * (a * x - r) * (a * x + r), (a ^ 2 * x ^ 2 + r ^ 2) ^ 2⟩

/-- `∂_x Γ^r_{rx}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_x_r_rx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx Gr_rx) (dx_Gr_rx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx, dx_Gr_rx, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_r Γ^r_{tp}`, reduced. -/
def dr_Gr_tp : Frac 6 := ⟨-a * (x - 1) * (x + 1) * (-a ^ 4 * d * w * x ^ 4 + 2 * a ^ 4 * d * x ^ 4
    - 2 * a ^ 4 * d * x ^ 2 + 2 * a ^ 4 * r * v * x ^ 4 - 2 * a ^ 4 * r * v * x ^ 2 - a ^ 4 * v ^ 2
    * x ^ 4 + 2 * a ^ 2 * d ^ 2 * x ^ 2 - 2 * a ^ 2 * d * r ^ 2 * w * x ^ 2 - 10 * a ^ 2 * d * r ^
    2 * x ^ 2 + 10 * a ^ 2 * d * r ^ 2 + 8 * a ^ 2 * d * r * v * x ^ 2 + 2 * a ^ 2 * r ^ 3 * v * x
    ^ 2 - 2 * a ^ 2 * r ^ 3 * v - 2 * a ^ 2 * r ^ 2 * v ^ 2 * x ^ 2 - 10 * d ^ 2 * r ^ 2 - d * r ^
    4 * w + 8 * d * r ^ 3 * v - r ^ 4 * v ^ 2), 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4⟩

/-- `∂_r Γ^r_{tp}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_r_r_tp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δr Gr_tp) (dr_Gr_tp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_tp, dr_Gr_tp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_x Γ^r_{tp}`, reduced. -/
def dx_Gr_tp : Frac 6 := ⟨a * d * x * (2 * a ^ 4 * r * x ^ 4 - 8 * a ^ 4 * r * x ^ 2 + 6 * a ^ 4 *
    r - a ^ 4 * v * x ^ 4 + 2 * a ^ 4 * v * x ^ 2 + 4 * a ^ 2 * d * r * x ^ 2 - 6 * a ^ 2 * d * r -
    4 * a ^ 2 * r ^ 3 * x ^ 2 + 4 * a ^ 2 * r ^ 3 + 2 * a ^ 2 * r ^ 2 * v - 2 * d * r ^ 3 + r ^ 4 *
    v), (a ^ 2 * x ^ 2 + r ^ 2) ^ 4⟩

/-- `∂_x Γ^r_{tp}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_x_r_tp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx Gr_tp) (dx_Gr_tp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_tp, dx_Gr_tp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_r Γ^r_{tt}`, reduced. -/
def dr_Gr_tt : Frac 6 := ⟨a ^ 4 * d * w * x ^ 4 - 2 * a ^ 4 * d * x ^ 4 + 2 * a ^ 4 * d * x ^ 2 - 2
    * a ^ 4 * r * v * x ^ 4 + 2 * a ^ 4 * r * v * x ^ 2 + a ^ 4 * v ^ 2 * x ^ 4 - 2 * a ^ 2 * d ^ 2
    * x ^ 2 + 2 * a ^ 2 * d * r ^ 2 * w * x ^ 2 + 10 * a ^ 2 * d * r ^ 2 * x ^ 2 - 10 * a ^ 2 * d *
    r ^ 2 - 8 * a ^ 2 * d * r * v * x ^ 2 - 2 * a ^ 2 * r ^ 3 * v * x ^ 2 + 2 * a ^ 2 * r ^ 3 * v +
    2 * a ^ 2 * r ^ 2 * v ^ 2 * x ^ 2 + 10 * d ^ 2 * r ^ 2 + d * r ^ 4 * w - 8 * d * r ^ 3 * v + r
    ^ 4 * v ^ 2, 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 4⟩

/-- `∂_r Γ^r_{tt}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_r_r_tt :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δr Gr_tt) (dr_Gr_tt))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_tt, dr_Gr_tt, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_x Γ^r_{tt}`, reduced. -/
def dx_Gr_tt : Frac 6 := ⟨2 * a ^ 2 * d * x * (2 * a ^ 2 * r * x ^ 2 - 3 * a ^ 2 * r - a ^ 2 * v *
    x ^ 2 + 3 * d * r - r ^ 3 - r ^ 2 * v), (a ^ 2 * x ^ 2 + r ^ 2) ^ 4⟩

/-- `∂_x Γ^r_{tt}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_x_r_tt :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx Gr_tt) (dx_Gr_tt))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_tt, dx_Gr_tt, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_r Γ^r_{xx}`, reduced. -/
def dr_Gr_xx : Frac 6 := ⟨a ^ 2 * d * x ^ 2 + a ^ 2 * r * v * x ^ 2 - d * r ^ 2 + r ^ 3 * v, (x -
    1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2⟩

/-- `∂_r Γ^r_{xx}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_r_r_xx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δr Gr_xx) (dr_Gr_xx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_xx, dr_Gr_xx, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_x Γ^r_{xx}`, reduced. -/
def dx_Gr_xx : Frac 6 := ⟨-2 * d * r * x * (2 * a ^ 2 * x ^ 2 - a ^ 2 + r ^ 2), (x - 1) ^ 2 * (x +
    1) ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2⟩

/-- `∂_x Γ^r_{xx}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_x_r_xx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx Gr_xx) (dx_Gr_xx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_xx, dx_Gr_xx, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_r Γ^t_{rp}`, reduced. -/
def dr_Gt_rp : Frac 6 := ⟨-a * (x - 1) * (x + 1) * (-a ^ 6 * d * w * x ^ 4 - 2 * a ^ 6 * d * x ^ 2
    + 2 * a ^ 6 * r * v * x ^ 2 + a ^ 6 * v ^ 2 * x ^ 4 + 2 * a ^ 4 * d ^ 2 * x ^ 4 + 2 * a ^ 4 * d
    ^ 2 * x ^ 2 - a ^ 4 * d * r ^ 2 * w * x ^ 4 - 2 * a ^ 4 * d * r ^ 2 * w * x ^ 2 - 12 * a ^ 4 *
    d * r ^ 2 * x ^ 2 + 6 * a ^ 4 * d * r ^ 2 - 2 * a ^ 4 * d * r * v * x ^ 4 + 2 * a ^ 4 * d * r *
    v * x ^ 2 + 4 * a ^ 4 * r ^ 3 * v * x ^ 2 + 2 * a ^ 4 * r ^ 3 * v + a ^ 4 * r ^ 2 * v ^ 2 * x ^
    4 + 2 * a ^ 4 * r ^ 2 * v ^ 2 * x ^ 2 + 6 * a ^ 2 * d ^ 2 * r ^ 2 * x ^ 2 - 6 * a ^ 2 * d ^ 2 *
    r ^ 2 - 2 * a ^ 2 * d * r ^ 4 * w * x ^ 2 - a ^ 2 * d * r ^ 4 * w - 10 * a ^ 2 * d * r ^ 4 * x
    ^ 2 + 4 * a ^ 2 * d * r ^ 4 - 2 * a ^ 2 * d * r ^ 3 * v * x ^ 2 + 2 * a ^ 2 * d * r ^ 3 * v + 2
    * a ^ 2 * r ^ 5 * v * x ^ 2 + 4 * a ^ 2 * r ^ 5 * v + 2 * a ^ 2 * r ^ 4 * v ^ 2 * x ^ 2 + a ^ 2
    * r ^ 4 * v ^ 2 - 4 * d ^ 2 * r ^ 4 - d * r ^ 6 * w - 2 * d * r ^ 6 + 2 * r ^ 7 * v + r ^ 6 * v
    ^ 2), 2 * d ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- `∂_r Γ^t_{rp}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_r_t_rp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δr Gt_rp) (dr_Gt_rp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_rp, dr_Gt_rp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_x Γ^t_{rp}`, reduced. -/
def dx_Gt_rp : Frac 6 := ⟨-a * x * (a ^ 2 + r ^ 2) ^ 2 * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a
    ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v), d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- `∂_x Γ^t_{rp}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_x_t_rp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx Gt_rp) (dx_Gt_rp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_rp, dx_Gt_rp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_r Γ^t_{tr}`, reduced. -/
def dr_Gt_tr : Frac 6 := ⟨a ^ 6 * d * w * x ^ 4 - 2 * a ^ 6 * d * x ^ 4 + 2 * a ^ 6 * d * x ^ 2 + 2
    * a ^ 6 * r * v * x ^ 4 - 2 * a ^ 6 * r * v * x ^ 2 - a ^ 6 * v ^ 2 * x ^ 4 - 2 * a ^ 4 * d ^ 2
    * x ^ 2 + a ^ 4 * d * r ^ 2 * w * x ^ 4 + 2 * a ^ 4 * d * r ^ 2 * w * x ^ 2 - 6 * a ^ 4 * d * r
    ^ 2 * x ^ 4 + 12 * a ^ 4 * d * r ^ 2 * x ^ 2 - 6 * a ^ 4 * d * r ^ 2 + 2 * a ^ 4 * d * r * v *
    x ^ 4 - 2 * a ^ 4 * d * r * v * x ^ 2 + 2 * a ^ 4 * r ^ 3 * v * x ^ 4 - 2 * a ^ 4 * r ^ 3 * v -
    a ^ 4 * r ^ 2 * v ^ 2 * x ^ 4 - 2 * a ^ 4 * r ^ 2 * v ^ 2 * x ^ 2 - 6 * a ^ 2 * d ^ 2 * r ^ 2 *
    x ^ 2 + 6 * a ^ 2 * d ^ 2 * r ^ 2 + 2 * a ^ 2 * d * r ^ 4 * w * x ^ 2 + a ^ 2 * d * r ^ 4 * w +
    2 * a ^ 2 * d * r ^ 4 * x ^ 2 - 2 * a ^ 2 * d * r ^ 4 + 2 * a ^ 2 * d * r ^ 3 * v * x ^ 2 - 2 *
    a ^ 2 * d * r ^ 3 * v + 2 * a ^ 2 * r ^ 5 * v * x ^ 2 - 2 * a ^ 2 * r ^ 5 * v - 2 * a ^ 2 * r ^
    4 * v ^ 2 * x ^ 2 - a ^ 2 * r ^ 4 * v ^ 2 + 2 * d ^ 2 * r ^ 4 + d * r ^ 6 * w - r ^ 6 * v ^ 2,
    2 * d ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- `∂_r Γ^t_{tr}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_r_t_tr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δr Gt_tr) (dr_Gt_tr))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tr, dr_Gt_tr, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_x Γ^t_{tr}`, reduced. -/
def dx_Gt_tr : Frac 6 := ⟨a ^ 2 * x * (a ^ 2 + r ^ 2) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a
    ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v), d * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- `∂_x Γ^t_{tr}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_x_t_tr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx Gt_tr) (dx_Gt_tr))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tr, dx_Gt_tr, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_r Γ^t_{tx}`, reduced. -/
def dr_Gt_tx : Frac 6 := ⟨a ^ 2 * x * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r - a ^ 2 * v * x ^ 2 +
    4 * d * r - 2 * r ^ 3 - r ^ 2 * v), (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- `∂_r Γ^t_{tx}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_r_t_tx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δr Gt_tx) (dr_Gt_tx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tx, dr_Gt_tx, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_x Γ^t_{tx}`, reduced. -/
def dx_Gt_tx : Frac 6 := ⟨-a ^ 2 * (3 * a ^ 2 * x ^ 2 - r ^ 2) * (a ^ 2 - d + r ^ 2), (a ^ 2 * x ^
    2 + r ^ 2) ^ 3⟩

/-- `∂_x Γ^t_{tx}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_x_t_tx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx Gt_tx) (dx_Gt_tx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_tx, dx_Gt_tx, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_r Γ^t_{xp}`, reduced. -/
def dr_Gt_xp : Frac 6 := ⟨a ^ 3 * x * (x - 1) * (x + 1) * (2 * a ^ 2 * r * x ^ 2 - 4 * a ^ 2 * r -
    a ^ 2 * v * x ^ 2 + 4 * d * r - 2 * r ^ 3 - r ^ 2 * v), (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- `∂_r Γ^t_{xp}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_r_t_xp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δr Gt_xp) (dr_Gt_xp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_xp, dr_Gt_xp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_x Γ^t_{xp}`, reduced. -/
def dx_Gt_xp : Frac 6 := ⟨-a ^ 3 * (a ^ 2 - d + r ^ 2) * (a ^ 2 * x ^ 4 - 3 * a ^ 2 * x ^ 2 - 3 * r
    ^ 2 * x ^ 2 + r ^ 2), (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- `∂_x Γ^t_{xp}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_x_t_xp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx Gt_xp) (dx_Gt_xp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gt_xp, dx_Gt_xp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_r Γ^x_{pp}`, reduced. -/
def dr_Gx_pp : Frac 6 := ⟨-a ^ 2 * x * (x - 1) ^ 2 * (x + 1) ^ 2 * (6 * a ^ 4 * r + a ^ 4 * v * x ^
    4 + a ^ 4 * v * x ^ 2 - 2 * a ^ 2 * d * r * x ^ 2 - 6 * a ^ 2 * d * r + 12 * a ^ 2 * r ^ 3 + 3
    * a ^ 2 * r ^ 2 * v * x ^ 2 + a ^ 2 * r ^ 2 * v - 8 * d * r ^ 3 + 6 * r ^ 5 + 2 * r ^ 4 * v),
    (a ^ 2 * x ^ 2 + r ^ 2) ^ 4⟩

/-- `∂_r Γ^x_{pp}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_r_x_pp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δr Gx_pp) (dr_Gx_pp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_pp, dr_Gx_pp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_x Γ^x_{pp}`, reduced. -/
def dx_Gx_pp : Frac 6 := ⟨3 * a ^ 8 * x ^ 4 - 5 * a ^ 8 * x ^ 2 - a ^ 6 * d * x ^ 8 - a ^ 6 * d * x
    ^ 6 - 3 * a ^ 6 * d * x ^ 4 + 5 * a ^ 6 * d * x ^ 2 + 9 * a ^ 6 * r ^ 2 * x ^ 4 - 18 * a ^ 6 *
    r ^ 2 * x ^ 2 + a ^ 6 * r ^ 2 - 5 * a ^ 4 * d * r ^ 2 * x ^ 6 - 7 * a ^ 4 * d * r ^ 2 * x ^ 4 +
    13 * a ^ 4 * d * r ^ 2 * x ^ 2 - a ^ 4 * d * r ^ 2 + 9 * a ^ 4 * r ^ 4 * x ^ 4 - 24 * a ^ 4 * r
    ^ 4 * x ^ 2 + 3 * a ^ 4 * r ^ 4 - 10 * a ^ 2 * d * r ^ 4 * x ^ 4 + 12 * a ^ 2 * d * r ^ 4 * x ^
    2 - 2 * a ^ 2 * d * r ^ 4 + 3 * a ^ 2 * r ^ 6 * x ^ 4 - 14 * a ^ 2 * r ^ 6 * x ^ 2 + 3 * a ^ 2
    * r ^ 6 - 3 * r ^ 8 * x ^ 2 + r ^ 8, (a ^ 2 * x ^ 2 + r ^ 2) ^ 4⟩

/-- `∂_x Γ^x_{pp}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_x_x_pp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx Gx_pp) (dx_Gx_pp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_pp, dx_Gx_pp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_r Γ^x_{rr}`, reduced. -/
def dr_Gx_rr : Frac 6 := ⟨-a ^ 2 * x * (x - 1) * (x + 1) * (a ^ 2 * v * x ^ 2 + 2 * d * r + r ^ 2 *
    v), d ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2⟩

/-- `∂_r Γ^x_{rr}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_r_x_rr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δr Gx_rr) (dr_Gx_rr))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rr, dr_Gx_rr, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_x Γ^x_{rr}`, reduced. -/
def dx_Gx_rr : Frac 6 := ⟨a ^ 2 * (a ^ 2 * x ^ 4 + a ^ 2 * x ^ 2 + 3 * r ^ 2 * x ^ 2 - r ^ 2), d *
    (a ^ 2 * x ^ 2 + r ^ 2) ^ 2⟩

/-- `∂_x Γ^x_{rr}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_x_x_rr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx Gx_rr) (dx_Gx_rr))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rr, dx_Gx_rr, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_r Γ^x_{rx}`, reduced. -/
def dr_Gx_rx : Frac 6 := ⟨(a * x - r) * (a * x + r), (a ^ 2 * x ^ 2 + r ^ 2) ^ 2⟩

/-- `∂_r Γ^x_{rx}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_r_x_rx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δr Gx_rx) (dr_Gx_rx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rx, dr_Gx_rx, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_x Γ^x_{rx}`, reduced. -/
def dx_Gx_rx : Frac 6 := ⟨-2 * a ^ 2 * r * x, (a ^ 2 * x ^ 2 + r ^ 2) ^ 2⟩

/-- `∂_x Γ^x_{rx}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_x_x_rx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx Gx_rx) (dx_Gx_rx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rx, dx_Gx_rx, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_r Γ^x_{tp}`, reduced. -/
def dr_Gx_tp : Frac 6 := ⟨a * x * (x - 1) * (x + 1) * (4 * a ^ 4 * r * x ^ 2 - 6 * a ^ 4 * r - a ^
    4 * v * x ^ 2 - 2 * a ^ 2 * d * r * x ^ 2 + 6 * a ^ 2 * d * r + 4 * a ^ 2 * r ^ 3 * x ^ 2 - 8 *
    a ^ 2 * r ^ 3 - a ^ 2 * r ^ 2 * v * x ^ 2 - a ^ 2 * r ^ 2 * v + 4 * d * r ^ 3 - 2 * r ^ 5 - r ^
    4 * v), (a ^ 2 * x ^ 2 + r ^ 2) ^ 4⟩

/-- `∂_r Γ^x_{tp}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_r_x_tp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δr Gx_tp) (dr_Gx_tp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_tp, dr_Gx_tp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_x Γ^x_{tp}`, reduced. -/
def dx_Gx_tp : Frac 6 := ⟨-a * (a ^ 2 + r ^ 2) * (a ^ 2 - d + r ^ 2) * (3 * a ^ 2 * x ^ 4 - 5 * a ^
    2 * x ^ 2 - 3 * r ^ 2 * x ^ 2 + r ^ 2), (a ^ 2 * x ^ 2 + r ^ 2) ^ 4⟩

/-- `∂_x Γ^x_{tp}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_x_x_tp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx Gx_tp) (dx_Gx_tp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_tp, dx_Gx_tp, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_r Γ^x_{tt}`, reduced. -/
def dr_Gx_tt : Frac 6 := ⟨-a ^ 2 * x * (x - 1) * (x + 1) * (2 * a ^ 2 * r * x ^ 2 - 6 * a ^ 2 * r -
    a ^ 2 * v * x ^ 2 + 6 * d * r - 4 * r ^ 3 - r ^ 2 * v), (a ^ 2 * x ^ 2 + r ^ 2) ^ 4⟩

/-- `∂_r Γ^x_{tt}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_r_x_tt :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δr Gx_tt) (dr_Gx_tt))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_tt, dr_Gx_tt, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_x Γ^x_{tt}`, reduced. -/
def dx_Gx_tt : Frac 6 := ⟨a ^ 2 * (a ^ 2 - d + r ^ 2) * (3 * a ^ 2 * x ^ 4 - 5 * a ^ 2 * x ^ 2 - 3
    * r ^ 2 * x ^ 2 + r ^ 2), (a ^ 2 * x ^ 2 + r ^ 2) ^ 4⟩

/-- `∂_x Γ^x_{tt}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_x_x_tt :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx Gx_tt) (dx_Gx_tt))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_tt, dx_Gx_tt, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_r Γ^x_{xx}`, reduced. -/
def dr_Gx_xx : Frac 6 := ⟨-2 * a ^ 2 * r * x, (a ^ 2 * x ^ 2 + r ^ 2) ^ 2⟩

/-- `∂_r Γ^x_{xx}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_r_x_xx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δr Gx_xx) (dr_Gx_xx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_xx, dr_Gx_xx, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

/-- `∂_x Γ^x_{xx}`, reduced. -/
def dx_Gx_xx : Frac 6 := ⟨(a ^ 2 + r ^ 2) * (3 * a ^ 2 * x ^ 4 - a ^ 2 * x ^ 2 + r ^ 2 * x ^ 2 + r
    ^ 2), (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2⟩

/-- `∂_x Γ^x_{xx}` by `Foundations/FormalDerivation`, reduced. -/
theorem deriv_x_x_xx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx Gx_xx) (dx_Gx_xx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_xx, dx_Gx_xx, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5, δx_0, δx_1, δx_2, δx_3,
        δx_4, δx_5]
    ring)

end LeanProofs.IPRA.Geometry.KerrNewmanConnectionDerivatives
