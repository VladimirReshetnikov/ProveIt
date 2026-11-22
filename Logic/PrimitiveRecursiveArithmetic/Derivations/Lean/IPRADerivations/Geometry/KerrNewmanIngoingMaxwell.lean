import IPRADerivations.Geometry.KerrNewmanIngoingConnection

/-!
# The Maxwell field and the stress tensor in the ingoing chart (`four_metrics_ipra`)

Packet: `geometry/four_metrics_ipra_2026-11-15`, `prop:regular` ("Field equations at
`Δ = 0`"), direct proof, last third: the potential `A₊ = −(q r/Σ) p₊` of `eq:ingoing`, its
field, the Maxwell equations and the stress tensor of `eq:EM`, with the metric and the inverse
of `Geometry/KerrNewmanIngoingConnection`, in the coordinates `(v, r, x, ψ)` (index `p` for
`ψ`). Antisymmetric components are named with their indices in this order.

* The potential: `A_v = −q r/Σ`, `A_ψ = q r a s/Σ`, `A_r = A_x = 0`.
* `field_vr`, `field_vx`, `field_rp`, `field_xp` (`eq:Ftable`): `F_{μν} = ∂_μ A_ν − ∂_ν A_μ`
  gives `F_vr = −E`, `F_vx = −a 𝓑`, `F_rψ = −a s E`, `F_xψ = −P 𝓑`, with
  `E = q (r² − a² x²)/Σ²`, `𝓑 = 2 q a r x/Σ²`; `F_vψ` and `F_rx` have no term.
* `closed_v`, `closed_p` (`eq:dF`): the two components of `dF = 0` that are not identically
  trivial.
* `raise_vr`, …, `raise_xp`: `F^{μν} = Σ_{α,β} g^{μα} g^{νβ} F_{αβ}` for the six pairs
  `μ < ν`, each term reduced over a common denominator (`Uμν_tk`); `F^{vψ} = F^{rx} = 0`, and
  the others are the reduced fractions `Uvr`, `Uvx`, `Urp`, `Uxp`. They do not contain `m`:
  `Δ` cancels.
* `maxwell_v`, `maxwell_p` (`eq:maxwell`): `∂_r(Σ F^{rν}) + ∂_x(Σ F^{xν}) = 0` for `ν = v, ψ`
  (`det g₊ = −Σ²`). For `ν = r` the only candidate term is `∂_x(Σ F^{xr})` and for `ν = x` it
  is `∂_r(Σ F^{rx})`, with `F^{rx} = 0` by `raise_rx`.
* `F2_half` (`eq:F2`): `Σ_{α<β} F_{αβ} F^{αβ} = 𝓑² − E²`.
* The stress tensor of `eq:EM`,
  `T_{μν} = 2 (Σ_{ρ,σ} F_{μρ} g^{ρσ} F_{νσ} − ¼ g_{μν} F_{αβ} F^{αβ})`: each term whose factors
  are nonzero is reduced over a common denominator (`Tμν_tk`), and `stress_μν` gives, with
  `K = q²/Σ²`, `T_vv = K (Δ + a² s)/Σ`, `T_vr = −K`, `T_vψ = −K a s (Δ + P)/Σ`,
  `T_rψ = K a s`, `T_ψψ = K s (Δ a² s + P²)/Σ`, `T_xx = K Σ/s`, and
  `T_vx = T_rr = T_rx = T_xψ = 0`.

**The Einstein–Maxwell equation in the ingoing chart.** For every pair `μ ≤ ν`, the theorem
`stress_μν` here and the theorem `ricci_μν` of `Geometry/KerrNewmanIngoingRicci` have literally
the same right-hand side, in the same indeterminates `r, x, a, m, q`: the sum of the terms of
`eq:ricci` and the sum of the terms of the right-hand side of `eq:EM` are the same fraction,
`R_{μν} = T_{μν}`. No denominator contains `Δ` (every common denominator is a product of `2`,
`Σ` and `s`), so the identities need only `Σ s ≠ 0` and hold at `Δ = 0`: `prop:regular`. The
composition of the two cleared identities of an entry into one is not stated.

The reduced fractions and the numerators were proposed by a computer algebra script; every
identity is checked by Lean as an identity of fractions cleared of denominators, a closed
sentence of iPRA certified in every commutative ring.
-/

namespace LeanProofs.IPRA.Geometry.KerrNewmanIngoingMaxwell

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Geometry.KerrNewmanIngoingConnection
open ZExp

local notation "r" => (ZExp.var 0 : ZExp 5)
local notation "x" => (ZExp.var 1 : ZExp 5)
local notation "a" => (ZExp.var 2 : ZExp 5)
local notation "m" => (ZExp.var 3 : ZExp 5)
local notation "q" => (ZExp.var 4 : ZExp 5)

/-! ## The potential and the field -/

/-- The numerator of `E`: `q (r² − a² x²)`. -/
def En : ZExp 5 := q * (r ^ 2 - a ^ 2 * x ^ 2)
/-- The numerator of `𝓑`: `2 q a r x`. -/
def Bn : ZExp 5 := 2 * q * a * r * x
/-- `E = q (r² − a² x²)/Σ²`. -/
def Ef : Frac 5 := ⟨En, Sg ^ 2⟩
/-- `𝓑 = 2 q a r x/Σ²`. -/
def Bf : Frac 5 := ⟨Bn, Sg ^ 2⟩
/-- `A_v = −q r/Σ`. -/
def Av : Frac 5 := ⟨-(q * r), Sg⟩
/-- `A_ψ = q r a s/Σ`. -/
def Ap : Frac 5 := ⟨q * r * a * sx, Sg⟩
/-- `F_vr = −E`. -/
def Fvr : Frac 5 := ⟨-En, Sg ^ 2⟩
/-- `F_vx = −a 𝓑`. -/
def Fvx : Frac 5 := ⟨-(a * Bn), Sg ^ 2⟩
/-- `F_rψ = −a s E`. -/
def Frp : Frac 5 := ⟨-(a * sx * En), Sg ^ 2⟩
/-- `F_xψ = −P 𝓑`. -/
def Fxp : Frac 5 := ⟨-(Pp * Bn), Sg ^ 2⟩

/-! ## The field `F = dA` (`eq:Ftable`) and `dF = 0` (`eq:dF`) -/

/-- `F_{vr} = ∂_v A_r − ∂_r A_v`. -/
theorem field_vr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (-Frac.d δr Av) (Fvr))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Av, Ap, Sg, sx, Pp, Fvr, Fvx, Frp, Fxp, En, Bn, δr_0, δr_1, δr_2, δr_3, δr_4,
        δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `F_{vx} = ∂_v A_x − ∂_x A_v`. -/
theorem field_vx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (-Frac.d δx Av) (Fvx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Av, Ap, Sg, sx, Pp, Fvr, Fvx, Frp, Fxp, En, Bn, δr_0, δr_1, δr_2, δr_3, δr_4,
        δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `F_{rp} = ∂_r A_p − ∂_p A_r`. -/
theorem field_rp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.d δr Ap) (Frp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Av, Ap, Sg, sx, Pp, Fvr, Fvx, Frp, Fxp, En, Bn, δr_0, δr_1, δr_2, δr_3, δr_4,
        δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `F_{xp} = ∂_x A_p − ∂_p A_x`. -/
theorem field_xp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.d δx Ap) (Fxp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Av, Ap, Sg, sx, Pp, Fvr, Fvx, Frp, Fxp, En, Bn, δr_0, δr_1, δr_2, δr_3, δr_4,
        δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `∂_r F_{xv} + ∂_x F_{vr} = 0` (`dF = 0`, component `v r x`). -/
theorem closed_v :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.d δx Fvr - Frac.d δr Fvx) (Frac.ofZ 0))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Sg, sx, Pp, Fvr, Fvx, Frp, Fxp, En, Bn, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0,
        δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `∂_r F_{xψ} + ∂_x F_{ψr} = 0` (`dF = 0`, component `r x ψ`). -/
theorem closed_p :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.d δr Fxp - Frac.d δx Frp) (Frac.ofZ 0))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Sg, sx, Pp, Fvr, Fvx, Frp, Fxp, En, Bn, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0,
        δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ## The field with raised indices -/

/-! ### `F^{vr}` -/

/-- `F^{vr}`, reduced. -/
def Uvr : Frac 5 := ⟨-q * (a ^ 2 + r ^ 2) * (a * x - r) * (a * x + r), (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `F^{vr}`. -/
def Uvr_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 4

/-- The numerator of `g^{vv} g^{rr} F_{vr}` over the common denominator. -/
def Uvr_n1 : ZExp 5 := -a ^ 2 * q * (x - 1) * (x + 1) * (a * x - r) * (a * x + r) * (a ^ 2 - 2 * m
    * r + q ^ 2 + r ^ 2)
/-- `g^{vv} g^{rr} F_{vr}`, reduced to the common denominator. -/
theorem Uvr_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (ivv * irr * Fvr) (⟨Uvr_n1, Uvr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Uvr_n1, Uvr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `g^{vr} g^{rv} F_{vr}` over the common denominator. -/
def Uvr_n2 : ZExp 5 := q * (a ^ 2 + r ^ 2) ^ 2 * (a * x - r) * (a * x + r)
/-- `g^{vr} g^{rv} F_{vr}`, reduced to the common denominator. -/
theorem Uvr_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (ivr * ivr * Fvr) (⟨Uvr_n2, Uvr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Uvr_n2, Uvr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `g^{vr} g^{rp} F_{rp}` over the common denominator. -/
def Uvr_n3 : ZExp 5 := -a ^ 2 * q * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a * x - r) * (a * x + r)
/-- `g^{vr} g^{rp} F_{rp}`, reduced to the common denominator. -/
theorem Uvr_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (ivr * irp * Frp) (⟨Uvr_n3, Uvr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Uvr_n3, Uvr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `g^{vp} g^{rr} F_{rp}` over the common denominator. -/
def Uvr_n4 : ZExp 5 := -a ^ 2 * q * (x - 1) * (x + 1) * (a * x - r) * (a * x + r) * (a ^ 2 - 2 * m
    * r + q ^ 2 + r ^ 2)
/-- `g^{vp} g^{rr} F_{rp}`, reduced to the common denominator. -/
theorem Uvr_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (ivp * irr * Frp) (⟨Uvr_n4, Uvr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Uvr_n4, Uvr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- `F^{vr} = Σ g^{vα} g^{rβ} F_{αβ}`: the signed sum of its terms is the reduced fraction. -/
theorem raise_vr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Uvr_n1 - Uvr_n2 + Uvr_n3 - Uvr_n4, Uvr_cd⟩) (Uvr))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Uvr_n1, Uvr_n2, Uvr_n3, Uvr_n4, Uvr_cd, Uvr, δr_0, δr_1, δr_2, δr_3, δr_4,
        δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ### `F^{vx}` -/

/-- `F^{vx}`, reduced. -/
def Uvx : Frac 5 := ⟨-2 * a ^ 2 * q * r * x * (x - 1) * (x + 1), (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `F^{vx}`. -/
def Uvx_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 4

/-- The numerator of `g^{vv} g^{xx} F_{vx}` over the common denominator. -/
def Uvx_n1 : ZExp 5 := -2 * a ^ 4 * q * r * x * (x - 1) ^ 2 * (x + 1) ^ 2
/-- `g^{vv} g^{xx} F_{vx}`, reduced to the common denominator. -/
theorem Uvx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (ivv * ixx * Fvx) (⟨Uvx_n1, Uvx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Uvx_n1, Uvx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `g^{vp} g^{xx} F_{xp}` over the common denominator. -/
def Uvx_n2 : ZExp 5 := 2 * a ^ 2 * q * r * x * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1)
/-- `g^{vp} g^{xx} F_{xp}`, reduced to the common denominator. -/
theorem Uvx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (ivp * ixx * Fxp) (⟨Uvx_n2, Uvx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Uvx_n2, Uvx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- `F^{vx} = Σ g^{vα} g^{xβ} F_{αβ}`: the signed sum of its terms is the reduced fraction. -/
theorem raise_vx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Uvx_n1 - Uvx_n2, Uvx_cd⟩) (Uvx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Uvx_n1, Uvx_n2, Uvx_cd, Uvx, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-! ### `F^{vp}` -/

/-- The common denominator of the terms of `F^{vp}`. -/
def Uvp_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 4

/-- The numerator of `g^{vv} g^{pr} F_{vr}` over the common denominator. -/
def Uvp_n1 : ZExp 5 := -a ^ 3 * q * (x - 1) * (x + 1) * (a * x - r) * (a * x + r)
/-- `g^{vv} g^{pr} F_{vr}`, reduced to the common denominator. -/
theorem Uvp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (ivv * irp * Fvr) (⟨Uvp_n1, Uvp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Uvp_n1, Uvp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `g^{vr} g^{pv} F_{vr}` over the common denominator. -/
def Uvp_n2 : ZExp 5 := a * q * (a ^ 2 + r ^ 2) * (a * x - r) * (a * x + r)
/-- `g^{vr} g^{pv} F_{vr}`, reduced to the common denominator. -/
theorem Uvp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (ivr * ivp * Fvr) (⟨Uvp_n2, Uvp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Uvp_n2, Uvp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `g^{vr} g^{pp} F_{rp}` over the common denominator. -/
def Uvp_n3 : ZExp 5 := a * q * (a ^ 2 + r ^ 2) * (a * x - r) * (a * x + r)
/-- `g^{vr} g^{pp} F_{rp}`, reduced to the common denominator. -/
theorem Uvp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (ivr * ipp * Frp) (⟨Uvp_n3, Uvp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Uvp_n3, Uvp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `g^{vp} g^{pr} F_{rp}` over the common denominator. -/
def Uvp_n4 : ZExp 5 := -a ^ 3 * q * (x - 1) * (x + 1) * (a * x - r) * (a * x + r)
/-- `g^{vp} g^{pr} F_{rp}`, reduced to the common denominator. -/
theorem Uvp_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (ivp * irp * Frp) (⟨Uvp_n4, Uvp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Uvp_n4, Uvp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- `F^{vp} = Σ g^{vα} g^{pβ} F_{αβ}`: the signed sum of its terms is `0`. -/
theorem raise_vp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Uvp_n1 - Uvp_n2 + Uvp_n3 - Uvp_n4, Uvp_cd⟩) (Frac.ofZ 0))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Uvp_n1, Uvp_n2, Uvp_n3, Uvp_n4, Uvp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0,
        δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ### `F^{rx}` -/

/-- The common denominator of the terms of `F^{rx}`. -/
def Urx_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 4

/-- The numerator of `g^{rv} g^{xx} F_{vx}` over the common denominator. -/
def Urx_n1 : ZExp 5 := 2 * a ^ 2 * q * r * x * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1)
/-- `g^{rv} g^{xx} F_{vx}`, reduced to the common denominator. -/
theorem Urx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (ivr * ixx * Fvx) (⟨Urx_n1, Urx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Urx_n1, Urx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `g^{rp} g^{xx} F_{xp}` over the common denominator. -/
def Urx_n2 : ZExp 5 := 2 * a ^ 2 * q * r * x * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1)
/-- `g^{rp} g^{xx} F_{xp}`, reduced to the common denominator. -/
theorem Urx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (irp * ixx * Fxp) (⟨Urx_n2, Urx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Urx_n2, Urx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- `F^{rx} = Σ g^{rα} g^{xβ} F_{αβ}`: the signed sum of its terms is `0`. -/
theorem raise_rx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Urx_n1 - Urx_n2, Urx_cd⟩) (Frac.ofZ 0))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Urx_n1, Urx_n2, Urx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-! ### `F^{rp}` -/

/-- `F^{rp}`, reduced. -/
def Urp : Frac 5 := ⟨a * q * (a * x - r) * (a * x + r), (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `F^{rp}`. -/
def Urp_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 4

/-- The numerator of `g^{rv} g^{pr} F_{vr}` over the common denominator. -/
def Urp_n1 : ZExp 5 := a * q * (a ^ 2 + r ^ 2) * (a * x - r) * (a * x + r)
/-- `g^{rv} g^{pr} F_{vr}`, reduced to the common denominator. -/
theorem Urp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (ivr * irp * Fvr) (⟨Urp_n1, Urp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Urp_n1, Urp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `g^{rr} g^{pv} F_{vr}` over the common denominator. -/
def Urp_n2 : ZExp 5 := a * q * (a * x - r) * (a * x + r) * (a ^ 2 - 2 * m * r + q ^ 2 + r ^ 2)
/-- `g^{rr} g^{pv} F_{vr}`, reduced to the common denominator. -/
theorem Urp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (irr * ivp * Fvr) (⟨Urp_n2, Urp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Urp_n2, Urp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `g^{rr} g^{pp} F_{rp}` over the common denominator. -/
def Urp_n3 : ZExp 5 := a * q * (a * x - r) * (a * x + r) * (a ^ 2 - 2 * m * r + q ^ 2 + r ^ 2)
/-- `g^{rr} g^{pp} F_{rp}`, reduced to the common denominator. -/
theorem Urp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (irr * ipp * Frp) (⟨Urp_n3, Urp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Urp_n3, Urp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `g^{rp} g^{pr} F_{rp}` over the common denominator. -/
def Urp_n4 : ZExp 5 := -a ^ 3 * q * (x - 1) * (x + 1) * (a * x - r) * (a * x + r)
/-- `g^{rp} g^{pr} F_{rp}`, reduced to the common denominator. -/
theorem Urp_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (irp * irp * Frp) (⟨Urp_n4, Urp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Urp_n4, Urp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- `F^{rp} = Σ g^{rα} g^{pβ} F_{αβ}`: the signed sum of its terms is the reduced fraction. -/
theorem raise_rp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Urp_n1 - Urp_n2 + Urp_n3 - Urp_n4, Urp_cd⟩) (Urp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Urp_n1, Urp_n2, Urp_n3, Urp_n4, Urp_cd, Urp, δr_0, δr_1, δr_2, δr_3, δr_4,
        δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ### `F^{xp}` -/

/-- `F^{xp}`, reduced. -/
def Uxp : Frac 5 := ⟨-2 * a * q * r * x, (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `F^{xp}`. -/
def Uxp_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 4

/-- The numerator of `g^{xx} g^{pv} F_{vx}` over the common denominator. -/
def Uxp_n1 : ZExp 5 := 2 * a ^ 3 * q * r * x * (x - 1) * (x + 1)
/-- `g^{xx} g^{pv} F_{vx}`, reduced to the common denominator. -/
theorem Uxp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (ixx * ivp * Fvx) (⟨Uxp_n1, Uxp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Uxp_n1, Uxp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `g^{xx} g^{pp} F_{xp}` over the common denominator. -/
def Uxp_n2 : ZExp 5 := -2 * a * q * r * x * (a ^ 2 + r ^ 2)
/-- `g^{xx} g^{pp} F_{xp}`, reduced to the common denominator. -/
theorem Uxp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (ixx * ipp * Fxp) (⟨Uxp_n2, Uxp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Uxp_n2, Uxp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- `F^{xp} = Σ g^{xα} g^{pβ} F_{αβ}`: the signed sum of its terms is the reduced fraction. -/
theorem raise_xp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨0 - Uxp_n1 + Uxp_n2, Uxp_cd⟩) (Uxp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Uxp_n1, Uxp_n2, Uxp_cd, Uxp, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-! ## The divergence equation `eq:maxwell` -/

/-- `∂_r(Σ F^{rv}) + ∂_x(Σ F^{xv}) = 0`. -/
theorem maxwell_v :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 0 - Frac.d δr (Frac.ofZ Sg * Uvr) - Frac.d δx (Frac.ofZ Sg *
          Uvx)) (Frac.ofZ 0))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Sg, sx, Pp, Dl, En, Bn, Uvr, Uvx, Urp, Uxp, δr_0, δr_1, δr_2, δr_3, δr_4,
        δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `∂_r(Σ F^{rp}) + ∂_x(Σ F^{xp}) = 0`. -/
theorem maxwell_p :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.d δr (Frac.ofZ Sg * Urp) + Frac.d δx (Frac.ofZ Sg * Uxp)) (Frac.ofZ
          0))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Sg, sx, Pp, Dl, En, Bn, Uvr, Uvx, Urp, Uxp, δr_0, δr_1, δr_2, δr_3, δr_4,
        δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ## The invariant `eq:F2` -/

/-- The common denominator of the terms of `½ F_{αβ} F^{αβ}`. -/
def F2_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `F_{vr} F^{vr}` over the common denominator. -/
def F2_n1 : ZExp 5 := -q ^ 2 * (a ^ 2 + r ^ 2) * (a * x - r) ^ 2 * (a * x + r) ^ 2
/-- `F_{vr} F^{vr}`, reduced to the common denominator. -/
theorem F2_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Fvr * Uvr) (⟨F2_n1, F2_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Fvr, Fvx, Frp, Fxp, En, Bn, Uvr, Uvx, Urp, Uxp, Sg, sx, Pp, Dl, F2_n1, F2_cd,
        δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `F_{vx} F^{vx}` over the common denominator. -/
def F2_n2 : ZExp 5 := 4 * a ^ 4 * q ^ 2 * r ^ 2 * x ^ 2 * (x - 1) * (x + 1)
/-- `F_{vx} F^{vx}`, reduced to the common denominator. -/
theorem F2_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Fvx * Uvx) (⟨F2_n2, F2_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Fvr, Fvx, Frp, Fxp, En, Bn, Uvr, Uvx, Urp, Uxp, Sg, sx, Pp, Dl, F2_n2, F2_cd,
        δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `F_{rp} F^{rp}` over the common denominator. -/
def F2_n3 : ZExp 5 := -a ^ 2 * q ^ 2 * (x - 1) * (x + 1) * (a * x - r) ^ 2 * (a * x + r) ^ 2
/-- `F_{rp} F^{rp}`, reduced to the common denominator. -/
theorem F2_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frp * Urp) (⟨F2_n3, F2_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Fvr, Fvx, Frp, Fxp, En, Bn, Uvr, Uvx, Urp, Uxp, Sg, sx, Pp, Dl, F2_n3, F2_cd,
        δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `F_{xp} F^{xp}` over the common denominator. -/
def F2_n4 : ZExp 5 := 4 * a ^ 2 * q ^ 2 * r ^ 2 * x ^ 2 * (a ^ 2 + r ^ 2)
/-- `F_{xp} F^{xp}`, reduced to the common denominator. -/
theorem F2_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Fxp * Uxp) (⟨F2_n4, F2_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Fvr, Fvx, Frp, Fxp, En, Bn, Uvr, Uvx, Urp, Uxp, Sg, sx, Pp, Dl, F2_n4, F2_cd,
        δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `eq:F2`: `Σ_{α<β} F_{αβ} F^{αβ} = 𝓑² − E²`, so `F_{αβ} F^{αβ} = 2 (𝓑² − E²)`. -/
theorem F2_half :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨F2_n1 + F2_n2 + F2_n3 + F2_n4, F2_cd⟩) (Bf * Bf - Ef * Ef))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [F2_n1, F2_n2, F2_n3, F2_n4, F2_cd, Ef, Bf, En, Bn, Sg, δr_0, δr_1, δr_2, δr_3,
        δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ## The stress tensor of `eq:EM` -/

/-! ### The entry `T_{vv}` -/

/-- The common denominator of the terms of `T_{vv}`. -/
def Tvv_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `2 F_{vr} g^{rr} F_{vr}` over the common denominator. -/
def Tvv_n1 : ZExp 5 := 2 * q ^ 2 * (a * x - r) ^ 2 * (a * x + r) ^ 2 * (a ^ 2 - 2 * m * r + q ^ 2 +
    r ^ 2)
/-- `2 F_{vr} g^{rr} F_{vr}`, reduced to the common denominator. -/
theorem Tvv_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Fvr * irr * Fvr)) (⟨Tvv_n1, Tvv_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Tvv_n1, Tvv_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `2 F_{vx} g^{xx} F_{vx}` over the common denominator. -/
def Tvv_n2 : ZExp 5 := -8 * a ^ 4 * q ^ 2 * r ^ 2 * x ^ 2 * (x - 1) * (x + 1)
/-- `2 F_{vx} g^{xx} F_{vx}`, reduced to the common denominator. -/
theorem Tvv_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Fvx * ixx * Fvx)) (⟨Tvv_n2, Tvv_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Tvv_n2, Tvv_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g_{vv} F_{αβ} F^{αβ} = g_{vv} (𝓑² − E²)` over the common denominator. -/
def Tvv_n3 : ZExp 5 := q ^ 2 * (a ^ 2 * x ^ 2 - 2 * a * r * x - r ^ 2) * (a ^ 2 * x ^ 2 + 2 * a * r
    * x - r ^ 2) * (a ^ 2 * x ^ 2 - 2 * m * r + q ^ 2 + r ^ 2)
/-- `½ g_{vv} F_{αβ} F^{αβ} = g_{vv} (𝓑² − E²)`, reduced to the common denominator. -/
theorem Tvv_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (gvv * (Bf * Bf - Ef * Ef)) (⟨Tvv_n3, Tvv_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Ef, Bf, En, Bn, Tvv_n3, Tvv_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- `T_{vv}`: the signed sum of its terms is `Kf * ⟨Dl + a ^ 2 * sx, Sg⟩`. -/
theorem stress_vv :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Tvv_n1 + Tvv_n2 - Tvv_n3, Tvv_cd⟩) (Kf * ⟨Dl + a ^ 2 * sx, Sg⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Tvv_n1, Tvv_n2, Tvv_n3, Tvv_cd, Kf, Sg, sx, Pp, Dl, δr_0, δr_1, δr_2, δr_3,
        δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ### The entry `T_{vr}` -/

/-- The common denominator of the terms of `T_{vr}`. -/
def Tvr_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `2 F_{vr} g^{rv} F_{vr}` over the common denominator. -/
def Tvr_n1 : ZExp 5 := 2 * q ^ 2 * (a ^ 2 + r ^ 2) * (a * x - r) ^ 2 * (a * x + r) ^ 2
/-- `2 F_{vr} g^{rv} F_{vr}`, reduced to the common denominator. -/
theorem Tvr_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Fvr * ivr * Fvr)) (⟨Tvr_n1, Tvr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Tvr_n1, Tvr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `2 F_{vr} g^{rp} F_{rp}` over the common denominator. -/
def Tvr_n2 : ZExp 5 := -2 * a ^ 2 * q ^ 2 * (x - 1) * (x + 1) * (a * x - r) ^ 2 * (a * x + r) ^ 2
/-- `2 F_{vr} g^{rp} F_{rp}`, reduced to the common denominator. -/
theorem Tvr_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Fvr * irp * Frp)) (⟨Tvr_n2, Tvr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Tvr_n2, Tvr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g_{vr} F_{αβ} F^{αβ} = g_{vr} (𝓑² − E²)` over the common denominator. -/
def Tvr_n3 : ZExp 5 := -q ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 - 2 * a * r * x - r ^ 2) *
    (a ^ 2 * x ^ 2 + 2 * a * r * x - r ^ 2)
/-- `½ g_{vr} F_{αβ} F^{αβ} = g_{vr} (𝓑² − E²)`, reduced to the common denominator. -/
theorem Tvr_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (gvr * (Bf * Bf - Ef * Ef)) (⟨Tvr_n3, Tvr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Ef, Bf, En, Bn, Tvr_n3, Tvr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- `T_{vr}`: the signed sum of its terms is `-Kf`. -/
theorem stress_vr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨0 - Tvr_n1 + Tvr_n2 - Tvr_n3, Tvr_cd⟩) (-Kf))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Tvr_n1, Tvr_n2, Tvr_n3, Tvr_cd, Kf, Sg, sx, Pp, Dl, δr_0, δr_1, δr_2, δr_3,
        δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ### The entry `T_{vx}` -/

/-- The common denominator of the terms of `T_{vx}`. -/
def Tvx_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `2 F_{vr} g^{rv} F_{vx}` over the common denominator. -/
def Tvx_n1 : ZExp 5 := -4 * a ^ 2 * q ^ 2 * r * x * (a ^ 2 + r ^ 2) * (a * x - r) * (a * x + r)
/-- `2 F_{vr} g^{rv} F_{vx}`, reduced to the common denominator. -/
theorem Tvx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Fvr * ivr * Fvx)) (⟨Tvx_n1, Tvx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Tvx_n1, Tvx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `2 F_{vr} g^{rp} F_{xp}` over the common denominator. -/
def Tvx_n2 : ZExp 5 := -4 * a ^ 2 * q ^ 2 * r * x * (a ^ 2 + r ^ 2) * (a * x - r) * (a * x + r)
/-- `2 F_{vr} g^{rp} F_{xp}`, reduced to the common denominator. -/
theorem Tvx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Fvr * irp * Fxp)) (⟨Tvx_n2, Tvx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Tvx_n2, Tvx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- `T_{vx}`: the signed sum of its terms is `Frac.ofZ 0`. -/
theorem stress_vx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨0 - Tvx_n1 + Tvx_n2, Tvx_cd⟩) (Frac.ofZ 0))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Tvx_n1, Tvx_n2, Tvx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-! ### The entry `T_{vp}` -/

/-- The common denominator of the terms of `T_{vp}`. -/
def Tvp_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `2 F_{vr} g^{rr} F_{rp}` over the common denominator. -/
def Tvp_n1 : ZExp 5 := -2 * a * q ^ 2 * (x - 1) * (x + 1) * (a * x - r) ^ 2 * (a * x + r) ^ 2 * (a
    ^ 2 - 2 * m * r + q ^ 2 + r ^ 2)
/-- `2 F_{vr} g^{rr} F_{rp}`, reduced to the common denominator. -/
theorem Tvp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Fvr * irr * Frp)) (⟨Tvp_n1, Tvp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Tvp_n1, Tvp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `2 F_{vx} g^{xx} F_{xp}` over the common denominator. -/
def Tvp_n2 : ZExp 5 := -8 * a ^ 3 * q ^ 2 * r ^ 2 * x ^ 2 * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1)
/-- `2 F_{vx} g^{xx} F_{xp}`, reduced to the common denominator. -/
theorem Tvp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Fvx * ixx * Fxp)) (⟨Tvp_n2, Tvp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Tvp_n2, Tvp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g_{vp} F_{αβ} F^{αβ} = g_{vp} (𝓑² − E²)` over the common denominator. -/
def Tvp_n3 : ZExp 5 := a * q ^ 2 * (x - 1) * (x + 1) * (-2 * m * r + q ^ 2) * (a ^ 2 * x ^ 2 - 2 *
    a * r * x - r ^ 2) * (a ^ 2 * x ^ 2 + 2 * a * r * x - r ^ 2)
/-- `½ g_{vp} F_{αβ} F^{αβ} = g_{vp} (𝓑² − E²)`, reduced to the common denominator. -/
theorem Tvp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (gvp * (Bf * Bf - Ef * Ef)) (⟨Tvp_n3, Tvp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Ef, Bf, En, Bn, Tvp_n3, Tvp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- `T_{vp}`: the signed sum of its terms is `-(Kf * ⟨a * sx * (Dl + Pp), Sg⟩)`. -/
theorem stress_vp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨0 - Tvp_n1 - Tvp_n2 - Tvp_n3, Tvp_cd⟩) (-(Kf * ⟨a * sx * (Dl + Pp),
          Sg⟩)))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Tvp_n1, Tvp_n2, Tvp_n3, Tvp_cd, Kf, Sg, sx, Pp, Dl, δr_0, δr_1, δr_2, δr_3,
        δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ### The entry `T_{rr}` -/

/-- The common denominator of the terms of `T_{rr}`. -/
def Trr_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `2 F_{vr} g^{vv} F_{vr}` over the common denominator. -/
def Trr_n1 : ZExp 5 := -2 * a ^ 2 * q ^ 2 * (x - 1) * (x + 1) * (a * x - r) ^ 2 * (a * x + r) ^ 2
/-- `2 F_{vr} g^{vv} F_{vr}`, reduced to the common denominator. -/
theorem Trr_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Fvr * ivv * Fvr)) (⟨Trr_n1, Trr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Trr_n1, Trr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `2 F_{vr} g^{vp} F_{rp}` over the common denominator. -/
def Trr_n2 : ZExp 5 := -2 * a ^ 2 * q ^ 2 * (x - 1) * (x + 1) * (a * x - r) ^ 2 * (a * x + r) ^ 2
/-- `2 F_{vr} g^{vp} F_{rp}`, reduced to the common denominator. -/
theorem Trr_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Fvr * ivp * Frp)) (⟨Trr_n2, Trr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Trr_n2, Trr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `2 F_{rp} g^{pv} F_{vr}` over the common denominator. -/
def Trr_n3 : ZExp 5 := -2 * a ^ 2 * q ^ 2 * (x - 1) * (x + 1) * (a * x - r) ^ 2 * (a * x + r) ^ 2
/-- `2 F_{rp} g^{pv} F_{vr}`, reduced to the common denominator. -/
theorem Trr_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Frp * ivp * Fvr)) (⟨Trr_n3, Trr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Trr_n3, Trr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `2 F_{rp} g^{pp} F_{rp}` over the common denominator. -/
def Trr_n4 : ZExp 5 := -2 * a ^ 2 * q ^ 2 * (x - 1) * (x + 1) * (a * x - r) ^ 2 * (a * x + r) ^ 2
/-- `2 F_{rp} g^{pp} F_{rp}`, reduced to the common denominator. -/
theorem Trr_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Frp * ipp * Frp)) (⟨Trr_n4, Trr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Trr_n4, Trr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- `T_{rr}`: the signed sum of its terms is `Frac.ofZ 0`. -/
theorem stress_rr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Trr_n1 - Trr_n2 - Trr_n3 + Trr_n4, Trr_cd⟩) (Frac.ofZ 0))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Trr_n1, Trr_n2, Trr_n3, Trr_n4, Trr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0,
        δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ### The entry `T_{rx}` -/

/-- The common denominator of the terms of `T_{rx}`. -/
def Trx_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `2 F_{vr} g^{vv} F_{vx}` over the common denominator. -/
def Trx_n1 : ZExp 5 := 4 * a ^ 4 * q ^ 2 * r * x * (x - 1) * (x + 1) * (a * x - r) * (a * x + r)
/-- `2 F_{vr} g^{vv} F_{vx}`, reduced to the common denominator. -/
theorem Trx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Fvr * ivv * Fvx)) (⟨Trx_n1, Trx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Trx_n1, Trx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `2 F_{vr} g^{vp} F_{xp}` over the common denominator. -/
def Trx_n2 : ZExp 5 := -4 * a ^ 2 * q ^ 2 * r * x * (a ^ 2 + r ^ 2) * (a * x - r) * (a * x + r)
/-- `2 F_{vr} g^{vp} F_{xp}`, reduced to the common denominator. -/
theorem Trx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Fvr * ivp * Fxp)) (⟨Trx_n2, Trx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Trx_n2, Trx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `2 F_{rp} g^{pv} F_{vx}` over the common denominator. -/
def Trx_n3 : ZExp 5 := 4 * a ^ 4 * q ^ 2 * r * x * (x - 1) * (x + 1) * (a * x - r) * (a * x + r)
/-- `2 F_{rp} g^{pv} F_{vx}`, reduced to the common denominator. -/
theorem Trx_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Frp * ivp * Fvx)) (⟨Trx_n3, Trx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Trx_n3, Trx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `2 F_{rp} g^{pp} F_{xp}` over the common denominator. -/
def Trx_n4 : ZExp 5 := -4 * a ^ 2 * q ^ 2 * r * x * (a ^ 2 + r ^ 2) * (a * x - r) * (a * x + r)
/-- `2 F_{rp} g^{pp} F_{xp}`, reduced to the common denominator. -/
theorem Trx_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Frp * ipp * Fxp)) (⟨Trx_n4, Trx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Trx_n4, Trx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- `T_{rx}`: the signed sum of its terms is `Frac.ofZ 0`. -/
theorem stress_rx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Trx_n1 - Trx_n2 - Trx_n3 + Trx_n4, Trx_cd⟩) (Frac.ofZ 0))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Trx_n1, Trx_n2, Trx_n3, Trx_n4, Trx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0,
        δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ### The entry `T_{rp}` -/

/-- The common denominator of the terms of `T_{rp}`. -/
def Trp_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `2 F_{vr} g^{vr} F_{rp}` over the common denominator. -/
def Trp_n1 : ZExp 5 := -2 * a * q ^ 2 * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a * x - r) ^ 2 * (a
    * x + r) ^ 2
/-- `2 F_{vr} g^{vr} F_{rp}`, reduced to the common denominator. -/
theorem Trp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Fvr * ivr * Frp)) (⟨Trp_n1, Trp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Trp_n1, Trp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `2 F_{rp} g^{pr} F_{rp}` over the common denominator. -/
def Trp_n2 : ZExp 5 := 2 * a ^ 3 * q ^ 2 * (x - 1) ^ 2 * (x + 1) ^ 2 * (a * x - r) ^ 2 * (a * x +
    r) ^ 2
/-- `2 F_{rp} g^{pr} F_{rp}`, reduced to the common denominator. -/
theorem Trp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Frp * irp * Frp)) (⟨Trp_n2, Trp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Trp_n2, Trp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g_{rp} F_{αβ} F^{αβ} = g_{rp} (𝓑² − E²)` over the common denominator. -/
def Trp_n3 : ZExp 5 := -a * q ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 -
    2 * a * r * x - r ^ 2) * (a ^ 2 * x ^ 2 + 2 * a * r * x - r ^ 2)
/-- `½ g_{rp} F_{αβ} F^{αβ} = g_{rp} (𝓑² − E²)`, reduced to the common denominator. -/
theorem Trp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (grp * (Bf * Bf - Ef * Ef)) (⟨Trp_n3, Trp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Ef, Bf, En, Bn, Trp_n3, Trp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- `T_{rp}`: the signed sum of its terms is `Kf * Frac.ofZ (a * sx)`. -/
theorem stress_rp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Trp_n1 - Trp_n2 - Trp_n3, Trp_cd⟩) (Kf * Frac.ofZ (a * sx)))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Trp_n1, Trp_n2, Trp_n3, Trp_cd, Kf, Sg, sx, Pp, Dl, δr_0, δr_1, δr_2, δr_3,
        δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ### The entry `T_{xx}` -/

/-- The common denominator of the terms of `T_{xx}`. -/
def Txx_cd : ZExp 5 := (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `2 F_{vx} g^{vv} F_{vx}` over the common denominator. -/
def Txx_n1 : ZExp 5 := -8 * a ^ 6 * q ^ 2 * r ^ 2 * x ^ 2 * (x - 1) ^ 2 * (x + 1) ^ 2
/-- `2 F_{vx} g^{vv} F_{vx}`, reduced to the common denominator. -/
theorem Txx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Fvx * ivv * Fvx)) (⟨Txx_n1, Txx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Txx_n1, Txx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `2 F_{vx} g^{vp} F_{xp}` over the common denominator. -/
def Txx_n2 : ZExp 5 := 8 * a ^ 4 * q ^ 2 * r ^ 2 * x ^ 2 * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1)
/-- `2 F_{vx} g^{vp} F_{xp}`, reduced to the common denominator. -/
theorem Txx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Fvx * ivp * Fxp)) (⟨Txx_n2, Txx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Txx_n2, Txx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `2 F_{xp} g^{pv} F_{vx}` over the common denominator. -/
def Txx_n3 : ZExp 5 := 8 * a ^ 4 * q ^ 2 * r ^ 2 * x ^ 2 * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1)
/-- `2 F_{xp} g^{pv} F_{vx}`, reduced to the common denominator. -/
theorem Txx_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Fxp * ivp * Fvx)) (⟨Txx_n3, Txx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Txx_n3, Txx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `2 F_{xp} g^{pp} F_{xp}` over the common denominator. -/
def Txx_n4 : ZExp 5 := -8 * a ^ 2 * q ^ 2 * r ^ 2 * x ^ 2 * (a ^ 2 + r ^ 2) ^ 2
/-- `2 F_{xp} g^{pp} F_{xp}`, reduced to the common denominator. -/
theorem Txx_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Fxp * ipp * Fxp)) (⟨Txx_n4, Txx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Txx_n4, Txx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g_{xx} F_{αβ} F^{αβ} = g_{xx} (𝓑² − E²)` over the common denominator. -/
def Txx_n5 : ZExp 5 := q ^ 2 * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^ 2 * x ^ 2 - 2 * a * r * x - r ^
    2) * (a ^ 2 * x ^ 2 + 2 * a * r * x - r ^ 2)
/-- `½ g_{xx} F_{αβ} F^{αβ} = g_{xx} (𝓑² − E²)`, reduced to the common denominator. -/
theorem Txx_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (gxx * (Bf * Bf - Ef * Ef)) (⟨Txx_n5, Txx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Ef, Bf, En, Bn, Txx_n5, Txx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- `T_{xx}`: the signed sum of its terms is `Kf * ⟨Sg, sx⟩`. -/
theorem stress_xx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Txx_n1 - Txx_n2 - Txx_n3 + Txx_n4 - Txx_n5, Txx_cd⟩) (Kf * ⟨Sg, sx⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Txx_n1, Txx_n2, Txx_n3, Txx_n4, Txx_n5, Txx_cd, Kf, Sg, sx, Pp, Dl, δr_0,
        δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ### The entry `T_{xp}` -/

/-- The common denominator of the terms of `T_{xp}`. -/
def Txp_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `2 F_{vx} g^{vr} F_{rp}` over the common denominator. -/
def Txp_n1 : ZExp 5 := 4 * a ^ 3 * q ^ 2 * r * x * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a * x -
    r) * (a * x + r)
/-- `2 F_{vx} g^{vr} F_{rp}`, reduced to the common denominator. -/
theorem Txp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Fvx * ivr * Frp)) (⟨Txp_n1, Txp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Txp_n1, Txp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `2 F_{xp} g^{pr} F_{rp}` over the common denominator. -/
def Txp_n2 : ZExp 5 := 4 * a ^ 3 * q ^ 2 * r * x * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a * x -
    r) * (a * x + r)
/-- `2 F_{xp} g^{pr} F_{rp}`, reduced to the common denominator. -/
theorem Txp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Fxp * irp * Frp)) (⟨Txp_n2, Txp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Txp_n2, Txp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- `T_{xp}`: the signed sum of its terms is `Frac.ofZ 0`. -/
theorem stress_xp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Txp_n1 - Txp_n2, Txp_cd⟩) (Frac.ofZ 0))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Txp_n1, Txp_n2, Txp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-! ### The entry `T_{pp}` -/

/-- The common denominator of the terms of `T_{pp}`. -/
def Tpp_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 5

/-- The numerator of `2 F_{rp} g^{rr} F_{rp}` over the common denominator. -/
def Tpp_n1 : ZExp 5 := 2 * a ^ 2 * q ^ 2 * (x - 1) ^ 2 * (x + 1) ^ 2 * (a * x - r) ^ 2 * (a * x +
    r) ^ 2 * (a ^ 2 - 2 * m * r + q ^ 2 + r ^ 2)
/-- `2 F_{rp} g^{rr} F_{rp}`, reduced to the common denominator. -/
theorem Tpp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Frp * irr * Frp)) (⟨Tpp_n1, Tpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Tpp_n1, Tpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `2 F_{xp} g^{xx} F_{xp}` over the common denominator. -/
def Tpp_n2 : ZExp 5 := -8 * a ^ 2 * q ^ 2 * r ^ 2 * x ^ 2 * (a ^ 2 + r ^ 2) ^ 2 * (x - 1) * (x + 1)
/-- `2 F_{xp} g^{xx} F_{xp}`, reduced to the common denominator. -/
theorem Tpp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.ofZ 2 * (Fxp * ixx * Fxp)) (⟨Tpp_n2, Tpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Fvr, Fvx, Frp, Fxp, En, Bn, Tpp_n2, Tpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g_{pp} F_{αβ} F^{αβ} = g_{pp} (𝓑² − E²)` over the common denominator. -/
def Tpp_n3 : ZExp 5 := q ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 - 2 * a * r * x - r ^ 2) * (a ^ 2
    * x ^ 2 + 2 * a * r * x - r ^ 2) * (a ^ 4 * x ^ 2 - 2 * a ^ 2 * m * r * x ^ 2 + 2 * a ^ 2 * m *
    r + a ^ 2 * q ^ 2 * x ^ 2 - a ^ 2 * q ^ 2 + a ^ 2 * r ^ 2 * x ^ 2 + a ^ 2 * r ^ 2 + r ^ 4)
/-- `½ g_{pp} F_{αβ} F^{αβ} = g_{pp} (𝓑² − E²)`, reduced to the common denominator. -/
theorem Tpp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (gpp * (Bf * Bf - Ef * Ef)) (⟨Tpp_n3, Tpp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Ef, Bf, En, Bn, Tpp_n3, Tpp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3,
        δx_4]
    ring)

/-- `T_{pp}`: the signed sum of its terms is `Kf * ⟨sx * (Dl * a ^ 2 * sx + Pp ^ 2), Sg⟩`. -/
theorem stress_pp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Tpp_n1 + Tpp_n2 - Tpp_n3, Tpp_cd⟩) (Kf * ⟨sx * (Dl * a ^ 2 * sx + Pp ^
          2), Sg⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Tpp_n1, Tpp_n2, Tpp_n3, Tpp_cd, Kf, Sg, sx, Pp, Dl, δr_0, δr_1, δr_2, δr_3,
        δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

end LeanProofs.IPRA.Geometry.KerrNewmanIngoingMaxwell
