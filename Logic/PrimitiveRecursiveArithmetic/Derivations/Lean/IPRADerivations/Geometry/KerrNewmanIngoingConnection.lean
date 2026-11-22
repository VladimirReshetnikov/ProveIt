import IPRADerivations.Foundations.FormalDerivation

/-!
# The connection of the Kerr–Newman metric in the ingoing chart (`four_metrics_ipra`)

Packet: `geometry/four_metrics_ipra_2026-11-15`, Section "A rational atlas across radial and
polar coordinate poles", `prop:regular` ("Field equations at `Δ = 0`": "The metric and
potential `eq:ingoing` satisfy Einstein–Maxwell whenever `Σ s ≠ 0`, including at `Δ = 0`"),
by the direct proof: "One direct proof recomputes `eq:gamma`–`eq:maxwell` with
`eq:ingoing`–`eq:ingoinginv`". This module is the first third: the inverse and the connection.
`Geometry/KerrNewmanIngoingRicci` computes the Ricci tensor and
`Geometry/KerrNewmanIngoingMaxwell` the field and the stress tensor.

In the coordinates `(v, r, x, ψ)` (the index `p` stands for `ψ`), with `Σ = r² + a² x²`,
`s = 1 − x²`, `P = r² + a²`, `Δ = r² − 2mr + a² + q²`, the metric `eq:ingoing`,
`g₊ = −(Δ/Σ) p₊² + 2 p₊ dr + (Σ/s) dx² + (s/Σ) b₊²` with `p₊ = dv − a s dψ`,
`b₊ = P dψ − a dv`, has the entries

`g_vv = (−Δ + a² s)/Σ`, `g_vr = 1`, `g_vψ = −a s (P − Δ)/Σ`, `g_rψ = −a s`,
`g_ψψ = s (P² − a² Δ s)/Σ`, `g_xx = Σ/s`, `g_rr = 0`,

and the inverse `eq:ingoinginv` is `Σ g⁻¹ = [[a² s, P, 0, a], [P, Δ, 0, a], [0, 0, s, 0],
[a, a, 0, 1/s]]` (`inverse_vv`, …, `inverse_pp`: the ten products with a nonvanishing term, as
identities of fractions). The coefficients do not depend on `v` and `ψ`, so `∂_v = ∂_ψ = 0`,
and `∂_r`, `∂_x` are the formal derivations `δr`, `δx` of `Foundations/FormalDerivation`
(`Δ` is a polynomial, so no indeterminate derivative occurs).

**The connection** (`eq:gamma`):
`Γ^λ_{μν} = ½ Σ_ρ g^{λρ} (∂_μ g_{ρν} + ∂_ν g_{ρμ} − ∂_ρ g_{μν})`. For each coefficient
`Γ^λ_{μν}` (`μ ≤ ν` in the order `v, r, x, ψ`) with at least one term that is not a derivative
along `v` or `ψ` and not a derivative of an entry that is `0`:

* `Gλ_μν` is its reduced fraction and `Gλ_μν_cd` a common denominator of its terms;
* `Gλ_μν_tk`: the `k`-th such term `½ g^{λρ} ∂_σ g_{αβ}`, with the derivative taken by
  `Foundations/FormalDerivation`, equals the numerator `Gλ_μν_nk` over the common denominator
  (terms whose derivative is `0`, such as `∂_r g_vr`, are included with numerator `0`);
* `christoffel_λ_μν`: the signed sum of these numerators over the common denominator is the
  reduced fraction (the sign of each term is its sign in `eq:gamma`).

Twenty-nine coefficients are nonzero; eight more (`Γ^v_{vr}`, `Γ^v_{rr}`, `Γ^r_{vx}`,
`Γ^r_{rr}`, `Γ^r_{xψ}`, `Γ^x_{vr}`, `Γ^ψ_{vr}`, `Γ^ψ_{rr}`) have terms that cancel, and the
remaining three have no term.

**No denominator contains `Δ`.** Every denominator in this module and in the two modules that
follow is a product of `2`, `Σ` and `s` (checked by the generating script for each common
denominator). So the reading of the cleared identities as equalities of rational functions
needs only `Σ s ≠ 0`: this is the content of `prop:regular`, "including at `Δ = 0`".

The reduced fractions and the numerators were proposed by a computer algebra script; every
identity is checked by Lean as an identity of fractions cleared of denominators, a closed
sentence of iPRA certified in every commutative ring.
-/

namespace LeanProofs.IPRA.Geometry.KerrNewmanIngoingConnection

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ZExp

local notation "r" => (ZExp.var 0 : ZExp 5)
local notation "x" => (ZExp.var 1 : ZExp 5)
local notation "a" => (ZExp.var 2 : ZExp 5)
local notation "m" => (ZExp.var 3 : ZExp 5)
local notation "q" => (ZExp.var 4 : ZExp 5)

/-- `∂_r`: `r ↦ 1`, and `0` on the other variables. -/
def δr : Fin 5 → ZExp 5
  | ⟨0, _⟩ => 1
  | _ => 0

/-- `∂_x`: `x ↦ 1`, and `0` on the other variables. -/
def δx : Fin 5 → ZExp 5
  | ⟨1, _⟩ => 1
  | _ => 0

theorem δr_0 : δr 0 = 1 := rfl
theorem δr_1 : δr 1 = 0 := rfl
theorem δr_2 : δr 2 = 0 := rfl
theorem δr_3 : δr 3 = 0 := rfl
theorem δr_4 : δr 4 = 0 := rfl
theorem δx_0 : δx 0 = 0 := rfl
theorem δx_1 : δx 1 = 1 := rfl
theorem δx_2 : δx 2 = 0 := rfl
theorem δx_3 : δx 3 = 0 := rfl
theorem δx_4 : δx 4 = 0 := rfl

/-- `Σ = r² + a² x²`. -/
def Sg : ZExp 5 := r ^ 2 + a ^ 2 * x ^ 2
/-- `s = 1 − x²`. -/
def sx : ZExp 5 := 1 - x ^ 2
/-- `P = r² + a²`. -/
def Pp : ZExp 5 := r ^ 2 + a ^ 2
/-- `Δ = r² − 2mr + a² + q²`. -/
def Dl : ZExp 5 := r ^ 2 - 2 * m * r + a ^ 2 + q ^ 2

/-! ## The metric `eq:ingoing` and the matrix `eq:ingoinginv` -/

/-- `g_vv = (−Δ + a² s)/Σ`. -/
def gvv : Frac 5 := ⟨-Dl + a ^ 2 * sx, Sg⟩
/-- `g_vr = 1`. -/
def gvr : Frac 5 := ⟨1, 1⟩
/-- `g_vψ = −a s (P − Δ)/Σ`. -/
def gvp : Frac 5 := ⟨-(a * sx * (Pp - Dl)), Sg⟩
/-- `g_rψ = −a s`. -/
def grp : Frac 5 := ⟨-(a * sx), 1⟩
/-- `g_ψψ = s (P² − a² Δ s)/Σ`. -/
def gpp : Frac 5 := ⟨sx * (Pp ^ 2 - a ^ 2 * Dl * sx), Sg⟩
/-- `g_xx = Σ/s`. -/
def gxx : Frac 5 := ⟨Sg, sx⟩
/-- `g^vv = a² s/Σ`. -/
def ivv : Frac 5 := ⟨a ^ 2 * sx, Sg⟩
/-- `g^vr = P/Σ`. -/
def ivr : Frac 5 := ⟨Pp, Sg⟩
/-- `g^vψ = a/Σ`. -/
def ivp : Frac 5 := ⟨a, Sg⟩
/-- `g^rr = Δ/Σ`. -/
def irr : Frac 5 := ⟨Dl, Sg⟩
/-- `g^rψ = a/Σ`. -/
def irp : Frac 5 := ⟨a, Sg⟩
/-- `g^xx = s/Σ`. -/
def ixx : Frac 5 := ⟨sx, Sg⟩
/-- `g^ψψ = 1/(s Σ)`. -/
def ipp : Frac 5 := ⟨1, sx * Sg⟩

/-- `K = q²/Σ²`, the common factor of the Ricci tensor and of the stress tensor. -/
def Kf : Frac 5 := ⟨q ^ 2, Sg ^ 2⟩

/-! ## The inverse `eq:ingoinginv` -/

/-- `(g g⁻¹)_v^v = 1`. -/
theorem inverse_vv :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (gvv * ivv + gvr * ivr + gvp * ivp) (Frac.ofZ 1))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `(g g⁻¹)_v^r = 0`. -/
theorem inverse_vr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (gvv * ivr + gvr * irr + gvp * irp) (Frac.ofZ 0))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `(g g⁻¹)_v^p = 0`. -/
theorem inverse_vp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (gvv * ivp + gvr * irp + gvp * ipp) (Frac.ofZ 0))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `(g g⁻¹)_r^v = 0`. -/
theorem inverse_rv :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (gvr * ivv + grp * ivp) (Frac.ofZ 0))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `(g g⁻¹)_r^r = 1`. -/
theorem inverse_rr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (gvr * ivr + grp * irp) (Frac.ofZ 1))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `(g g⁻¹)_r^p = 0`. -/
theorem inverse_rp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (gvr * ivp + grp * ipp) (Frac.ofZ 0))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `(g g⁻¹)_x^x = 1`. -/
theorem inverse_xx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (gxx * ixx) (Frac.ofZ 1))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `(g g⁻¹)_p^v = 0`. -/
theorem inverse_pv :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (gvp * ivv + grp * ivr + gpp * ivp) (Frac.ofZ 0))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `(g g⁻¹)_p^r = 0`. -/
theorem inverse_pr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (gvp * ivr + grp * irr + gpp * irp) (Frac.ofZ 0))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `(g g⁻¹)_p^p = 1`. -/
theorem inverse_pp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (gvp * ivp + grp * irp + gpp * ipp) (Frac.ofZ 1))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ## The connection coefficients `eq:gamma` -/

/-! ### `Γ^v_{vv}` -/

/-- `Γ^v_{vv}`, reduced. -/
def Gv_vv : Frac 5 := ⟨-(a ^ 2 + r ^ 2) * (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^ 2 * r), (a ^ 2 * x ^
    2 + r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `Γ^v_{vv}`. -/
def Gv_vv_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 3

/-- The numerator of `½ g^{vr} ∂_r g_{vv}` over the common denominator. -/
def Gv_vv_n1 : ZExp 5 := (a ^ 2 + r ^ 2) * (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^ 2 * r)
/-- `½ g^{vr} ∂_r g_{vv}`, reduced to the common denominator. -/
theorem Gv_vv_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivr * Frac.d δr gvv)) (⟨Gv_vv_n1, Gv_vv_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gv_vv_n1, Gv_vv_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `Γ^v_{vv}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_v_vv :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨0 - Gv_vv_n1, Gv_vv_cd⟩) (Gv_vv))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_vv_n1, Gv_vv_cd, Gv_vv, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-! ### `Γ^v_{vr}` -/

/-- `Γ^v_{vr}`, reduced. -/
def Gv_vr : Frac 5 := ⟨0, 1⟩

/-- The common denominator of the terms of `Γ^v_{vr}`. -/
def Gv_vr_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 3

/-- The numerator of `½ g^{vv} ∂_r g_{vv}` over the common denominator. -/
def Gv_vr_n1 : ZExp 5 := -a ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^ 2 * r)
/-- `½ g^{vv} ∂_r g_{vv}`, reduced to the common denominator. -/
theorem Gv_vr_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivv * Frac.d δr gvv)) (⟨Gv_vr_n1, Gv_vr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gv_vr_n1, Gv_vr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{vr} ∂_r g_{rv}` over the common denominator. -/
def Gv_vr_n2 : ZExp 5 := 0
/-- `½ g^{vr} ∂_r g_{rv}`, reduced to the common denominator. -/
theorem Gv_vr_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivr * Frac.d δr gvr)) (⟨Gv_vr_n2, Gv_vr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gv_vr_n2, Gv_vr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{vr} ∂_r g_{vr}` over the common denominator. -/
def Gv_vr_n3 : ZExp 5 := 0
/-- `½ g^{vr} ∂_r g_{vr}`, reduced to the common denominator. -/
theorem Gv_vr_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivr * Frac.d δr gvr)) (⟨Gv_vr_n3, Gv_vr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gv_vr_n3, Gv_vr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{vp} ∂_r g_{pv}` over the common denominator. -/
def Gv_vr_n4 : ZExp 5 := a ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^ 2 * r)
/-- `½ g^{vp} ∂_r g_{pv}`, reduced to the common denominator. -/
theorem Gv_vr_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivp * Frac.d δr gvp)) (⟨Gv_vr_n4, Gv_vr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gv_vr_n4, Gv_vr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `Γ^v_{vr}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_v_vr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Gv_vr_n1 + Gv_vr_n2 - Gv_vr_n3 + Gv_vr_n4, Gv_vr_cd⟩) (Gv_vr))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_vr_n1, Gv_vr_n2, Gv_vr_n3, Gv_vr_n4, Gv_vr_cd, Gv_vr, δr_0, δr_1, δr_2,
        δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ### `Γ^v_{vx}` -/

/-- `Γ^v_{vx}`, reduced. -/
def Gv_vx : Frac 5 := ⟨-a ^ 2 * x * (-2 * m * r + q ^ 2), (a ^ 2 * x ^ 2 + r ^ 2) ^ 2⟩

/-- The common denominator of the terms of `Γ^v_{vx}`. -/
def Gv_vx_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 3

/-- The numerator of `½ g^{vv} ∂_x g_{vv}` over the common denominator. -/
def Gv_vx_n1 : ZExp 5 := -a ^ 4 * x * (x - 1) * (x + 1) * (-2 * m * r + q ^ 2)
/-- `½ g^{vv} ∂_x g_{vv}`, reduced to the common denominator. -/
theorem Gv_vx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivv * Frac.d δx gvv)) (⟨Gv_vx_n1, Gv_vx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gv_vx_n1, Gv_vx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{vr} ∂_x g_{rv}` over the common denominator. -/
def Gv_vx_n2 : ZExp 5 := 0
/-- `½ g^{vr} ∂_x g_{rv}`, reduced to the common denominator. -/
theorem Gv_vx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivr * Frac.d δx gvr)) (⟨Gv_vx_n2, Gv_vx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gv_vx_n2, Gv_vx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{vp} ∂_x g_{pv}` over the common denominator. -/
def Gv_vx_n3 : ZExp 5 := -a ^ 2 * x * (a ^ 2 + r ^ 2) * (-2 * m * r + q ^ 2)
/-- `½ g^{vp} ∂_x g_{pv}`, reduced to the common denominator. -/
theorem Gv_vx_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivp * Frac.d δx gvp)) (⟨Gv_vx_n3, Gv_vx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gv_vx_n3, Gv_vx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `Γ^v_{vx}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_v_vx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Gv_vx_n1 + Gv_vx_n2 + Gv_vx_n3, Gv_vx_cd⟩) (Gv_vx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_vx_n1, Gv_vx_n2, Gv_vx_n3, Gv_vx_cd, Gv_vx, δr_0, δr_1, δr_2, δr_3, δr_4,
        δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ### `Γ^v_{vp}` -/

/-- `Γ^v_{vp}`, reduced. -/
def Gv_vp : Frac 5 := ⟨-a * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 * m * x ^ 2 - m * r ^ 2 +
    q ^ 2 * r), (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `Γ^v_{vp}`. -/
def Gv_vp_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 3

/-- The numerator of `½ g^{vr} ∂_r g_{vp}` over the common denominator. -/
def Gv_vp_n1 : ZExp 5 := a * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 * m * x ^ 2 - m * r ^ 2 +
    q ^ 2 * r)
/-- `½ g^{vr} ∂_r g_{vp}`, reduced to the common denominator. -/
theorem Gv_vp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivr * Frac.d δr gvp)) (⟨Gv_vp_n1, Gv_vp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gv_vp_n1, Gv_vp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `Γ^v_{vp}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_v_vp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨0 - Gv_vp_n1, Gv_vp_cd⟩) (Gv_vp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_vp_n1, Gv_vp_cd, Gv_vp, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-! ### `Γ^v_{rr}` -/

/-- `Γ^v_{rr}`, reduced. -/
def Gv_rr : Frac 5 := ⟨0, 1⟩

/-- The common denominator of the terms of `Γ^v_{rr}`. -/
def Gv_rr_cd : ZExp 5 := 1

/-- The numerator of `½ g^{vv} ∂_r g_{vr}` over the common denominator. -/
def Gv_rr_n1 : ZExp 5 := 0
/-- `½ g^{vv} ∂_r g_{vr}`, reduced to the common denominator. -/
theorem Gv_rr_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivv * Frac.d δr gvr)) (⟨Gv_rr_n1, Gv_rr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gv_rr_n1, Gv_rr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{vv} ∂_r g_{vr}` over the common denominator. -/
def Gv_rr_n2 : ZExp 5 := 0
/-- `½ g^{vv} ∂_r g_{vr}`, reduced to the common denominator. -/
theorem Gv_rr_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivv * Frac.d δr gvr)) (⟨Gv_rr_n2, Gv_rr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gv_rr_n2, Gv_rr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{vp} ∂_r g_{pr}` over the common denominator. -/
def Gv_rr_n3 : ZExp 5 := 0
/-- `½ g^{vp} ∂_r g_{pr}`, reduced to the common denominator. -/
theorem Gv_rr_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivp * Frac.d δr grp)) (⟨Gv_rr_n3, Gv_rr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gv_rr_n3, Gv_rr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{vp} ∂_r g_{pr}` over the common denominator. -/
def Gv_rr_n4 : ZExp 5 := 0
/-- `½ g^{vp} ∂_r g_{pr}`, reduced to the common denominator. -/
theorem Gv_rr_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivp * Frac.d δr grp)) (⟨Gv_rr_n4, Gv_rr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gv_rr_n4, Gv_rr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `Γ^v_{rr}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_v_rr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Gv_rr_n1 + Gv_rr_n2 + Gv_rr_n3 + Gv_rr_n4, Gv_rr_cd⟩) (Gv_rr))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_rr_n1, Gv_rr_n2, Gv_rr_n3, Gv_rr_n4, Gv_rr_cd, Gv_rr, δr_0, δr_1, δr_2,
        δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ### `Γ^v_{rx}` -/

/-- `Γ^v_{rx}`, reduced. -/
def Gv_rx : Frac 5 := ⟨a ^ 2 * x, a ^ 2 * x ^ 2 + r ^ 2⟩

/-- The common denominator of the terms of `Γ^v_{rx}`. -/
def Gv_rx_cd : ZExp 5 := a ^ 2 * x ^ 2 + r ^ 2

/-- The numerator of `½ g^{vv} ∂_x g_{vr}` over the common denominator. -/
def Gv_rx_n1 : ZExp 5 := 0
/-- `½ g^{vv} ∂_x g_{vr}`, reduced to the common denominator. -/
theorem Gv_rx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivv * Frac.d δx gvr)) (⟨Gv_rx_n1, Gv_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gv_rx_n1, Gv_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{vp} ∂_x g_{pr}` over the common denominator. -/
def Gv_rx_n2 : ZExp 5 := a ^ 2 * x
/-- `½ g^{vp} ∂_x g_{pr}`, reduced to the common denominator. -/
theorem Gv_rx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivp * Frac.d δx grp)) (⟨Gv_rx_n2, Gv_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gv_rx_n2, Gv_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `Γ^v_{rx}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_v_rx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Gv_rx_n1 + Gv_rx_n2, Gv_rx_cd⟩) (Gv_rx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_rx_n1, Gv_rx_n2, Gv_rx_cd, Gv_rx, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-! ### `Γ^v_{rp}` -/

/-- `Γ^v_{rp}`, reduced. -/
def Gv_rp : Frac 5 := ⟨-a * r * (x - 1) * (x + 1), a ^ 2 * x ^ 2 + r ^ 2⟩

/-- The common denominator of the terms of `Γ^v_{rp}`. -/
def Gv_rp_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 3

/-- The numerator of `½ g^{vv} ∂_r g_{vp}` over the common denominator. -/
def Gv_rp_n1 : ZExp 5 := -a ^ 3 * (x - 1) ^ 2 * (x + 1) ^ 2 * (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^
    2 * r)
/-- `½ g^{vv} ∂_r g_{vp}`, reduced to the common denominator. -/
theorem Gv_rp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivv * Frac.d δr gvp)) (⟨Gv_rp_n1, Gv_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gv_rp_n1, Gv_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{vr} ∂_r g_{rp}` over the common denominator. -/
def Gv_rp_n2 : ZExp 5 := 0
/-- `½ g^{vr} ∂_r g_{rp}`, reduced to the common denominator. -/
theorem Gv_rp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivr * Frac.d δr grp)) (⟨Gv_rp_n2, Gv_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gv_rp_n2, Gv_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{vr} ∂_r g_{rp}` over the common denominator. -/
def Gv_rp_n3 : ZExp 5 := 0
/-- `½ g^{vr} ∂_r g_{rp}`, reduced to the common denominator. -/
theorem Gv_rp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivr * Frac.d δr grp)) (⟨Gv_rp_n3, Gv_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gv_rp_n3, Gv_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{vp} ∂_r g_{pp}` over the common denominator. -/
def Gv_rp_n4 : ZExp 5 := -a * (x - 1) * (x + 1) * (-a ^ 4 * m * x ^ 4 + a ^ 4 * m * x ^ 2 + a ^ 4 *
    r * x ^ 4 + a ^ 2 * m * r ^ 2 * x ^ 2 - a ^ 2 * m * r ^ 2 - a ^ 2 * q ^ 2 * r * x ^ 2 + a ^ 2 *
    q ^ 2 * r + 2 * a ^ 2 * r ^ 3 * x ^ 2 + r ^ 5)
/-- `½ g^{vp} ∂_r g_{pp}`, reduced to the common denominator. -/
theorem Gv_rp_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivp * Frac.d δr gpp)) (⟨Gv_rp_n4, Gv_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gv_rp_n4, Gv_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `Γ^v_{rp}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_v_rp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Gv_rp_n1 + Gv_rp_n2 - Gv_rp_n3 + Gv_rp_n4, Gv_rp_cd⟩) (Gv_rp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_rp_n1, Gv_rp_n2, Gv_rp_n3, Gv_rp_n4, Gv_rp_cd, Gv_rp, δr_0, δr_1, δr_2,
        δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ### `Γ^v_{xx}` -/

/-- `Γ^v_{xx}`, reduced. -/
def Gv_xx : Frac 5 := ⟨r * (a ^ 2 + r ^ 2), (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2)⟩

/-- The common denominator of the terms of `Γ^v_{xx}`. -/
def Gv_xx_cd : ZExp 5 := (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2)

/-- The numerator of `½ g^{vr} ∂_r g_{xx}` over the common denominator. -/
def Gv_xx_n1 : ZExp 5 := -r * (a ^ 2 + r ^ 2)
/-- `½ g^{vr} ∂_r g_{xx}`, reduced to the common denominator. -/
theorem Gv_xx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivr * Frac.d δr gxx)) (⟨Gv_xx_n1, Gv_xx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gv_xx_n1, Gv_xx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `Γ^v_{xx}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_v_xx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨0 - Gv_xx_n1, Gv_xx_cd⟩) (Gv_xx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_xx_n1, Gv_xx_cd, Gv_xx, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-! ### `Γ^v_{xp}` -/

/-- `Γ^v_{xp}`, reduced. -/
def Gv_xp : Frac 5 := ⟨-a ^ 3 * x * (x - 1) * (x + 1) * (-2 * m * r + q ^ 2), (a ^ 2 * x ^ 2 + r ^
    2) ^ 2⟩

/-- The common denominator of the terms of `Γ^v_{xp}`. -/
def Gv_xp_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 3

/-- The numerator of `½ g^{vv} ∂_x g_{vp}` over the common denominator. -/
def Gv_xp_n1 : ZExp 5 := a ^ 3 * x * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (-2 * m * r + q ^ 2)
/-- `½ g^{vv} ∂_x g_{vp}`, reduced to the common denominator. -/
theorem Gv_xp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivv * Frac.d δx gvp)) (⟨Gv_xp_n1, Gv_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gv_xp_n1, Gv_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{vr} ∂_x g_{rp}` over the common denominator. -/
def Gv_xp_n2 : ZExp 5 := a * x * (a ^ 2 + r ^ 2) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `½ g^{vr} ∂_x g_{rp}`, reduced to the common denominator. -/
theorem Gv_xp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivr * Frac.d δx grp)) (⟨Gv_xp_n2, Gv_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gv_xp_n2, Gv_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{vp} ∂_x g_{pp}` over the common denominator. -/
def Gv_xp_n3 : ZExp 5 := -a * x * (a ^ 6 * x ^ 4 - 2 * a ^ 4 * m * r * x ^ 4 + 2 * a ^ 4 * m * r +
    a ^ 4 * q ^ 2 * x ^ 4 - a ^ 4 * q ^ 2 + a ^ 4 * r ^ 2 * x ^ 4 + 2 * a ^ 4 * r ^ 2 * x ^ 2 - 4 *
    a ^ 2 * m * r ^ 3 * x ^ 2 + 4 * a ^ 2 * m * r ^ 3 + 2 * a ^ 2 * q ^ 2 * r ^ 2 * x ^ 2 - 2 * a ^
    2 * q ^ 2 * r ^ 2 + 2 * a ^ 2 * r ^ 4 * x ^ 2 + a ^ 2 * r ^ 4 + r ^ 6)
/-- `½ g^{vp} ∂_x g_{pp}`, reduced to the common denominator. -/
theorem Gv_xp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivp * Frac.d δx gpp)) (⟨Gv_xp_n3, Gv_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gv_xp_n3, Gv_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `Γ^v_{xp}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_v_xp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Gv_xp_n1 + Gv_xp_n2 + Gv_xp_n3, Gv_xp_cd⟩) (Gv_xp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_xp_n1, Gv_xp_n2, Gv_xp_n3, Gv_xp_cd, Gv_xp, δr_0, δr_1, δr_2, δr_3, δr_4,
        δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ### `Γ^v_{pp}` -/

/-- `Γ^v_{pp}`, reduced. -/
def Gv_pp : Frac 5 := ⟨(a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (-a ^ 4 * m * x ^ 4 + a ^ 4 * m * x ^
    2 + a ^ 4 * r * x ^ 4 + a ^ 2 * m * r ^ 2 * x ^ 2 - a ^ 2 * m * r ^ 2 - a ^ 2 * q ^ 2 * r * x ^
    2 + a ^ 2 * q ^ 2 * r + 2 * a ^ 2 * r ^ 3 * x ^ 2 + r ^ 5), (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `Γ^v_{pp}`. -/
def Gv_pp_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 3

/-- The numerator of `½ g^{vr} ∂_r g_{pp}` over the common denominator. -/
def Gv_pp_n1 : ZExp 5 := -(a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (-a ^ 4 * m * x ^ 4 + a ^ 4 * m * x
    ^ 2 + a ^ 4 * r * x ^ 4 + a ^ 2 * m * r ^ 2 * x ^ 2 - a ^ 2 * m * r ^ 2 - a ^ 2 * q ^ 2 * r * x
    ^ 2 + a ^ 2 * q ^ 2 * r + 2 * a ^ 2 * r ^ 3 * x ^ 2 + r ^ 5)
/-- `½ g^{vr} ∂_r g_{pp}`, reduced to the common denominator. -/
theorem Gv_pp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivr * Frac.d δr gpp)) (⟨Gv_pp_n1, Gv_pp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gv_pp_n1, Gv_pp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `Γ^v_{pp}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_v_pp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨0 - Gv_pp_n1, Gv_pp_cd⟩) (Gv_pp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gv_pp_n1, Gv_pp_cd, Gv_pp, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-! ### `Γ^r_{vv}` -/

/-- `Γ^r_{vv}`, reduced. -/
def Gr_vv : Frac 5 := ⟨-(a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^ 2 * r) * (a ^ 2 - 2 * m * r + q ^ 2 +
    r ^ 2), (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `Γ^r_{vv}`. -/
def Gr_vv_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 3

/-- The numerator of `½ g^{rr} ∂_r g_{vv}` over the common denominator. -/
def Gr_vv_n1 : ZExp 5 := (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^ 2 * r) * (a ^ 2 - 2 * m * r + q ^ 2 +
    r ^ 2)
/-- `½ g^{rr} ∂_r g_{vv}`, reduced to the common denominator. -/
theorem Gr_vv_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (irr * Frac.d δr gvv)) (⟨Gr_vv_n1, Gr_vv_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gr_vv_n1, Gr_vv_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `Γ^r_{vv}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_r_vv :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨0 - Gr_vv_n1, Gr_vv_cd⟩) (Gr_vv))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_vv_n1, Gr_vv_cd, Gr_vv, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-! ### `Γ^r_{vr}` -/

/-- `Γ^r_{vr}`, reduced. -/
def Gr_vr : Frac 5 := ⟨a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^ 2 * r, (a ^ 2 * x ^ 2 + r ^ 2) ^ 2⟩

/-- The common denominator of the terms of `Γ^r_{vr}`. -/
def Gr_vr_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 3

/-- The numerator of `½ g^{rv} ∂_r g_{vv}` over the common denominator. -/
def Gr_vr_n1 : ZExp 5 := (a ^ 2 + r ^ 2) * (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^ 2 * r)
/-- `½ g^{rv} ∂_r g_{vv}`, reduced to the common denominator. -/
theorem Gr_vr_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivr * Frac.d δr gvv)) (⟨Gr_vr_n1, Gr_vr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gr_vr_n1, Gr_vr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{rr} ∂_r g_{rv}` over the common denominator. -/
def Gr_vr_n2 : ZExp 5 := 0
/-- `½ g^{rr} ∂_r g_{rv}`, reduced to the common denominator. -/
theorem Gr_vr_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (irr * Frac.d δr gvr)) (⟨Gr_vr_n2, Gr_vr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gr_vr_n2, Gr_vr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{rr} ∂_r g_{vr}` over the common denominator. -/
def Gr_vr_n3 : ZExp 5 := 0
/-- `½ g^{rr} ∂_r g_{vr}`, reduced to the common denominator. -/
theorem Gr_vr_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (irr * Frac.d δr gvr)) (⟨Gr_vr_n3, Gr_vr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gr_vr_n3, Gr_vr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{rp} ∂_r g_{pv}` over the common denominator. -/
def Gr_vr_n4 : ZExp 5 := a ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^ 2 * r)
/-- `½ g^{rp} ∂_r g_{pv}`, reduced to the common denominator. -/
theorem Gr_vr_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (irp * Frac.d δr gvp)) (⟨Gr_vr_n4, Gr_vr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gr_vr_n4, Gr_vr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `Γ^r_{vr}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_r_vr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Gr_vr_n1 + Gr_vr_n2 - Gr_vr_n3 + Gr_vr_n4, Gr_vr_cd⟩) (Gr_vr))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_vr_n1, Gr_vr_n2, Gr_vr_n3, Gr_vr_n4, Gr_vr_cd, Gr_vr, δr_0, δr_1, δr_2,
        δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ### `Γ^r_{vx}` -/

/-- `Γ^r_{vx}`, reduced. -/
def Gr_vx : Frac 5 := ⟨0, 1⟩

/-- The common denominator of the terms of `Γ^r_{vx}`. -/
def Gr_vx_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 3

/-- The numerator of `½ g^{rv} ∂_x g_{vv}` over the common denominator. -/
def Gr_vx_n1 : ZExp 5 := a ^ 2 * x * (a ^ 2 + r ^ 2) * (-2 * m * r + q ^ 2)
/-- `½ g^{rv} ∂_x g_{vv}`, reduced to the common denominator. -/
theorem Gr_vx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivr * Frac.d δx gvv)) (⟨Gr_vx_n1, Gr_vx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gr_vx_n1, Gr_vx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{rr} ∂_x g_{rv}` over the common denominator. -/
def Gr_vx_n2 : ZExp 5 := 0
/-- `½ g^{rr} ∂_x g_{rv}`, reduced to the common denominator. -/
theorem Gr_vx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (irr * Frac.d δx gvr)) (⟨Gr_vx_n2, Gr_vx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gr_vx_n2, Gr_vx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{rp} ∂_x g_{pv}` over the common denominator. -/
def Gr_vx_n3 : ZExp 5 := -a ^ 2 * x * (a ^ 2 + r ^ 2) * (-2 * m * r + q ^ 2)
/-- `½ g^{rp} ∂_x g_{pv}`, reduced to the common denominator. -/
theorem Gr_vx_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (irp * Frac.d δx gvp)) (⟨Gr_vx_n3, Gr_vx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gr_vx_n3, Gr_vx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `Γ^r_{vx}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_r_vx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Gr_vx_n1 + Gr_vx_n2 + Gr_vx_n3, Gr_vx_cd⟩) (Gr_vx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_vx_n1, Gr_vx_n2, Gr_vx_n3, Gr_vx_cd, Gr_vx, δr_0, δr_1, δr_2, δr_3, δr_4,
        δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ### `Γ^r_{vp}` -/

/-- `Γ^r_{vp}`, reduced. -/
def Gr_vp : Frac 5 := ⟨-a * (x - 1) * (x + 1) * (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^ 2 * r) * (a ^
    2 - 2 * m * r + q ^ 2 + r ^ 2), (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `Γ^r_{vp}`. -/
def Gr_vp_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 3

/-- The numerator of `½ g^{rr} ∂_r g_{vp}` over the common denominator. -/
def Gr_vp_n1 : ZExp 5 := a * (x - 1) * (x + 1) * (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^ 2 * r) * (a ^
    2 - 2 * m * r + q ^ 2 + r ^ 2)
/-- `½ g^{rr} ∂_r g_{vp}`, reduced to the common denominator. -/
theorem Gr_vp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (irr * Frac.d δr gvp)) (⟨Gr_vp_n1, Gr_vp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gr_vp_n1, Gr_vp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `Γ^r_{vp}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_r_vp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨0 - Gr_vp_n1, Gr_vp_cd⟩) (Gr_vp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_vp_n1, Gr_vp_cd, Gr_vp, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-! ### `Γ^r_{rr}` -/

/-- `Γ^r_{rr}`, reduced. -/
def Gr_rr : Frac 5 := ⟨0, 1⟩

/-- The common denominator of the terms of `Γ^r_{rr}`. -/
def Gr_rr_cd : ZExp 5 := 1

/-- The numerator of `½ g^{rv} ∂_r g_{vr}` over the common denominator. -/
def Gr_rr_n1 : ZExp 5 := 0
/-- `½ g^{rv} ∂_r g_{vr}`, reduced to the common denominator. -/
theorem Gr_rr_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivr * Frac.d δr gvr)) (⟨Gr_rr_n1, Gr_rr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gr_rr_n1, Gr_rr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{rv} ∂_r g_{vr}` over the common denominator. -/
def Gr_rr_n2 : ZExp 5 := 0
/-- `½ g^{rv} ∂_r g_{vr}`, reduced to the common denominator. -/
theorem Gr_rr_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivr * Frac.d δr gvr)) (⟨Gr_rr_n2, Gr_rr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gr_rr_n2, Gr_rr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{rp} ∂_r g_{pr}` over the common denominator. -/
def Gr_rr_n3 : ZExp 5 := 0
/-- `½ g^{rp} ∂_r g_{pr}`, reduced to the common denominator. -/
theorem Gr_rr_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (irp * Frac.d δr grp)) (⟨Gr_rr_n3, Gr_rr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gr_rr_n3, Gr_rr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{rp} ∂_r g_{pr}` over the common denominator. -/
def Gr_rr_n4 : ZExp 5 := 0
/-- `½ g^{rp} ∂_r g_{pr}`, reduced to the common denominator. -/
theorem Gr_rr_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (irp * Frac.d δr grp)) (⟨Gr_rr_n4, Gr_rr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gr_rr_n4, Gr_rr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `Γ^r_{rr}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_r_rr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Gr_rr_n1 + Gr_rr_n2 + Gr_rr_n3 + Gr_rr_n4, Gr_rr_cd⟩) (Gr_rr))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rr_n1, Gr_rr_n2, Gr_rr_n3, Gr_rr_n4, Gr_rr_cd, Gr_rr, δr_0, δr_1, δr_2,
        δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ### `Γ^r_{rx}` -/

/-- `Γ^r_{rx}`, reduced. -/
def Gr_rx : Frac 5 := ⟨a ^ 2 * x, a ^ 2 * x ^ 2 + r ^ 2⟩

/-- The common denominator of the terms of `Γ^r_{rx}`. -/
def Gr_rx_cd : ZExp 5 := a ^ 2 * x ^ 2 + r ^ 2

/-- The numerator of `½ g^{rv} ∂_x g_{vr}` over the common denominator. -/
def Gr_rx_n1 : ZExp 5 := 0
/-- `½ g^{rv} ∂_x g_{vr}`, reduced to the common denominator. -/
theorem Gr_rx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivr * Frac.d δx gvr)) (⟨Gr_rx_n1, Gr_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gr_rx_n1, Gr_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{rp} ∂_x g_{pr}` over the common denominator. -/
def Gr_rx_n2 : ZExp 5 := a ^ 2 * x
/-- `½ g^{rp} ∂_x g_{pr}`, reduced to the common denominator. -/
theorem Gr_rx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (irp * Frac.d δx grp)) (⟨Gr_rx_n2, Gr_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gr_rx_n2, Gr_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `Γ^r_{rx}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_r_rx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Gr_rx_n1 + Gr_rx_n2, Gr_rx_cd⟩) (Gr_rx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rx_n1, Gr_rx_n2, Gr_rx_cd, Gr_rx, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-! ### `Γ^r_{rp}` -/

/-- `Γ^r_{rp}`, reduced. -/
def Gr_rp : Frac 5 := ⟨-a * (x - 1) * (x + 1) * (-a ^ 2 * m * x ^ 2 + a ^ 2 * r * x ^ 2 + m * r ^ 2
    - q ^ 2 * r + r ^ 3), (a ^ 2 * x ^ 2 + r ^ 2) ^ 2⟩

/-- The common denominator of the terms of `Γ^r_{rp}`. -/
def Gr_rp_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 3

/-- The numerator of `½ g^{rv} ∂_r g_{vp}` over the common denominator. -/
def Gr_rp_n1 : ZExp 5 := a * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (a ^ 2 * m * x ^ 2 - m * r ^ 2 +
    q ^ 2 * r)
/-- `½ g^{rv} ∂_r g_{vp}`, reduced to the common denominator. -/
theorem Gr_rp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivr * Frac.d δr gvp)) (⟨Gr_rp_n1, Gr_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gr_rp_n1, Gr_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{rr} ∂_r g_{rp}` over the common denominator. -/
def Gr_rp_n2 : ZExp 5 := 0
/-- `½ g^{rr} ∂_r g_{rp}`, reduced to the common denominator. -/
theorem Gr_rp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (irr * Frac.d δr grp)) (⟨Gr_rp_n2, Gr_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gr_rp_n2, Gr_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{rr} ∂_r g_{rp}` over the common denominator. -/
def Gr_rp_n3 : ZExp 5 := 0
/-- `½ g^{rr} ∂_r g_{rp}`, reduced to the common denominator. -/
theorem Gr_rp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (irr * Frac.d δr grp)) (⟨Gr_rp_n3, Gr_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gr_rp_n3, Gr_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{rp} ∂_r g_{pp}` over the common denominator. -/
def Gr_rp_n4 : ZExp 5 := -a * (x - 1) * (x + 1) * (-a ^ 4 * m * x ^ 4 + a ^ 4 * m * x ^ 2 + a ^ 4 *
    r * x ^ 4 + a ^ 2 * m * r ^ 2 * x ^ 2 - a ^ 2 * m * r ^ 2 - a ^ 2 * q ^ 2 * r * x ^ 2 + a ^ 2 *
    q ^ 2 * r + 2 * a ^ 2 * r ^ 3 * x ^ 2 + r ^ 5)
/-- `½ g^{rp} ∂_r g_{pp}`, reduced to the common denominator. -/
theorem Gr_rp_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (irp * Frac.d δr gpp)) (⟨Gr_rp_n4, Gr_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gr_rp_n4, Gr_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `Γ^r_{rp}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_r_rp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Gr_rp_n1 + Gr_rp_n2 - Gr_rp_n3 + Gr_rp_n4, Gr_rp_cd⟩) (Gr_rp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_rp_n1, Gr_rp_n2, Gr_rp_n3, Gr_rp_n4, Gr_rp_cd, Gr_rp, δr_0, δr_1, δr_2,
        δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ### `Γ^r_{xx}` -/

/-- `Γ^r_{xx}`, reduced. -/
def Gr_xx : Frac 5 := ⟨r * (a ^ 2 - 2 * m * r + q ^ 2 + r ^ 2), (x - 1) * (x + 1) * (a ^ 2 * x ^ 2
    + r ^ 2)⟩

/-- The common denominator of the terms of `Γ^r_{xx}`. -/
def Gr_xx_cd : ZExp 5 := (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2)

/-- The numerator of `½ g^{rr} ∂_r g_{xx}` over the common denominator. -/
def Gr_xx_n1 : ZExp 5 := -r * (a ^ 2 - 2 * m * r + q ^ 2 + r ^ 2)
/-- `½ g^{rr} ∂_r g_{xx}`, reduced to the common denominator. -/
theorem Gr_xx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (irr * Frac.d δr gxx)) (⟨Gr_xx_n1, Gr_xx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gr_xx_n1, Gr_xx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `Γ^r_{xx}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_r_xx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨0 - Gr_xx_n1, Gr_xx_cd⟩) (Gr_xx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_xx_n1, Gr_xx_cd, Gr_xx, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-! ### `Γ^r_{xp}` -/

/-- `Γ^r_{xp}`, reduced. -/
def Gr_xp : Frac 5 := ⟨0, 1⟩

/-- The common denominator of the terms of `Γ^r_{xp}`. -/
def Gr_xp_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 3

/-- The numerator of `½ g^{rv} ∂_x g_{vp}` over the common denominator. -/
def Gr_xp_n1 : ZExp 5 := -a * x * (a ^ 2 + r ^ 2) ^ 2 * (-2 * m * r + q ^ 2)
/-- `½ g^{rv} ∂_x g_{vp}`, reduced to the common denominator. -/
theorem Gr_xp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivr * Frac.d δx gvp)) (⟨Gr_xp_n1, Gr_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gr_xp_n1, Gr_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{rr} ∂_x g_{rp}` over the common denominator. -/
def Gr_xp_n2 : ZExp 5 := a * x * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2 * (a ^ 2 - 2 * m * r + q ^ 2 + r ^ 2)
/-- `½ g^{rr} ∂_x g_{rp}`, reduced to the common denominator. -/
theorem Gr_xp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (irr * Frac.d δx grp)) (⟨Gr_xp_n2, Gr_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gr_xp_n2, Gr_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{rp} ∂_x g_{pp}` over the common denominator. -/
def Gr_xp_n3 : ZExp 5 := -a * x * (a ^ 6 * x ^ 4 - 2 * a ^ 4 * m * r * x ^ 4 + 2 * a ^ 4 * m * r +
    a ^ 4 * q ^ 2 * x ^ 4 - a ^ 4 * q ^ 2 + a ^ 4 * r ^ 2 * x ^ 4 + 2 * a ^ 4 * r ^ 2 * x ^ 2 - 4 *
    a ^ 2 * m * r ^ 3 * x ^ 2 + 4 * a ^ 2 * m * r ^ 3 + 2 * a ^ 2 * q ^ 2 * r ^ 2 * x ^ 2 - 2 * a ^
    2 * q ^ 2 * r ^ 2 + 2 * a ^ 2 * r ^ 4 * x ^ 2 + a ^ 2 * r ^ 4 + r ^ 6)
/-- `½ g^{rp} ∂_x g_{pp}`, reduced to the common denominator. -/
theorem Gr_xp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (irp * Frac.d δx gpp)) (⟨Gr_xp_n3, Gr_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gr_xp_n3, Gr_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `Γ^r_{xp}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_r_xp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Gr_xp_n1 + Gr_xp_n2 + Gr_xp_n3, Gr_xp_cd⟩) (Gr_xp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_xp_n1, Gr_xp_n2, Gr_xp_n3, Gr_xp_cd, Gr_xp, δr_0, δr_1, δr_2, δr_3, δr_4,
        δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ### `Γ^r_{pp}` -/

/-- `Γ^r_{pp}`, reduced. -/
def Gr_pp : Frac 5 := ⟨(x - 1) * (x + 1) * (a ^ 2 - 2 * m * r + q ^ 2 + r ^ 2) * (-a ^ 4 * m * x ^
    4 + a ^ 4 * m * x ^ 2 + a ^ 4 * r * x ^ 4 + a ^ 2 * m * r ^ 2 * x ^ 2 - a ^ 2 * m * r ^ 2 - a ^
    2 * q ^ 2 * r * x ^ 2 + a ^ 2 * q ^ 2 * r + 2 * a ^ 2 * r ^ 3 * x ^ 2 + r ^ 5), (a ^ 2 * x ^ 2
    + r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `Γ^r_{pp}`. -/
def Gr_pp_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 3

/-- The numerator of `½ g^{rr} ∂_r g_{pp}` over the common denominator. -/
def Gr_pp_n1 : ZExp 5 := -(x - 1) * (x + 1) * (a ^ 2 - 2 * m * r + q ^ 2 + r ^ 2) * (-a ^ 4 * m * x
    ^ 4 + a ^ 4 * m * x ^ 2 + a ^ 4 * r * x ^ 4 + a ^ 2 * m * r ^ 2 * x ^ 2 - a ^ 2 * m * r ^ 2 - a
    ^ 2 * q ^ 2 * r * x ^ 2 + a ^ 2 * q ^ 2 * r + 2 * a ^ 2 * r ^ 3 * x ^ 2 + r ^ 5)
/-- `½ g^{rr} ∂_r g_{pp}`, reduced to the common denominator. -/
theorem Gr_pp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (irr * Frac.d δr gpp)) (⟨Gr_pp_n1, Gr_pp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gr_pp_n1, Gr_pp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `Γ^r_{pp}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_r_pp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨0 - Gr_pp_n1, Gr_pp_cd⟩) (Gr_pp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gr_pp_n1, Gr_pp_cd, Gr_pp, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-! ### `Γ^x_{vv}` -/

/-- `Γ^x_{vv}`, reduced. -/
def Gx_vv : Frac 5 := ⟨a ^ 2 * x * (x - 1) * (x + 1) * (-2 * m * r + q ^ 2), (a ^ 2 * x ^ 2 + r ^
    2) ^ 3⟩

/-- The common denominator of the terms of `Γ^x_{vv}`. -/
def Gx_vv_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 3

/-- The numerator of `½ g^{xx} ∂_x g_{vv}` over the common denominator. -/
def Gx_vv_n1 : ZExp 5 := -a ^ 2 * x * (x - 1) * (x + 1) * (-2 * m * r + q ^ 2)
/-- `½ g^{xx} ∂_x g_{vv}`, reduced to the common denominator. -/
theorem Gx_vv_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ixx * Frac.d δx gvv)) (⟨Gx_vv_n1, Gx_vv_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gx_vv_n1, Gx_vv_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `Γ^x_{vv}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_x_vv :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨0 - Gx_vv_n1, Gx_vv_cd⟩) (Gx_vv))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_vv_n1, Gx_vv_cd, Gx_vv, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-! ### `Γ^x_{vr}` -/

/-- `Γ^x_{vr}`, reduced. -/
def Gx_vr : Frac 5 := ⟨0, 1⟩

/-- The common denominator of the terms of `Γ^x_{vr}`. -/
def Gx_vr_cd : ZExp 5 := 1

/-- The numerator of `½ g^{xx} ∂_x g_{vr}` over the common denominator. -/
def Gx_vr_n1 : ZExp 5 := 0
/-- `½ g^{xx} ∂_x g_{vr}`, reduced to the common denominator. -/
theorem Gx_vr_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ixx * Frac.d δx gvr)) (⟨Gx_vr_n1, Gx_vr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gx_vr_n1, Gx_vr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `Γ^x_{vr}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_x_vr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨0 - Gx_vr_n1, Gx_vr_cd⟩) (Gx_vr))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_vr_n1, Gx_vr_cd, Gx_vr, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-! ### `Γ^x_{vp}` -/

/-- `Γ^x_{vp}`, reduced. -/
def Gx_vp : Frac 5 := ⟨-a * x * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (-2 * m * r + q ^ 2), (a ^ 2
    * x ^ 2 + r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `Γ^x_{vp}`. -/
def Gx_vp_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 3

/-- The numerator of `½ g^{xx} ∂_x g_{vp}` over the common denominator. -/
def Gx_vp_n1 : ZExp 5 := a * x * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (-2 * m * r + q ^ 2)
/-- `½ g^{xx} ∂_x g_{vp}`, reduced to the common denominator. -/
theorem Gx_vp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ixx * Frac.d δx gvp)) (⟨Gx_vp_n1, Gx_vp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gx_vp_n1, Gx_vp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `Γ^x_{vp}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_x_vp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨0 - Gx_vp_n1, Gx_vp_cd⟩) (Gx_vp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_vp_n1, Gx_vp_cd, Gx_vp, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-! ### `Γ^x_{rx}` -/

/-- `Γ^x_{rx}`, reduced. -/
def Gx_rx : Frac 5 := ⟨r, a ^ 2 * x ^ 2 + r ^ 2⟩

/-- The common denominator of the terms of `Γ^x_{rx}`. -/
def Gx_rx_cd : ZExp 5 := a ^ 2 * x ^ 2 + r ^ 2

/-- The numerator of `½ g^{xx} ∂_r g_{xx}` over the common denominator. -/
def Gx_rx_n1 : ZExp 5 := r
/-- `½ g^{xx} ∂_r g_{xx}`, reduced to the common denominator. -/
theorem Gx_rx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ixx * Frac.d δr gxx)) (⟨Gx_rx_n1, Gx_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gx_rx_n1, Gx_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `Γ^x_{rx}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_x_rx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Gx_rx_n1, Gx_rx_cd⟩) (Gx_rx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rx_n1, Gx_rx_cd, Gx_rx, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4])

/-! ### `Γ^x_{rp}` -/

/-- `Γ^x_{rp}`, reduced. -/
def Gx_rp : Frac 5 := ⟨a * x * (x - 1) * (x + 1), a ^ 2 * x ^ 2 + r ^ 2⟩

/-- The common denominator of the terms of `Γ^x_{rp}`. -/
def Gx_rp_cd : ZExp 5 := a ^ 2 * x ^ 2 + r ^ 2

/-- The numerator of `½ g^{xx} ∂_x g_{rp}` over the common denominator. -/
def Gx_rp_n1 : ZExp 5 := -a * x * (x - 1) * (x + 1)
/-- `½ g^{xx} ∂_x g_{rp}`, reduced to the common denominator. -/
theorem Gx_rp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ixx * Frac.d δx grp)) (⟨Gx_rp_n1, Gx_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gx_rp_n1, Gx_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `Γ^x_{rp}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_x_rp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨0 - Gx_rp_n1, Gx_rp_cd⟩) (Gx_rp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_rp_n1, Gx_rp_cd, Gx_rp, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-! ### `Γ^x_{xx}` -/

/-- `Γ^x_{xx}`, reduced. -/
def Gx_xx : Frac 5 := ⟨-x * (a ^ 2 + r ^ 2), (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2)⟩

/-- The common denominator of the terms of `Γ^x_{xx}`. -/
def Gx_xx_cd : ZExp 5 := (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2)

/-- The numerator of `½ g^{xx} ∂_x g_{xx}` over the common denominator. -/
def Gx_xx_n1 : ZExp 5 := -x * (a ^ 2 + r ^ 2)
/-- `½ g^{xx} ∂_x g_{xx}`, reduced to the common denominator. -/
theorem Gx_xx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ixx * Frac.d δx gxx)) (⟨Gx_xx_n1, Gx_xx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gx_xx_n1, Gx_xx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{xx} ∂_x g_{xx}` over the common denominator. -/
def Gx_xx_n2 : ZExp 5 := -x * (a ^ 2 + r ^ 2)
/-- `½ g^{xx} ∂_x g_{xx}`, reduced to the common denominator. -/
theorem Gx_xx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ixx * Frac.d δx gxx)) (⟨Gx_xx_n2, Gx_xx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gx_xx_n2, Gx_xx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{xx} ∂_x g_{xx}` over the common denominator. -/
def Gx_xx_n3 : ZExp 5 := -x * (a ^ 2 + r ^ 2)
/-- `½ g^{xx} ∂_x g_{xx}`, reduced to the common denominator. -/
theorem Gx_xx_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ixx * Frac.d δx gxx)) (⟨Gx_xx_n3, Gx_xx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gx_xx_n3, Gx_xx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `Γ^x_{xx}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_x_xx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Gx_xx_n1 + Gx_xx_n2 - Gx_xx_n3, Gx_xx_cd⟩) (Gx_xx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_xx_n1, Gx_xx_n2, Gx_xx_n3, Gx_xx_cd, Gx_xx, δr_0, δr_1, δr_2, δr_3, δr_4,
        δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ### `Γ^x_{pp}` -/

/-- `Γ^x_{pp}`, reduced. -/
def Gx_pp : Frac 5 := ⟨-x * (x - 1) * (x + 1) * (a ^ 6 * x ^ 4 - 2 * a ^ 4 * m * r * x ^ 4 + 2 * a
    ^ 4 * m * r + a ^ 4 * q ^ 2 * x ^ 4 - a ^ 4 * q ^ 2 + a ^ 4 * r ^ 2 * x ^ 4 + 2 * a ^ 4 * r ^ 2
    * x ^ 2 - 4 * a ^ 2 * m * r ^ 3 * x ^ 2 + 4 * a ^ 2 * m * r ^ 3 + 2 * a ^ 2 * q ^ 2 * r ^ 2 * x
    ^ 2 - 2 * a ^ 2 * q ^ 2 * r ^ 2 + 2 * a ^ 2 * r ^ 4 * x ^ 2 + a ^ 2 * r ^ 4 + r ^ 6), (a ^ 2 *
    x ^ 2 + r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `Γ^x_{pp}`. -/
def Gx_pp_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 3

/-- The numerator of `½ g^{xx} ∂_x g_{pp}` over the common denominator. -/
def Gx_pp_n1 : ZExp 5 := x * (x - 1) * (x + 1) * (a ^ 6 * x ^ 4 - 2 * a ^ 4 * m * r * x ^ 4 + 2 * a
    ^ 4 * m * r + a ^ 4 * q ^ 2 * x ^ 4 - a ^ 4 * q ^ 2 + a ^ 4 * r ^ 2 * x ^ 4 + 2 * a ^ 4 * r ^ 2
    * x ^ 2 - 4 * a ^ 2 * m * r ^ 3 * x ^ 2 + 4 * a ^ 2 * m * r ^ 3 + 2 * a ^ 2 * q ^ 2 * r ^ 2 * x
    ^ 2 - 2 * a ^ 2 * q ^ 2 * r ^ 2 + 2 * a ^ 2 * r ^ 4 * x ^ 2 + a ^ 2 * r ^ 4 + r ^ 6)
/-- `½ g^{xx} ∂_x g_{pp}`, reduced to the common denominator. -/
theorem Gx_pp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ixx * Frac.d δx gpp)) (⟨Gx_pp_n1, Gx_pp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gx_pp_n1, Gx_pp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `Γ^x_{pp}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_x_pp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨0 - Gx_pp_n1, Gx_pp_cd⟩) (Gx_pp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gx_pp_n1, Gx_pp_cd, Gx_pp, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-! ### `Γ^p_{vv}` -/

/-- `Γ^p_{vv}`, reduced. -/
def Gp_vv : Frac 5 := ⟨-a * (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^ 2 * r), (a ^ 2 * x ^ 2 + r ^ 2) ^
    3⟩

/-- The common denominator of the terms of `Γ^p_{vv}`. -/
def Gp_vv_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 3

/-- The numerator of `½ g^{pr} ∂_r g_{vv}` over the common denominator. -/
def Gp_vv_n1 : ZExp 5 := a * (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^ 2 * r)
/-- `½ g^{pr} ∂_r g_{vv}`, reduced to the common denominator. -/
theorem Gp_vv_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (irp * Frac.d δr gvv)) (⟨Gp_vv_n1, Gp_vv_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gp_vv_n1, Gp_vv_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `Γ^p_{vv}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_p_vv :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨0 - Gp_vv_n1, Gp_vv_cd⟩) (Gp_vv))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vv_n1, Gp_vv_cd, Gp_vv, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-! ### `Γ^p_{vr}` -/

/-- `Γ^p_{vr}`, reduced. -/
def Gp_vr : Frac 5 := ⟨0, 1⟩

/-- The common denominator of the terms of `Γ^p_{vr}`. -/
def Gp_vr_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 3

/-- The numerator of `½ g^{pv} ∂_r g_{vv}` over the common denominator. -/
def Gp_vr_n1 : ZExp 5 := a * (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^ 2 * r)
/-- `½ g^{pv} ∂_r g_{vv}`, reduced to the common denominator. -/
theorem Gp_vr_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivp * Frac.d δr gvv)) (⟨Gp_vr_n1, Gp_vr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gp_vr_n1, Gp_vr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{pr} ∂_r g_{rv}` over the common denominator. -/
def Gp_vr_n2 : ZExp 5 := 0
/-- `½ g^{pr} ∂_r g_{rv}`, reduced to the common denominator. -/
theorem Gp_vr_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (irp * Frac.d δr gvr)) (⟨Gp_vr_n2, Gp_vr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gp_vr_n2, Gp_vr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{pr} ∂_r g_{vr}` over the common denominator. -/
def Gp_vr_n3 : ZExp 5 := 0
/-- `½ g^{pr} ∂_r g_{vr}`, reduced to the common denominator. -/
theorem Gp_vr_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (irp * Frac.d δr gvr)) (⟨Gp_vr_n3, Gp_vr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gp_vr_n3, Gp_vr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{pp} ∂_r g_{pv}` over the common denominator. -/
def Gp_vr_n4 : ZExp 5 := -a * (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^ 2 * r)
/-- `½ g^{pp} ∂_r g_{pv}`, reduced to the common denominator. -/
theorem Gp_vr_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ipp * Frac.d δr gvp)) (⟨Gp_vr_n4, Gp_vr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gp_vr_n4, Gp_vr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `Γ^p_{vr}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_p_vr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Gp_vr_n1 + Gp_vr_n2 - Gp_vr_n3 + Gp_vr_n4, Gp_vr_cd⟩) (Gp_vr))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vr_n1, Gp_vr_n2, Gp_vr_n3, Gp_vr_n4, Gp_vr_cd, Gp_vr, δr_0, δr_1, δr_2,
        δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ### `Γ^p_{vx}` -/

/-- `Γ^p_{vx}`, reduced. -/
def Gp_vx : Frac 5 := ⟨a * x * (-2 * m * r + q ^ 2), (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^
    2⟩

/-- The common denominator of the terms of `Γ^p_{vx}`. -/
def Gp_vx_cd : ZExp 5 := (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3

/-- The numerator of `½ g^{pv} ∂_x g_{vv}` over the common denominator. -/
def Gp_vx_n1 : ZExp 5 := a ^ 3 * x * (x - 1) * (x + 1) * (-2 * m * r + q ^ 2)
/-- `½ g^{pv} ∂_x g_{vv}`, reduced to the common denominator. -/
theorem Gp_vx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivp * Frac.d δx gvv)) (⟨Gp_vx_n1, Gp_vx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gp_vx_n1, Gp_vx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{pr} ∂_x g_{rv}` over the common denominator. -/
def Gp_vx_n2 : ZExp 5 := 0
/-- `½ g^{pr} ∂_x g_{rv}`, reduced to the common denominator. -/
theorem Gp_vx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (irp * Frac.d δx gvr)) (⟨Gp_vx_n2, Gp_vx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gp_vx_n2, Gp_vx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{pp} ∂_x g_{pv}` over the common denominator. -/
def Gp_vx_n3 : ZExp 5 := a * x * (a ^ 2 + r ^ 2) * (-2 * m * r + q ^ 2)
/-- `½ g^{pp} ∂_x g_{pv}`, reduced to the common denominator. -/
theorem Gp_vx_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ipp * Frac.d δx gvp)) (⟨Gp_vx_n3, Gp_vx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gp_vx_n3, Gp_vx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `Γ^p_{vx}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_p_vx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Gp_vx_n1 + Gp_vx_n2 + Gp_vx_n3, Gp_vx_cd⟩) (Gp_vx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vx_n1, Gp_vx_n2, Gp_vx_n3, Gp_vx_cd, Gp_vx, δr_0, δr_1, δr_2, δr_3, δr_4,
        δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ### `Γ^p_{vp}` -/

/-- `Γ^p_{vp}`, reduced. -/
def Gp_vp : Frac 5 := ⟨-a ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^ 2 * r), (a
    ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `Γ^p_{vp}`. -/
def Gp_vp_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 3

/-- The numerator of `½ g^{pr} ∂_r g_{vp}` over the common denominator. -/
def Gp_vp_n1 : ZExp 5 := a ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^ 2 * r)
/-- `½ g^{pr} ∂_r g_{vp}`, reduced to the common denominator. -/
theorem Gp_vp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (irp * Frac.d δr gvp)) (⟨Gp_vp_n1, Gp_vp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gp_vp_n1, Gp_vp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `Γ^p_{vp}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_p_vp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨0 - Gp_vp_n1, Gp_vp_cd⟩) (Gp_vp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_vp_n1, Gp_vp_cd, Gp_vp, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-! ### `Γ^p_{rr}` -/

/-- `Γ^p_{rr}`, reduced. -/
def Gp_rr : Frac 5 := ⟨0, 1⟩

/-- The common denominator of the terms of `Γ^p_{rr}`. -/
def Gp_rr_cd : ZExp 5 := 1

/-- The numerator of `½ g^{pv} ∂_r g_{vr}` over the common denominator. -/
def Gp_rr_n1 : ZExp 5 := 0
/-- `½ g^{pv} ∂_r g_{vr}`, reduced to the common denominator. -/
theorem Gp_rr_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivp * Frac.d δr gvr)) (⟨Gp_rr_n1, Gp_rr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gp_rr_n1, Gp_rr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{pv} ∂_r g_{vr}` over the common denominator. -/
def Gp_rr_n2 : ZExp 5 := 0
/-- `½ g^{pv} ∂_r g_{vr}`, reduced to the common denominator. -/
theorem Gp_rr_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivp * Frac.d δr gvr)) (⟨Gp_rr_n2, Gp_rr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gp_rr_n2, Gp_rr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{pp} ∂_r g_{pr}` over the common denominator. -/
def Gp_rr_n3 : ZExp 5 := 0
/-- `½ g^{pp} ∂_r g_{pr}`, reduced to the common denominator. -/
theorem Gp_rr_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ipp * Frac.d δr grp)) (⟨Gp_rr_n3, Gp_rr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gp_rr_n3, Gp_rr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{pp} ∂_r g_{pr}` over the common denominator. -/
def Gp_rr_n4 : ZExp 5 := 0
/-- `½ g^{pp} ∂_r g_{pr}`, reduced to the common denominator. -/
theorem Gp_rr_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ipp * Frac.d δr grp)) (⟨Gp_rr_n4, Gp_rr_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gp_rr_n4, Gp_rr_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `Γ^p_{rr}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_p_rr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Gp_rr_n1 + Gp_rr_n2 + Gp_rr_n3 + Gp_rr_n4, Gp_rr_cd⟩) (Gp_rr))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rr_n1, Gp_rr_n2, Gp_rr_n3, Gp_rr_n4, Gp_rr_cd, Gp_rr, δr_0, δr_1, δr_2,
        δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ### `Γ^p_{rx}` -/

/-- `Γ^p_{rx}`, reduced. -/
def Gp_rx : Frac 5 := ⟨-a * x, (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2)⟩

/-- The common denominator of the terms of `Γ^p_{rx}`. -/
def Gp_rx_cd : ZExp 5 := (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2)

/-- The numerator of `½ g^{pv} ∂_x g_{vr}` over the common denominator. -/
def Gp_rx_n1 : ZExp 5 := 0
/-- `½ g^{pv} ∂_x g_{vr}`, reduced to the common denominator. -/
theorem Gp_rx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivp * Frac.d δx gvr)) (⟨Gp_rx_n1, Gp_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gp_rx_n1, Gp_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{pp} ∂_x g_{pr}` over the common denominator. -/
def Gp_rx_n2 : ZExp 5 := -a * x
/-- `½ g^{pp} ∂_x g_{pr}`, reduced to the common denominator. -/
theorem Gp_rx_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ipp * Frac.d δx grp)) (⟨Gp_rx_n2, Gp_rx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gp_rx_n2, Gp_rx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `Γ^p_{rx}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_p_rx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Gp_rx_n1 + Gp_rx_n2, Gp_rx_cd⟩) (Gp_rx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rx_n1, Gp_rx_n2, Gp_rx_cd, Gp_rx, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1,
        δx_2, δx_3, δx_4]
    ring)

/-! ### `Γ^p_{rp}` -/

/-- `Γ^p_{rp}`, reduced. -/
def Gp_rp : Frac 5 := ⟨r, a ^ 2 * x ^ 2 + r ^ 2⟩

/-- The common denominator of the terms of `Γ^p_{rp}`. -/
def Gp_rp_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 3

/-- The numerator of `½ g^{pv} ∂_r g_{vp}` over the common denominator. -/
def Gp_rp_n1 : ZExp 5 := a ^ 2 * (x - 1) * (x + 1) * (a ^ 2 * m * x ^ 2 - m * r ^ 2 + q ^ 2 * r)
/-- `½ g^{pv} ∂_r g_{vp}`, reduced to the common denominator. -/
theorem Gp_rp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivp * Frac.d δr gvp)) (⟨Gp_rp_n1, Gp_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gp_rp_n1, Gp_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{pr} ∂_r g_{rp}` over the common denominator. -/
def Gp_rp_n2 : ZExp 5 := 0
/-- `½ g^{pr} ∂_r g_{rp}`, reduced to the common denominator. -/
theorem Gp_rp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (irp * Frac.d δr grp)) (⟨Gp_rp_n2, Gp_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gp_rp_n2, Gp_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{pr} ∂_r g_{rp}` over the common denominator. -/
def Gp_rp_n3 : ZExp 5 := 0
/-- `½ g^{pr} ∂_r g_{rp}`, reduced to the common denominator. -/
theorem Gp_rp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (irp * Frac.d δr grp)) (⟨Gp_rp_n3, Gp_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gp_rp_n3, Gp_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{pp} ∂_r g_{pp}` over the common denominator. -/
def Gp_rp_n4 : ZExp 5 := -a ^ 4 * m * x ^ 4 + a ^ 4 * m * x ^ 2 + a ^ 4 * r * x ^ 4 + a ^ 2 * m * r
    ^ 2 * x ^ 2 - a ^ 2 * m * r ^ 2 - a ^ 2 * q ^ 2 * r * x ^ 2 + a ^ 2 * q ^ 2 * r + 2 * a ^ 2 * r
    ^ 3 * x ^ 2 + r ^ 5
/-- `½ g^{pp} ∂_r g_{pp}`, reduced to the common denominator. -/
theorem Gp_rp_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ipp * Frac.d δr gpp)) (⟨Gp_rp_n4, Gp_rp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gp_rp_n4, Gp_rp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `Γ^p_{rp}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_p_rp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Gp_rp_n1 + Gp_rp_n2 - Gp_rp_n3 + Gp_rp_n4, Gp_rp_cd⟩) (Gp_rp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_rp_n1, Gp_rp_n2, Gp_rp_n3, Gp_rp_n4, Gp_rp_cd, Gp_rp, δr_0, δr_1, δr_2,
        δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ### `Γ^p_{xx}` -/

/-- `Γ^p_{xx}`, reduced. -/
def Gp_xx : Frac 5 := ⟨a * r, (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2)⟩

/-- The common denominator of the terms of `Γ^p_{xx}`. -/
def Gp_xx_cd : ZExp 5 := (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2)

/-- The numerator of `½ g^{pr} ∂_r g_{xx}` over the common denominator. -/
def Gp_xx_n1 : ZExp 5 := -a * r
/-- `½ g^{pr} ∂_r g_{xx}`, reduced to the common denominator. -/
theorem Gp_xx_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (irp * Frac.d δr gxx)) (⟨Gp_xx_n1, Gp_xx_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gp_xx_n1, Gp_xx_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `Γ^p_{xx}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_p_xx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨0 - Gp_xx_n1, Gp_xx_cd⟩) (Gp_xx))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_xx_n1, Gp_xx_cd, Gp_xx, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

/-! ### `Γ^p_{xp}` -/

/-- `Γ^p_{xp}`, reduced. -/
def Gp_xp : Frac 5 := ⟨x * (a ^ 4 * x ^ 4 - 2 * a ^ 2 * m * r * x ^ 2 + 2 * a ^ 2 * m * r + a ^ 2 *
    q ^ 2 * x ^ 2 - a ^ 2 * q ^ 2 + 2 * a ^ 2 * r ^ 2 * x ^ 2 + r ^ 4), (x - 1) * (x + 1) * (a ^ 2
    * x ^ 2 + r ^ 2) ^ 2⟩

/-- The common denominator of the terms of `Γ^p_{xp}`. -/
def Gp_xp_cd : ZExp 5 := (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 3

/-- The numerator of `½ g^{pv} ∂_x g_{vp}` over the common denominator. -/
def Gp_xp_n1 : ZExp 5 := -a ^ 2 * x * (a ^ 2 + r ^ 2) * (x - 1) * (x + 1) * (-2 * m * r + q ^ 2)
/-- `½ g^{pv} ∂_x g_{vp}`, reduced to the common denominator. -/
theorem Gp_xp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ivp * Frac.d δx gvp)) (⟨Gp_xp_n1, Gp_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gp_xp_n1, Gp_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{pr} ∂_x g_{rp}` over the common denominator. -/
def Gp_xp_n2 : ZExp 5 := a ^ 2 * x * (x - 1) * (x + 1) * (a ^ 2 * x ^ 2 + r ^ 2) ^ 2
/-- `½ g^{pr} ∂_x g_{rp}`, reduced to the common denominator. -/
theorem Gp_xp_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (irp * Frac.d δx grp)) (⟨Gp_xp_n2, Gp_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gp_xp_n2, Gp_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- The numerator of `½ g^{pp} ∂_x g_{pp}` over the common denominator. -/
def Gp_xp_n3 : ZExp 5 := x * (a ^ 6 * x ^ 4 - 2 * a ^ 4 * m * r * x ^ 4 + 2 * a ^ 4 * m * r + a ^ 4
    * q ^ 2 * x ^ 4 - a ^ 4 * q ^ 2 + a ^ 4 * r ^ 2 * x ^ 4 + 2 * a ^ 4 * r ^ 2 * x ^ 2 - 4 * a ^ 2
    * m * r ^ 3 * x ^ 2 + 4 * a ^ 2 * m * r ^ 3 + 2 * a ^ 2 * q ^ 2 * r ^ 2 * x ^ 2 - 2 * a ^ 2 * q
    ^ 2 * r ^ 2 + 2 * a ^ 2 * r ^ 4 * x ^ 2 + a ^ 2 * r ^ 4 + r ^ 6)
/-- `½ g^{pp} ∂_x g_{pp}`, reduced to the common denominator. -/
theorem Gp_xp_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (ipp * Frac.d δx gpp)) (⟨Gp_xp_n3, Gp_xp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gp_xp_n3, Gp_xp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `Γ^p_{xp}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_p_xp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨Gp_xp_n1 + Gp_xp_n2 + Gp_xp_n3, Gp_xp_cd⟩) (Gp_xp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_xp_n1, Gp_xp_n2, Gp_xp_n3, Gp_xp_cd, Gp_xp, δr_0, δr_1, δr_2, δr_3, δr_4,
        δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-! ### `Γ^p_{pp}` -/

/-- `Γ^p_{pp}`, reduced. -/
def Gp_pp : Frac 5 := ⟨a * (x - 1) * (x + 1) * (-a ^ 4 * m * x ^ 4 + a ^ 4 * m * x ^ 2 + a ^ 4 * r
    * x ^ 4 + a ^ 2 * m * r ^ 2 * x ^ 2 - a ^ 2 * m * r ^ 2 - a ^ 2 * q ^ 2 * r * x ^ 2 + a ^ 2 * q
    ^ 2 * r + 2 * a ^ 2 * r ^ 3 * x ^ 2 + r ^ 5), (a ^ 2 * x ^ 2 + r ^ 2) ^ 3⟩

/-- The common denominator of the terms of `Γ^p_{pp}`. -/
def Gp_pp_cd : ZExp 5 := (a ^ 2 * x ^ 2 + r ^ 2) ^ 3

/-- The numerator of `½ g^{pr} ∂_r g_{pp}` over the common denominator. -/
def Gp_pp_n1 : ZExp 5 := -a * (x - 1) * (x + 1) * (-a ^ 4 * m * x ^ 4 + a ^ 4 * m * x ^ 2 + a ^ 4 *
    r * x ^ 4 + a ^ 2 * m * r ^ 2 * x ^ 2 - a ^ 2 * m * r ^ 2 - a ^ 2 * q ^ 2 * r * x ^ 2 + a ^ 2 *
    q ^ 2 * r + 2 * a ^ 2 * r ^ 3 * x ^ 2 + r ^ 5)
/-- `½ g^{pr} ∂_r g_{pp}`, reduced to the common denominator. -/
theorem Gp_pp_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (Frac.half (irp * Frac.d δr gpp)) (⟨Gp_pp_n1, Gp_pp_cd⟩))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [gvv, gvr, gvp, grp, gpp, gxx, ivv, ivr, ivp, irr, irp, ixx, ipp, Sg, sx, Pp,
        Dl, Gp_pp_n1, Gp_pp_cd, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2, δx_3, δx_4]
    ring)

/-- `Γ^p_{pp}`: the signed sum of its terms is the reduced fraction. -/
theorem christoffel_p_pp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (⟨0 - Gp_pp_n1, Gp_pp_cd⟩) (Gp_pp))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Gp_pp_n1, Gp_pp_cd, Gp_pp, δr_0, δr_1, δr_2, δr_3, δr_4, δx_0, δx_1, δx_2,
        δx_3, δx_4]
    ring)

end LeanProofs.IPRA.Geometry.KerrNewmanIngoingConnection
