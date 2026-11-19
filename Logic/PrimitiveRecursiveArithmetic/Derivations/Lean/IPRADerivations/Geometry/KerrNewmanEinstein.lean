import IPRADerivations.Foundations.ExpressionRenaming
import IPRADerivations.Geometry.KerrNewmanRicci
import IPRADerivations.Geometry.KerrNewmanMaxwell

/-!
# The scalar curvature and the Einstein–Maxwell equation of the Kerr–Newman family

Packet: `geometry/four_metrics_ipra_2026-11-15`: the second identity of `lem:offshell`
("`R = (2 − w)/Σ`"), the remark after `eq:maxwell` ("The trace of the right-hand side of
`eq:EM` is zero"), and the Einstein–Maxwell equation `eq:EM`,
`R_{μν} = 2 (F_{μρ} F_ν{}^ρ − ¼ g_{μν} F_{αβ} F^{αβ})`, for the Kerr–Newman radial function
(`thm:KN`, `thm:converse`: "Equating `eq:offshell` and `eq:stress` in the invertible coframe
gives `U = V = q²/Σ²`").

## The coframe and the scalar curvature (indeterminates `r, x, a, d, v, w`)

The proof of `lem:offshell` ends: "Tracing in the coframe `(p, dr, dx, b)` gives
`R = −2U + 2V = (2 − w)/Σ`". With `p = dt − a s dφ`, `b = P dφ − a dt` and the inverse metric
`eq:ginv`:

* `coframe_pp`, `coframe_bb`, `coframe_pb`: `g⁻¹(p, p) = −Σ/d`, `g⁻¹(b, b) = Σ/s`,
  `g⁻¹(p, b) = 0`;
* `trace_U`, `trace_V`: the contraction of `(d/Σ) p² − (Σ/d) dr²` with the inverse metric is
  `−2`, and that of `(Σ/s) dx² + (s/Σ) b²` is `2`;
* `scalar_UV`: `−2U + 2V = (2 − w)/Σ`;
* `Rtt`, `Rtp`, `Rpp`, `Rrr`, `Rxx`: the entries of `eq:offshell` (the right-hand sides of
  `Geometry/KerrNewmanRicci.ricci_tt` … `ricci_xx`, verbatim);
* `scalar_t1` … `scalar_t5`: each term `g^{μν} R_{μν}` of the contraction equals a numerator
  over the common denominator `2 d Σ⁴` (identities of fractions in which `Σ`, `s`, `P`, `N`
  are not unfolded);
* `scalar_curvature`: `g^{tt} R_tt + 2 g^{tφ} R_tφ + g^{φφ} R_φφ + g^{rr} R_rr + g^{xx} R_xx`,
  as the sum of these numerators, is `(2 − w)/Σ`.

## The stress tensor is trace-free (indeterminates `r, x, a, d, q`)

* `Ttt`, `Ttp`, `Tpp`, `Trr`, `Txx`: the entries of `eq:stress` (the right-hand sides of
  `Geometry/KerrNewmanMaxwell.stress_tt` … `stress_xx`, verbatim);
* `stress_trace`: the contraction of the tensor `(d/Σ) p² − (Σ/d) dr² + (Σ/s) dx² + (s/Σ) b²`
  of `eq:stress` with the inverse metric is `0`, so `g^{μν} T_{μν} = (E² + 𝓑²) · 0`.

## The Einstein–Maxwell equation (indeterminates `r, x, a, d, v, w, m, q`)

The two calculations are compared after renaming their variables into one list
(`Foundations/ExpressionRenaming`): `ι₆` for the Ricci side, `ι₅` for the Maxwell side. Under
the hypotheses `d = Δ = r² − 2mr + a² + q²`, `v = 2r − 2m`, `w = 2`
(`Geometry/KerrNewmanRicci.knHyps`):

* `kn_U`, `kn_V`: `U = q²/Σ²` and `V = q²/Σ²` (`thm:KN`, as fractions);
* `kn_field`: `E² + 𝓑² = q²/Σ²` in the common variables (`eq:sumSquares`; no hypothesis);
* `kn_scalar`: the scalar curvature `(2 − w)/Σ` is `0`;
* `einstein_tt`, `einstein_tp`, `einstein_pp`, `einstein_rr`, `einstein_xx`:
  `R_{μν} = T_{μν}`, the entry of `eq:offshell` equals the entry of `eq:stress`.

The converse direction of `prop:radial` ("Conversely these two scalar equations imply those
two values of `U`, `V`, so all the tensor equations follow") has only the hypotheses
`eq:radial`, `w = 2` and `N = r² − a² + d − r v = q²` (`radialHyps`), for an unspecified radial
function: `radial_U`, `radial_V`, and `radial_tt`, `radial_tp`, `radial_pp`, `radial_rr`,
`radial_xx`. The forward direction cancels `Σ²` and is not stated.

For the remaining entries both sides are `0`: `ricci_rx` and `stress_rx`, and `R_tr`, `R_tx`,
`R_rφ`, `R_xφ`, `T_tr`, `T_tx`, `T_rφ`, `T_xφ` have no nonvanishing term.

Every statement is an identity of fractions cleared of denominators (`Frac.eqn`), a closed
sentence of iPRA certified in every commutative ring; its reading as an equality of rational
functions uses `Σ d s ≠ 0`. The chain "sum of the terms of `eq:ricci` = entry of
`eq:offshell`" (`ricci_μν`), "= entry of `eq:stress`" (`einstein_μν`), "= sum of the terms of
`eq:EM`" (`stress_μν`) is three such sentences; their composition into one cleared identity
between the two sums of terms is not stated. The primitive recursive functions `Reg` and `Zero`
of `thm:arithmetic` and its literal form (for all codes `c`) are not derived.
-/

namespace LeanProofs.IPRA.Geometry.KerrNewmanEinstein

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ZExp

/-! ## The coframe and the scalar curvature -/

section Scalar

open LeanProofs.IPRA.Geometry.KerrNewmanBase (Sg sx)
open LeanProofs.IPRA.Geometry.KerrNewmanConnection (Pp itt itp ipp irr ixx)
open LeanProofs.IPRA.Geometry.KerrNewmanRicci (Nn Vf Uf)

local notation "r" => (ZExp.var 0 : ZExp 6)
local notation "x" => (ZExp.var 1 : ZExp 6)
local notation "a" => (ZExp.var 2 : ZExp 6)
local notation "d" => (ZExp.var 3 : ZExp 6)
local notation "v" => (ZExp.var 4 : ZExp 6)
local notation "w" => (ZExp.var 5 : ZExp 6)

/-- `g⁻¹(p, p) = g^{tt} − 2 a s g^{tφ} + a² s² g^{φφ} = −Σ/d` for `p = dt − a s dφ`. -/
theorem coframe_pp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (itt - Frac.ofZ (2 * a * sx) * itp + Frac.ofZ (a ^ 2 * sx ^ 2) * ipp)
        ⟨-Sg, d⟩)) :=
  derive_imp _ _ (by
    frac_poly R ρ h [itt, itp, ipp, Pp, Sg, sx]
    ring)

/-- `g⁻¹(b, b) = a² g^{tt} − 2 a P g^{tφ} + P² g^{φφ} = Σ/s` for `b = P dφ − a dt`. -/
theorem coframe_bb :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.ofZ (a ^ 2) * itt - Frac.ofZ (2 * a * Pp) * itp
        + Frac.ofZ (Pp ^ 2) * ipp) ⟨Sg, sx⟩)) :=
  derive_imp _ _ (by
    frac_poly R ρ h [itt, itp, ipp, Pp, Sg, sx]
    ring)

/-- `g⁻¹(p, b) = −a g^{tt} + (P + a² s) g^{tφ} − a s P g^{φφ} = 0`: the coframe is
orthogonal. -/
theorem coframe_pb :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.ofZ (Pp + a ^ 2 * sx) * itp - Frac.ofZ a * itt
        - Frac.ofZ (a * sx * Pp) * ipp) (Frac.ofZ 0))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [itt, itp, ipp, Pp, Sg, sx]
    ring)

/-- The contraction of `(d/Σ) p² − (Σ/d) dr²` with the inverse metric is `−2`. -/
theorem trace_U :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (itt * ⟨d, Sg⟩ - Frac.ofZ 2 * (itp * ⟨d * a * sx, Sg⟩)
        + ipp * ⟨d * a ^ 2 * sx ^ 2, Sg⟩ - irr * ⟨Sg, d⟩) (Frac.ofZ (-2)))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [itt, itp, ipp, irr, Pp, Sg, sx]
    ring)

/-- The contraction of `(Σ/s) dx² + (s/Σ) b²` with the inverse metric is `2`. -/
theorem trace_V :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (itt * ⟨sx * a ^ 2, Sg⟩ - Frac.ofZ 2 * (itp * ⟨sx * a * Pp, Sg⟩)
        + ipp * ⟨sx * Pp ^ 2, Sg⟩ + ixx * ⟨Sg, sx⟩) (Frac.ofZ 2))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [itt, itp, ipp, ixx, Pp, Sg, sx]
    ring)

/-- `−2U + 2V = (2 − w)/Σ`. -/
theorem scalar_UV :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.ofZ 2 * Vf - Frac.ofZ 2 * Uf) ⟨2 - w, Sg⟩)) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Uf, Vf]
    ring)

/-- `R_tt` of `eq:offshell`. -/
def Rtt : Frac 6 := Uf * ⟨d, Sg⟩ + Vf * ⟨sx * a ^ 2, Sg⟩
/-- `R_tφ` of `eq:offshell`. -/
def Rtp : Frac 6 := -(Uf * ⟨d * a * sx, Sg⟩) - Vf * ⟨sx * a * Pp, Sg⟩
/-- `R_φφ` of `eq:offshell`. -/
def Rpp : Frac 6 := Uf * ⟨d * a ^ 2 * sx ^ 2, Sg⟩ + Vf * ⟨sx * Pp ^ 2, Sg⟩
/-- `R_rr` of `eq:offshell`. -/
def Rrr : Frac 6 := -(Uf * ⟨Sg, d⟩)
/-- `R_xx` of `eq:offshell`. -/
def Rxx : Frac 6 := Vf * ⟨Sg, sx⟩

/-- `2 Σ² U = 2N + (w − 2) Σ`. -/
def Mn : ZExp 6 := 2 * Nn + (w - 2) * Sg
/-- The common denominator of the terms of the scalar curvature: `2 d Σ⁴`. -/
def Sc_cd : ZExp 6 := 2 * d * Sg ^ 4
/-- The numerator of `g^{tt} R_tt`. -/
def Sc_n1 : ZExp 6 := -((Pp ^ 2 - a ^ 2 * d * sx) * (d * Mn + 2 * Nn * sx * a ^ 2))
/-- The numerator of `g^{tφ} R_tφ`. -/
def Sc_n2 : ZExp 6 := a ^ 2 * sx * (Pp - d) * (d * Mn + 2 * Nn * Pp)
/-- The numerator of `g^{φφ} R_φφ`. -/
def Sc_n3 : ZExp 6 := (d - a ^ 2 * sx) * (d * a ^ 2 * sx * Mn + 2 * Nn * Pp ^ 2)
/-- The numerator of `g^{rr} R_rr = −U`. -/
def Sc_n4 : ZExp 6 := -(Mn * d * Sg ^ 2)
/-- The numerator of `g^{xx} R_xx = V`. -/
def Sc_n5 : ZExp 6 := 2 * Nn * d * Sg ^ 2

/-- `g^{tt} R_tt`, reduced to the common denominator. -/
theorem scalar_t1 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (itt * Rtt) ⟨Sc_n1, Sc_cd⟩)) :=
  derive_imp _ _ (by
    frac_poly R ρ h [itt, Rtt, Uf, Vf, Mn, Sc_n1, Sc_cd]
    ring)

/-- `g^{tφ} R_tφ`, reduced to the common denominator. -/
theorem scalar_t2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (itp * Rtp) ⟨Sc_n2, Sc_cd⟩)) :=
  derive_imp _ _ (by
    frac_poly R ρ h [itp, Rtp, Uf, Vf, Mn, Sc_n2, Sc_cd]
    ring)

/-- `g^{φφ} R_φφ`, reduced to the common denominator. -/
theorem scalar_t3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (ipp * Rpp) ⟨Sc_n3, Sc_cd⟩)) :=
  derive_imp _ _ (by
    frac_poly R ρ h [ipp, Rpp, Uf, Vf, Mn, Sc_n3, Sc_cd]
    ring)

/-- `g^{rr} R_rr`, reduced to the common denominator. -/
theorem scalar_t4 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (irr * Rrr) ⟨Sc_n4, Sc_cd⟩)) :=
  derive_imp _ _ (by
    frac_poly R ρ h [irr, Rrr, Uf, Vf, Mn, Sc_n4, Sc_cd]
    ring)

/-- `g^{xx} R_xx`, reduced to the common denominator. -/
theorem scalar_t5 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (ixx * Rxx) ⟨Sc_n5, Sc_cd⟩)) :=
  derive_imp _ _ (by
    frac_poly R ρ h [ixx, Rxx, Uf, Vf, Mn, Sc_n5, Sc_cd]
    ring)

/-- The scalar curvature (`lem:offshell`):
`g^{tt} R_tt + 2 g^{tφ} R_tφ + g^{φφ} R_φφ + g^{rr} R_rr + g^{xx} R_xx = (2 − w)/Σ`, as the sum
of the numerators of its terms. -/
theorem scalar_curvature :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn ⟨Sc_n1 + 2 * Sc_n2 + Sc_n3 + Sc_n4 + Sc_n5, Sc_cd⟩ ⟨2 - w, Sg⟩)) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Sc_n1, Sc_n2, Sc_n3, Sc_n4, Sc_n5, Sc_cd, Mn, Nn, Pp, Sg, sx]
    ring)

end Scalar

/-! ## The stress tensor is trace-free -/

section Stress

open LeanProofs.IPRA.Geometry.KerrNewmanMaxwell (Sg sx Pp itt itp ipp irr ixx EB2)

local notation "r" => (ZExp.var 0 : ZExp 5)
local notation "x" => (ZExp.var 1 : ZExp 5)
local notation "a" => (ZExp.var 2 : ZExp 5)
local notation "d" => (ZExp.var 3 : ZExp 5)
local notation "q" => (ZExp.var 4 : ZExp 5)

/-- `T_tt` of `eq:stress`. -/
def Ttt : Frac 5 := EB2 * (⟨d, Sg⟩ + ⟨sx * a ^ 2, Sg⟩)
/-- `T_tφ` of `eq:stress`. -/
def Ttp : Frac 5 := -(EB2 * (⟨d * a * sx, Sg⟩ + ⟨sx * a * Pp, Sg⟩))
/-- `T_φφ` of `eq:stress`. -/
def Tpp : Frac 5 := EB2 * (⟨d * a ^ 2 * sx ^ 2, Sg⟩ + ⟨sx * Pp ^ 2, Sg⟩)
/-- `T_rr` of `eq:stress`. -/
def Trr : Frac 5 := -(EB2 * ⟨Sg, d⟩)
/-- `T_xx` of `eq:stress`. -/
def Txx : Frac 5 := EB2 * ⟨Sg, sx⟩

/-- The contraction of `(d/Σ) p² − (Σ/d) dr² + (Σ/s) dx² + (s/Σ) b²` with the inverse metric is
`0`: the right-hand side of `eq:EM` is trace-free. -/
theorem stress_trace :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (Frac.eqn (itt * ⟨d + sx * a ^ 2, Sg⟩
        - Frac.ofZ 2 * (itp * ⟨d * a * sx + sx * a * Pp, Sg⟩)
        + ipp * ⟨d * a ^ 2 * sx ^ 2 + sx * Pp ^ 2, Sg⟩ - irr * ⟨Sg, d⟩ + ixx * ⟨Sg, sx⟩)
        (Frac.ofZ 0))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [itt, itp, ipp, irr, ixx, Pp, Sg, sx]
    ring)

end Stress

/-! ## The Einstein–Maxwell equation at `d = Δ` -/

section Einstein

open LeanProofs.IPRA.Geometry.KerrNewmanRicci (Nn Vf Uf knHyps)
open LeanProofs.IPRA.Geometry.KerrNewmanMaxwell (EB2 Ef Bf En Bn)

/-- The variables `r, x, a, d, v, w` of `Geometry/KerrNewmanRicci` among
`r, x, a, d, v, w, m, q`. -/
def ι₆ : Fin 6 → Fin 8 := ![0, 1, 2, 3, 4, 5]

/-- The variables `r, x, a, d, q` of `Geometry/KerrNewmanMaxwell` among
`r, x, a, d, v, w, m, q`. -/
def ι₅ : Fin 5 → Fin 8 := ![0, 1, 2, 3, 7]

theorem ι₆_0 : ι₆ 0 = 0 := rfl
theorem ι₆_1 : ι₆ 1 = 1 := rfl
theorem ι₆_2 : ι₆ 2 = 2 := rfl
theorem ι₆_3 : ι₆ 3 = 3 := rfl
theorem ι₆_4 : ι₆ 4 = 4 := rfl
theorem ι₆_5 : ι₆ 5 = 5 := rfl
theorem ι₅_0 : ι₅ 0 = 0 := rfl
theorem ι₅_1 : ι₅ 1 = 1 := rfl
theorem ι₅_2 : ι₅ 2 = 2 := rfl
theorem ι₅_3 : ι₅ 3 = 3 := rfl
theorem ι₅_4 : ι₅ 4 = 7 := rfl

local notation "Q" => (ZExp.var 7 : ZExp 8)
local notation "W" => (ZExp.var 5 : ZExp 8)
local notation "Σ₈" => ZExp.rename ι₆ LeanProofs.IPRA.Geometry.KerrNewmanBase.Sg

/-- `thm:KN`: `U = q²/Σ²` for the Kerr–Newman radial function. -/
theorem kn_U :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp knHyps (Frac.eqn (Frac.rename ι₆ Uf) ⟨Q ^ 2, Σ₈ ^ 2⟩)) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Frac.rename_num, Frac.rename_den, eval_rename, Uf, Vf, Nn,
      KerrNewmanBase.Sg, ι₆_0, ι₆_1, ι₆_2, ι₆_3, ι₆_4, ι₆_5]
    obtain ⟨h₁, h₂, h₃⟩ := h
    rw [h₁, h₂, h₃]
    ring)

/-- `thm:KN`: `V = q²/Σ²` for the Kerr–Newman radial function. -/
theorem kn_V :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp knHyps (Frac.eqn (Frac.rename ι₆ Vf) ⟨Q ^ 2, Σ₈ ^ 2⟩)) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Frac.rename_num, Frac.rename_den, eval_rename, Vf, Nn,
      KerrNewmanBase.Sg, ι₆_0, ι₆_1, ι₆_2, ι₆_3, ι₆_4, ι₆_5]
    obtain ⟨h₁, h₂, _⟩ := h
    rw [h₁, h₂]
    ring)

/-- `eq:sumSquares` in the common variables: `E² + 𝓑² = q²/Σ²`. -/
theorem kn_field :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp [] (Frac.eqn (Frac.rename ι₅ EB2) ⟨Q ^ 2, Σ₈ ^ 2⟩)) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Frac.rename_num, Frac.rename_den, eval_rename, EB2, Ef, Bf, En, Bn,
      KerrNewmanBase.Sg, KerrNewmanMaxwell.Sg, ι₆_0, ι₆_1, ι₆_2, ι₆_3, ι₆_4, ι₆_5, ι₅_0, ι₅_1,
      ι₅_2, ι₅_3, ι₅_4]
    ring)

/-- The scalar curvature `(2 − w)/Σ` of the Kerr–Newman metric is `0`. -/
theorem kn_scalar :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp knHyps (Frac.eqn ⟨2 - W, Σ₈⟩ (Frac.ofZ 0))) :=
  derive_imp _ _ (by
    frac_poly R ρ h [eval_rename, KerrNewmanBase.Sg, ι₆_0, ι₆_1, ι₆_2, ι₆_3, ι₆_4, ι₆_5]
    obtain ⟨_, _, h₃⟩ := h
    rw [h₃]
    ring)

/-- Start the certificate of an entry of the Einstein–Maxwell equation. -/
local macro "em_poly" : tactic =>
  `(tactic| (
    frac_poly R ρ h [Frac.rename_num, Frac.rename_den, eval_rename, Rtt, Rtp, Rpp, Rrr, Rxx,
      Ttt, Ttp, Tpp, Trr, Txx, Uf, Vf, Nn, EB2, Ef, Bf, En, Bn, KerrNewmanBase.Sg,
      KerrNewmanBase.sx, KerrNewmanConnection.Pp, KerrNewmanMaxwell.Sg, KerrNewmanMaxwell.sx,
      KerrNewmanMaxwell.Pp, ι₆_0, ι₆_1, ι₆_2, ι₆_3, ι₆_4, ι₆_5, ι₅_0, ι₅_1, ι₅_2, ι₅_3, ι₅_4]
    obtain ⟨h₁, h₂, h₃⟩ := h
    try rw [h₃]
    rw [h₂, h₁]
    ring))

/-- `eq:EM`, entry `tt`: `R_tt = T_tt` for the Kerr–Newman radial function. -/
theorem einstein_tt :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp knHyps (Frac.eqn (Frac.rename ι₆ Rtt) (Frac.rename ι₅ Ttt))) :=
  derive_imp _ _ (by em_poly)

/-- `eq:EM`, entry `tφ`: `R_tφ = T_tφ` for the Kerr–Newman radial function. -/
theorem einstein_tp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp knHyps (Frac.eqn (Frac.rename ι₆ Rtp) (Frac.rename ι₅ Ttp))) :=
  derive_imp _ _ (by em_poly)

/-- `eq:EM`, entry `φφ`: `R_φφ = T_φφ` for the Kerr–Newman radial function. -/
theorem einstein_pp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp knHyps (Frac.eqn (Frac.rename ι₆ Rpp) (Frac.rename ι₅ Tpp))) :=
  derive_imp _ _ (by em_poly)

/-- `eq:EM`, entry `rr`: `R_rr = T_rr` for the Kerr–Newman radial function. -/
theorem einstein_rr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp knHyps (Frac.eqn (Frac.rename ι₆ Rrr) (Frac.rename ι₅ Trr))) :=
  derive_imp _ _ (by em_poly)

/-- `eq:EM`, entry `xx`: `R_xx = T_xx` for the Kerr–Newman radial function. -/
theorem einstein_xx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp knHyps (Frac.eqn (Frac.rename ι₆ Rxx) (Frac.rename ι₅ Txx))) :=
  derive_imp _ _ (by em_poly)

/-! ## The radial reduction (`prop:radial`, converse direction)

"Conversely these two scalar equations imply those two values of `U`, `V`, so all the tensor
equations follow": the hypotheses are only `eq:radial`, `d″ = 2` and
`r² − a² + d − r d′ = q²`, for an unspecified radial function. -/

/-- The radial equations `eq:radial`: `w = 2` and `N = q²`. -/
abbrev radialHyps : List (ZExp 8 × ZExp 8) := [(W, 2), (ZExp.rename ι₆ Nn, Q ^ 2)]

/-- `eq:radial` gives `U = q²/Σ²`. -/
theorem radial_U :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp radialHyps (Frac.eqn (Frac.rename ι₆ Uf) ⟨Q ^ 2, Σ₈ ^ 2⟩)) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Frac.rename_num, Frac.rename_den, eval_rename, Uf, Vf, Nn,
      KerrNewmanBase.Sg, ι₆_0, ι₆_1, ι₆_2, ι₆_3, ι₆_4, ι₆_5]
    obtain ⟨h₁, h₂⟩ := h
    rw [h₁, h₂]
    ring)

/-- `eq:radial` gives `V = q²/Σ²`. -/
theorem radial_V :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp radialHyps (Frac.eqn (Frac.rename ι₆ Vf) ⟨Q ^ 2, Σ₈ ^ 2⟩)) :=
  derive_imp _ _ (by
    frac_poly R ρ h [Frac.rename_num, Frac.rename_den, eval_rename, Vf, Nn,
      KerrNewmanBase.Sg, ι₆_0, ι₆_1, ι₆_2, ι₆_3, ι₆_4, ι₆_5]
    obtain ⟨_, h₂⟩ := h
    rw [h₂])

/-- Start the certificate of an entry of the Einstein–Maxwell equation from `eq:radial`. -/
local macro "rad_poly" : tactic =>
  `(tactic| (
    frac_poly R ρ h [Frac.rename_num, Frac.rename_den, eval_rename, Rtt, Rtp, Rpp, Rrr, Rxx,
      Ttt, Ttp, Tpp, Trr, Txx, Uf, Vf, Nn, EB2, Ef, Bf, En, Bn, KerrNewmanBase.Sg,
      KerrNewmanBase.sx, KerrNewmanConnection.Pp, KerrNewmanMaxwell.Sg, KerrNewmanMaxwell.sx,
      KerrNewmanMaxwell.Pp, ι₆_0, ι₆_1, ι₆_2, ι₆_3, ι₆_4, ι₆_5, ι₅_0, ι₅_1, ι₅_2, ι₅_3, ι₅_4]
    obtain ⟨h₁, h₂⟩ := h
    try rw [h₁]
    rw [h₂]
    ring))

/-- `eq:EM`, entry `tt`, from `eq:radial`. -/
theorem radial_tt :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp radialHyps (Frac.eqn (Frac.rename ι₆ Rtt) (Frac.rename ι₅ Ttt))) :=
  derive_imp _ _ (by rad_poly)

/-- `eq:EM`, entry `tφ`, from `eq:radial`. -/
theorem radial_tp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp radialHyps (Frac.eqn (Frac.rename ι₆ Rtp) (Frac.rename ι₅ Ttp))) :=
  derive_imp _ _ (by rad_poly)

/-- `eq:EM`, entry `φφ`, from `eq:radial`. -/
theorem radial_pp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp radialHyps (Frac.eqn (Frac.rename ι₆ Rpp) (Frac.rename ι₅ Tpp))) :=
  derive_imp _ _ (by rad_poly)

/-- `eq:EM`, entry `rr`, from `eq:radial`. -/
theorem radial_rr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp radialHyps (Frac.eqn (Frac.rename ι₆ Rrr) (Frac.rename ι₅ Trr))) :=
  derive_imp _ _ (by rad_poly)

/-- `eq:EM`, entry `xx`, from `eq:radial`. -/
theorem radial_xx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp radialHyps (Frac.eqn (Frac.rename ι₆ Rxx) (Frac.rename ι₅ Txx))) :=
  derive_imp _ _ (by rad_poly)

end Einstein

end LeanProofs.IPRA.Geometry.KerrNewmanEinstein
