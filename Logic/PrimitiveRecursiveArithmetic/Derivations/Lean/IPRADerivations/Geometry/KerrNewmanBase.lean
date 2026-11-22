import IPRADerivations.Foundations.FormalDerivation

/-!
# The base block of the radial-function metric: connection (`four_metrics_ipra`)

Packet: `geometry/four_metrics_ipra_2026-11-15`, proof of `lem:offshell` ("Radial-function Ricci
identity"), Subsection "The base block, including all required traces". The radial function is
left unspecified: "Write `d = Δ(r)`, `v = Δ′(r)`, and `w = Δ″(r)`. Algebraically, these are three
independent indeterminates, with `∂_r d = v`, `∂_r v = w`, and `∂_x d = ∂_x v = 0`. No derivative
of `w` is used. This is a finite second-jet calculation."

With `Σ = r² + a² x²`, `s = 1 − x²` and the base metric `h = diag(Σ/d, Σ/s)` in the coordinates
`(r, x)`, the derivations `∂_r`, `∂_x` are the formal derivations of
`Foundations/FormalDerivation` on the polynomial expressions in `r, x, a, d, v, w`, extended to
fractions by the quotient rule. Each statement is an identity of fractions cleared of
denominators, a closed sentence of iPRA certified in every commutative ring.

* `inverse_rr`, `inverse_xx`: `h^{rr} h_{rr} = 1`, `h^{xx} h_{xx} = 1`;
* `gamma_rrr`, `gamma_rrx`, `gamma_rxx`, `gamma_xrr`, `gamma_xrx`, `gamma_xxx` (`eq:basegamma`):
  the six connection coefficients `γ^i_{jk} = ½ h^{ii} (∂_j h_{ik} + ∂_k h_{ij} − ∂_i h_{jk})`
  of the diagonal metric `h` are
  `γ^r_{rr} = r/Σ − v/(2d)`, `γ^r_{rx} = a² x/Σ`, `γ^r_{xx} = −r d/(Σ s)`,
  `γ^x_{rr} = −a² x s/(Σ d)`, `γ^x_{rx} = r/Σ`, `γ^x_{xx} = a² x/Σ + x/s`;
* `d_trace_r`, `d_trace_x`: "the derivatives `∂_r(v/(2d)) = w/(2d) − v²/(2d²)` and
  `∂_x(−x/s) = −(1 + x²)/s²`";
* `mixed_entry`: the displayed computation of `R_{rx}`,
  `0 − ∂_x(v/(2d)) + (a² x/Σ)(v/(2d)) + (r/Σ)(−x/s) − (a² x v/(2dΣ) − r x/(sΣ)) = 0`.

The derivation `∂_r` is set to `0` on `w` (its derivative is not used). The curvature
`eq:basecurv` of `h`, the fiber block and the assembly of `lem:offshell` are not derived here.
-/

namespace LeanProofs.IPRA.Geometry.KerrNewmanBase

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ZExp

local notation "r" => (ZExp.var 0 : ZExp 6)
local notation "x" => (ZExp.var 1 : ZExp 6)
local notation "a" => (ZExp.var 2 : ZExp 6)
local notation "d" => (ZExp.var 3 : ZExp 6)
local notation "v" => (ZExp.var 4 : ZExp 6)
local notation "w" => (ZExp.var 5 : ZExp 6)

/-- `∂_r`: `r ↦ 1`, `d ↦ v`, `v ↦ w`, and `0` on `x`, `a`, `w`. -/
def δr : Fin 6 → ZExp 6
  | ⟨0, _⟩ => 1
  | ⟨3, _⟩ => var 4
  | ⟨4, _⟩ => var 5
  | _ => 0

/-- `∂_x`: `x ↦ 1`, and `0` on the other variables. -/
def δx : Fin 6 → ZExp 6
  | ⟨1, _⟩ => 1
  | _ => 0

theorem δr_0 : δr 0 = 1 := rfl
theorem δr_1 : δr 1 = 0 := rfl
theorem δr_2 : δr 2 = 0 := rfl
theorem δr_3 : δr 3 = var 4 := rfl
theorem δr_4 : δr 4 = var 5 := rfl
theorem δr_5 : δr 5 = 0 := rfl
theorem δx_0 : δx 0 = 0 := rfl
theorem δx_1 : δx 1 = 1 := rfl
theorem δx_2 : δx 2 = 0 := rfl
theorem δx_3 : δx 3 = 0 := rfl
theorem δx_4 : δx 4 = 0 := rfl
theorem δx_5 : δx 5 = 0 := rfl

/-- `Σ = r² + a² x²`. -/
def Sg : ZExp 6 := r ^ 2 + a ^ 2 * x ^ 2
/-- `s = 1 − x²`. -/
def sx : ZExp 6 := 1 - x ^ 2

/-- `h_{rr} = Σ/d`. -/
def hrr : Frac 6 := ⟨Sg, d⟩
/-- `h_{xx} = Σ/s`. -/
def hxx : Frac 6 := ⟨Sg, sx⟩
/-- `h^{rr} = d/Σ`. -/
def irr : Frac 6 := ⟨d, Sg⟩
/-- `h^{xx} = s/Σ`. -/
def ixx : Frac 6 := ⟨sx, Sg⟩

/-- Certificates of this module: unfold the definitions and the two derivations. -/
macro "kn_poly" : tactic =>
  `(tactic| (frac_poly R ρ h [hrr, hxx, irr, ixx, Sg, sx, δr_0, δr_1, δr_2, δr_3, δr_4, δr_5,
      δx_0, δx_1, δx_2, δx_3, δx_4, δx_5]; ring))

/-! ## The inverse -/

theorem inverse_rr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6) (imp [] (Frac.eqn (irr * hrr) (Frac.ofZ 1))) :=
  derive_imp _ _ (by kn_poly)

theorem inverse_xx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6) (imp [] (Frac.eqn (ixx * hxx) (Frac.ofZ 1))) :=
  derive_imp _ _ (by kn_poly)

/-! ## The six connection coefficients (`eq:basegamma`) -/

/-- `γ^r_{rr} = ½ h^{rr} ∂_r h_{rr} = r/Σ − v/(2d)`. -/
theorem gamma_rrr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.half (irr * Frac.d δr hrr)) (⟨r, Sg⟩ - ⟨v, 2 * d⟩))) :=
  derive_imp _ _ (by kn_poly)

/-- `γ^r_{rx} = ½ h^{rr} ∂_x h_{rr} = a² x/Σ`. -/
theorem gamma_rrx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.half (irr * Frac.d δx hrr)) ⟨a ^ 2 * x, Sg⟩)) :=
  derive_imp _ _ (by kn_poly)

/-- `γ^r_{xx} = −½ h^{rr} ∂_r h_{xx} = −r d/(Σ s)`. -/
theorem gamma_rxx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (-(Frac.half (irr * Frac.d δr hxx))) (-⟨r * d, Sg * sx⟩))) :=
  derive_imp _ _ (by kn_poly)

/-- `γ^x_{rr} = −½ h^{xx} ∂_x h_{rr} = −a² x s/(Σ d)`. -/
theorem gamma_xrr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (-(Frac.half (ixx * Frac.d δx hrr))) (-⟨a ^ 2 * x * sx, Sg * d⟩))) :=
  derive_imp _ _ (by kn_poly)

/-- `γ^x_{rx} = ½ h^{xx} ∂_r h_{xx} = r/Σ`. -/
theorem gamma_xrx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.half (ixx * Frac.d δr hxx)) ⟨r, Sg⟩)) :=
  derive_imp _ _ (by kn_poly)

/-- `γ^x_{xx} = ½ h^{xx} ∂_x h_{xx} = a² x/Σ + x/s`. -/
theorem gamma_xxx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.half (ixx * Frac.d δx hxx)) (⟨a ^ 2 * x, Sg⟩ + ⟨x, sx⟩))) :=
  derive_imp _ _ (by kn_poly)

/-! ## The two derivatives of the traces and the mixed entry -/

/-- `∂_r (v/(2d)) = w/(2d) − v²/(2d²)`. -/
theorem d_trace_r :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δr ⟨v, 2 * d⟩) (⟨w, 2 * d⟩ - ⟨v ^ 2, 2 * d ^ 2⟩))) :=
  derive_imp _ _ (by kn_poly)

/-- `∂_x (−x/s) = −(1 + x²)/s²`. -/
theorem d_trace_x :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn (Frac.d δx (-⟨x, sx⟩)) (-⟨1 + x ^ 2, sx ^ 2⟩))) :=
  derive_imp _ _ (by kn_poly)

/-- The mixed entry `R_{rx}` of `eq:base-result`:
`0 − ∂_x(v/(2d)) + (a² x/Σ)(v/(2d)) + (r/Σ)(−x/s) − (a² x v/(2dΣ) − r x/(sΣ)) = 0`. -/
theorem mixed_entry :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (Frac.eqn
        (Frac.ofZ 0 - Frac.d δx ⟨v, 2 * d⟩ + ⟨a ^ 2 * x, Sg⟩ * ⟨v, 2 * d⟩ +
          ⟨r, Sg⟩ * (-⟨x, sx⟩) - (⟨a ^ 2 * x * v, 2 * d * Sg⟩ - ⟨r * x, sx * Sg⟩))
        (Frac.ofZ 0))) :=
  derive_imp _ _ (by kn_poly)

end LeanProofs.IPRA.Geometry.KerrNewmanBase
