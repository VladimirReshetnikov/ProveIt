import IPRADerivations.Geometry.KerrNewmanEinstein

/-!
# The static Ricci tensor as a specialization of the radial-function identity

Packet: `geometry/four_metrics_ipra_2026-11-15`, Subsection "Reissner–Nordström and its
elementary verification", after `eq:staticRic`:

"These identities also follow from `lem:offshell` with `d = r² f`, `a = 0`; the substitution
`d′ = 2 r f + r² f′`, `d″ = 2 f + 4 r f′ + r² f″` gives exactly the four entries."

The four entries are `eq:staticRic` for the metric `−f dt² + f⁻¹ dr² + r² dΩ²`:

`R_tt = f (f″/2 + f′/r)`, `R_rr = −f⁻¹ (f″/2 + f′/r)`, `R_θθ = 1 − f − r f′`,
`R_φφ = sin²θ (1 − f − r f′)`.

Here `f`, `f′`, `f″` are three further indeterminates `f, f₁, f₂`, and the entries of
`eq:offshell` (`Geometry/KerrNewmanEinstein.Rtt`, …, in the indeterminates
`r, x, a, d, v, w`) are renamed into the list `r, x, a, d, v, w, f, f₁, f₂`
(`Foundations/ExpressionRenaming`). Under the hypotheses `a = 0`, `d = r² f`,
`v = 2 r f + r² f₁`, `w = 2 f + 4 r f₁ + r² f₂` (`staticHyps`):

* `static_N`: `N = r² − a² + d − r v = r² (1 − f − r f₁)`;
* `static_tt`: `R_tt = f (f₂/2 + f₁/r)`;
* `static_rr`: `R_rr = −(1/f) (f₂/2 + f₁/r)`;
* `static_xx`: `R_xx = (1 − f − r f₁)/s`, that is `R_θθ = s R_xx = 1 − f − r f₁`, since
  `dx²/s = dθ²` for `x = cos θ` ("Returning to angular notation");
* `static_pp`: `R_φφ = s (1 − f − r f₁)`, with `s = sin²θ`;
* `static_tp`: `R_tφ = 0`.

Every statement is an implication between polynomial equations (the conclusion is an identity
of fractions cleared of denominators), a closed sentence of iPRA certified in every commutative
ring; its reading as an equality of rational functions uses `r f s ≠ 0`.
-/

namespace LeanProofs.IPRA.Geometry.KerrNewmanStatic

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Geometry.KerrNewmanRicci (Nn Vf Uf)
open LeanProofs.IPRA.Geometry.KerrNewmanEinstein (Rtt Rtp Rpp Rrr Rxx)
open ZExp

/-- The variables `r, x, a, d, v, w` among `r, x, a, d, v, w, f, f₁, f₂`. -/
def ι : Fin 6 → Fin 9 := ![0, 1, 2, 3, 4, 5]

theorem ι_0 : ι 0 = 0 := rfl
theorem ι_1 : ι 1 = 1 := rfl
theorem ι_2 : ι 2 = 2 := rfl
theorem ι_3 : ι 3 = 3 := rfl
theorem ι_4 : ι 4 = 4 := rfl
theorem ι_5 : ι 5 = 5 := rfl

local notation "R" => (ZExp.var 0 : ZExp 9)
local notation "X" => (ZExp.var 1 : ZExp 9)
local notation "A" => (ZExp.var 2 : ZExp 9)
local notation "D" => (ZExp.var 3 : ZExp 9)
local notation "V" => (ZExp.var 4 : ZExp 9)
local notation "W" => (ZExp.var 5 : ZExp 9)
local notation "F" => (ZExp.var 6 : ZExp 9)
local notation "F₁" => (ZExp.var 7 : ZExp 9)
local notation "F₂" => (ZExp.var 8 : ZExp 9)

/-- The static substitution: `a = 0`, `d = r² f`, `d′ = 2 r f + r² f′`,
`d″ = 2 f + 4 r f′ + r² f″`. -/
abbrev staticHyps : List (ZExp 9 × ZExp 9) :=
  [(A, 0), (D, R ^ 2 * F), (V, 2 * R * F + R ^ 2 * F₁), (W, 2 * F + 4 * R * F₁ + R ^ 2 * F₂)]

/-- `N = r² − a² + d − r v = r² (1 − f − r f₁)`. -/
theorem static_N :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 9)
      (imp staticHyps (ZExp.rename ι Nn, R ^ 2 * (1 - F - R * F₁))) :=
  derive_imp _ _ (by
    ipra_poly S ρ h [eval_rename, Nn, ι_0, ι_1, ι_2, ι_3, ι_4, ι_5]
    obtain ⟨h₁, h₂, h₃, _⟩ := h
    rw [h₃, h₂, h₁]
    ring)

/-- Start the certificate of an entry of `eq:staticRic`. -/
local macro "st_poly" : tactic =>
  `(tactic| (
    frac_poly S ρ h [Frac.rename_num, Frac.rename_den, eval_rename, Rtt, Rtp, Rpp, Rrr, Rxx,
      Uf, Vf, Nn, KerrNewmanBase.Sg, KerrNewmanBase.sx, KerrNewmanConnection.Pp, ι_0, ι_1, ι_2,
      ι_3, ι_4, ι_5]
    obtain ⟨h₁, h₂, h₃, h₄⟩ := h
    try rw [h₄]
    rw [h₃, h₂, h₁]
    ring))

/-- `eq:staticRic`: `R_tt = f (f″/2 + f′/r)`. -/
theorem static_tt :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 9)
      (imp staticHyps (Frac.eqn (Frac.rename ι Rtt) (Frac.ofZ F * (⟨F₂, 2⟩ + ⟨F₁, R⟩)))) :=
  derive_imp _ _ (by st_poly)

/-- `eq:staticRic`: `R_rr = −f⁻¹ (f″/2 + f′/r)`. -/
theorem static_rr :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 9)
      (imp staticHyps (Frac.eqn (Frac.rename ι Rrr) (-(⟨1, F⟩ * (⟨F₂, 2⟩ + ⟨F₁, R⟩))))) :=
  derive_imp _ _ (by st_poly)

/-- `eq:staticRic`: `R_xx = (1 − f − r f′)/s`, that is `R_θθ = 1 − f − r f′`. -/
theorem static_xx :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 9)
      (imp staticHyps (Frac.eqn (Frac.rename ι Rxx) ⟨1 - F - R * F₁, 1 - X ^ 2⟩)) :=
  derive_imp _ _ (by st_poly)

/-- `eq:staticRic`: `R_φφ = s (1 − f − r f′)`, with `s = sin²θ`. -/
theorem static_pp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 9)
      (imp staticHyps (Frac.eqn (Frac.rename ι Rpp)
        (Frac.ofZ ((1 - X ^ 2) * (1 - F - R * F₁))))) :=
  derive_imp _ _ (by st_poly)

/-- `R_tφ = 0` for the static metric. -/
theorem static_tp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 9)
      (imp staticHyps (Frac.eqn (Frac.rename ι Rtp) (Frac.ofZ 0))) :=
  derive_imp _ _ (by st_poly)

end LeanProofs.IPRA.Geometry.KerrNewmanStatic
