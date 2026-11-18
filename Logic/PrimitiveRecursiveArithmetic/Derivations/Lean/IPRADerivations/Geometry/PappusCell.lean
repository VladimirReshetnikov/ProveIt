import IPRADerivations.Core.PolynomialImplications

/-!
# Exact cell identities of Pappus's centroid theorems (`pappus_centroid_ipra_2026-11-15`)

Packet: `geometry/pappus_centroid_ipra_2026-11-15`. `Geometry/PappusSegment` derives the
midpoint moment of a segment (`lem:segment-moment`). This module derives the exact algebra of
the volume theorem and of the polygon approximation of `τ`, as implications between integer
polynomial equations (`Core/PolynomialImplications`); `τ` is an integer parameter standing for
the turn constant.

* `cell_pappus` (`prop:cell-pappus`): for the rectangle `[a, b] × [c, d]` rotated about the
  axis, with doubled volume `2 V = τ (b² − a²)(d − c)` and doubled first moment
  `2 M = (a + b)(b − a)(d − c)`: `2 V = τ · 2 M`, the cleared form of `V(C) = τ M(C)`;
* `cell_pappus_centroid`: with area `A = (b − a)(d − c)` and doubled centroid radius
  `2 r̄ = a + b`: `2 V = τ A · 2 r̄`, the cleared form of `V = τ A r̄`;
* `grid_pappus_two` (`thm:grid-pappus`, two cells): `V₁ = τ M₁` and `V₂ = τ M₂` give
  `V₁ + V₂ = τ (M₁ + M₂)`;
* `half_angle_gap` (`lem:polygon-estimates`): `2 c₁² = 1 + c₀` gives
  `2 (1 − c₁)(1 + c₁) = 1 − c₀`, the identity behind `1 − c₁ ≤ (1 − c₀) / 2`;
* `frustum_split` (`lem:frustum-squeeze`): `q l − p h = (q − p) l + p (l − h)`.

The limits of the packet (the constant `τ` from nested polygons, rectifiable curves, Jordan
laminae), the inequalities and the sums over arbitrarily many cells are not derived.
-/

namespace LeanProofs.IPRA.Geometry.PappusCell

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ZExp

/-! ## One cell: `a, b, c, d, τ, V, M` -/

section Cell

local notation "a" => (ZExp.var 0 : ZExp 7)
local notation "b" => (ZExp.var 1 : ZExp 7)
local notation "c" => (ZExp.var 2 : ZExp 7)
local notation "d" => (ZExp.var 3 : ZExp 7)
local notation "τ" => (ZExp.var 4 : ZExp 7)
local notation "V" => (ZExp.var 5 : ZExp 7)
local notation "M" => (ZExp.var 6 : ZExp 7)

theorem cell_pappus :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 7)
      (imp [(2 * V, τ * (b ^ 2 - a ^ 2) * (d - c)), (2 * M, (a + b) * (b - a) * (d - c))]
        (2 * V, τ * (2 * M))) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂⟩ := h
    linear_combination h₁ - ρ 4 * h₂)

theorem cell_pappus_centroid :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 7)
      (imp [(2 * V, τ * (b ^ 2 - a ^ 2) * (d - c))] (2 * V, τ * ((b - a) * (d - c)) * (a + b))) :=
  derive_imp _ _ (by ipra_poly R ρ h; linear_combination h)

end Cell

/-! ## Two cells: `τ, V₁, M₁, V₂, M₂` -/

section Grid

local notation "τ" => (ZExp.var 0 : ZExp 5)
local notation "V₁" => (ZExp.var 1 : ZExp 5)
local notation "M₁" => (ZExp.var 2 : ZExp 5)
local notation "V₂" => (ZExp.var 3 : ZExp 5)
local notation "M₂" => (ZExp.var 4 : ZExp 5)

theorem grid_pappus_two :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [(V₁, τ * M₁), (V₂, τ * M₂)] (V₁ + V₂, τ * (M₁ + M₂))) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂⟩ := h
    linear_combination h₁ + h₂)

end Grid

/-! ## The polygon recursion and the frustum split -/

section Polygon

local notation "c₀" => (ZExp.var 0 : ZExp 2)
local notation "c₁" => (ZExp.var 1 : ZExp 2)

theorem half_angle_gap :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2)
      (imp [(2 * c₁ ^ 2, 1 + c₀)] (2 * (1 - c₁) * (1 + c₁), 1 - c₀)) :=
  derive_imp _ _ (by ipra_poly R ρ h; linear_combination (-1 : R) * h)

end Polygon

section Frustum

local notation "p" => (ZExp.var 0 : ZExp 4)
local notation "q" => (ZExp.var 1 : ZExp 4)
local notation "l" => (ZExp.var 2 : ZExp 4)
local notation "hh" => (ZExp.var 3 : ZExp 4)

theorem frustum_split :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 4)
      (imp [] (q * l - p * hh, (q - p) * l + p * (l - hh))) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

end Frustum

end LeanProofs.IPRA.Geometry.PappusCell
