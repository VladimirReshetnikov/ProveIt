import IPRADerivations.Core.PolynomialImplications

/-!
# Uniqueness of the circumcentre (`triangle_formulas_ipra`, `thm:sine`)

Packet: `geometry/triangle_formulas_ipra`. `Geometry/Circumcircle` shows that the point
`O = (w U − y V, x V − z U)` (the circumcentre times `2 t`) is equidistant from the vertices
`(0, 0)`, `(x, y)`, `(z, w)`, with `U = x² + y²`, `V = z² + w²`, `t = x w − y z`. This module
derives the converse part of `thm:sine`: a point equidistant from the three vertices is that
point.

* `bisector_x`, `bisector_y`: `|P|² = |P − (x, y)|²` is the linear equation
  `2 (x P₁ + y P₂) = U`, and likewise for `(z, w)`;
* `circumcentre_x`, `circumcentre_y`: if `|P|² = |P − (x, y)|² = |P − (z, w)|²`, then
  `2 t P₁ = U w − V y` and `2 t P₂ = V x − U z`.

For a nondegenerate triangle (`t ≠ 0`) this determines `P`; the cancellation of `2 t` and the
reading `2 h R = a b c` through square roots are not derived here.
-/

namespace LeanProofs.IPRA.Geometry.CircumcentreUnique

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ZExp

local notation "x" => (ZExp.var 0 : ZExp 6)
local notation "y" => (ZExp.var 1 : ZExp 6)
local notation "z" => (ZExp.var 2 : ZExp 6)
local notation "w" => (ZExp.var 3 : ZExp 6)
local notation "P₁" => (ZExp.var 4 : ZExp 6)
local notation "P₂" => (ZExp.var 5 : ZExp 6)

/-- `P` is equidistant from `(0, 0)`, `(x, y)` and `(z, w)`. -/
abbrev equidistant : List (ZExp 6 × ZExp 6) :=
  [(P₁ ^ 2 + P₂ ^ 2, (P₁ - x) ^ 2 + (P₂ - y) ^ 2), (P₁ ^ 2 + P₂ ^ 2, (P₁ - z) ^ 2 + (P₂ - w) ^ 2)]

theorem bisector_x :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp equidistant (2 * (x * P₁ + y * P₂), x ^ 2 + y ^ 2)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, _⟩ := h
    linear_combination h₁)

theorem bisector_y :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp equidistant (2 * (z * P₁ + w * P₂), z ^ 2 + w ^ 2)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨_, h₂⟩ := h
    linear_combination h₂)

theorem circumcentre_x :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp equidistant (2 * (x * w - y * z) * P₁, (x ^ 2 + y ^ 2) * w - (z ^ 2 + w ^ 2) * y)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂⟩ := h
    linear_combination ρ 3 * h₁ - ρ 1 * h₂)

theorem circumcentre_y :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp equidistant (2 * (x * w - y * z) * P₂, (z ^ 2 + w ^ 2) * x - (x ^ 2 + y ^ 2) * z)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂⟩ := h
    linear_combination ρ 0 * h₂ - ρ 2 * h₁)

end LeanProofs.IPRA.Geometry.CircumcentreUnique
