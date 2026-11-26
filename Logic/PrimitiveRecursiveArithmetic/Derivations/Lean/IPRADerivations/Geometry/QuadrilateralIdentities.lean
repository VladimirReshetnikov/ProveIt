import IPRADerivations.Geometry.TriangleCentres

/-!
# Quadrilaterals: Varignon, the diagonal area bound and Bretschneider's identity

Packet: `geometry/euclidean_geometry_ipra_2026-11-22`, `chapters/polygons.tex`, Theorems `poly:parallelogram`,
`poly:varignon`, `poly:diagonal-area`, `poly:bretschneider` and Corollary `poly:brahmagupta`. Points have two
integer-term coordinates, with `dot`, `det`, `nsq` of `Geometry/TriangleCentres`. As iPRA derivations:

* `diagonal_sq_diff`, `diagonal_dot`: for the parallelogram on `u, v`, "Their squared-length difference is
  `4 u · v`" and "Their dot product is `N(v) − N(u)`" (rectangle and rhombus criteria);
* `varignon_area`: "`[A, B] + [B, C] + [C, D] + [D, A] = [C − A, D − B]`", the doubled signed area of a
  quadrilateral by its diagonals; the midpoint parallelogram has sides `(C − A)/2`, `(D − B)/2`;
* `diagonal_area_bound`: "The Gram identity bounds the determinant squared by `p² q²`":
  `[e, f]² ≤ |e|² |f|²`;
* `brahmagupta_factor`: "`16 (s − a)(s − b)(s − c)(s − d) = 4 (X + Y)² − E²`" with `X = ab`, `Y = cd`,
  `E = a² + b² − c² − d²`;
* `bretschneider`: with the cosine–sine pairs `(x, u)/w` and `(y, v)/τ` of the opposite angles
  (`x² + u² = w²`, `y² + v² = τ²`), the cosine law `w τ E = 2 X x τ − 2 Y y w` and the area
  `w τ · 2K = X u τ + Y v w`:
  `(w τ)² (4 (X + Y)² − E² − 4 (2K)²) = 8 X Y · w τ (w τ + x y − u v)`, the cleared form of
  "`K₀² = (s − a)(s − b)(s − c)(s − d) − (abcd/2)(1 + xy − uv)`";
* `bretschneider_defect`: "`2 (1 + xy − uv) = (x + y)² + (u − v)² ≥ 0`", cleared:
  `0 ≤ 2 w τ (w τ + x y − u v)`.

Not derived: the convexity hypotheses, the equality cases, and the square root in Brahmagupta's formula.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.QuadrilateralIdentities

open_ipra
open LeanProofs.IPRA.Geometry.TriangleCentres (dot det nsq)

variable {n : ℕ} {Γ : List (Fm PTm n)}

attribute [local ipra_defs] dot det nsq

/-- The diagonals of the parallelogram on `u, v`: `|u + v|² − |v − u|² = 4 u · v`. -/
theorem diagonal_sq_diff (u₁ u₂ v₁ v₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (nsq (u₁ + v₁) (u₂ + v₂) - nsq (v₁ - u₁) (v₂ - u₂))
      (ZT.natLit 4 * dot u₁ u₂ v₁ v₂) := by
  ipra_lc

/-- The diagonals of the parallelogram on `u, v`: `(u + v) · (v − u) = |v|² − |u|²`. -/
theorem diagonal_dot (u₁ u₂ v₁ v₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (dot (u₁ + v₁) (u₂ + v₂) (v₁ - u₁) (v₂ - u₂)) (nsq v₁ v₂ - nsq u₁ u₂) := by
  ipra_lc

/-- The doubled signed area of a quadrilateral: `[A, B] + [B, C] + [C, D] + [D, A] = [C − A, D − B]`. -/
theorem varignon_area (a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (det a₁ a₂ b₁ b₂ + det b₁ b₂ c₁ c₂ + det c₁ c₂ d₁ d₂ + det d₁ d₂ a₁ a₂)
      (det (c₁ - a₁) (c₂ - a₂) (d₁ - b₁) (d₂ - b₂)) := by
  ipra_lc

/-- The diagonal area bound: `[e, f]² ≤ |e|² |f|²`. -/
theorem diagonal_area_bound (e₁ e₂ f₁ f₂ : ZT n) :
    Γ ⊢[PRAAx] zle (ZT.sq (det e₁ e₂ f₁ f₂)) (nsq e₁ e₂ * nsq f₁ f₂) := by
  ipra_zle (ZT.toZ Γ (dot e₁ e₂ f₁ f₂) ^ 2)

/-- `(−a + b + c + d)(a − b + c + d)(a + b − c + d)(a + b + c − d) = 4 (ab + cd)² − (a² + b² − c² − d²)²`. -/
theorem brahmagupta_factor (a b c d : ZT n) :
    Γ ⊢[PRAAx] ZT.eq ((b + c + d - a) * (a + c + d - b) * (a + b + d - c) * (a + b + c - d))
      (ZT.natLit 4 * ZT.sq (a * b + c * d) - ZT.sq (a * a + b * b - c * c - d * d)) := by
  ipra_lc

/-- Bretschneider's identity, cleared of the denominators `w`, `τ` of the two angle pairs. -/
theorem bretschneider {X Y E K x u w y v τ : ZT n}
    (h1 : Γ ⊢[PRAAx] ZT.eq (x * x + u * u) (w * w)) (h2 : Γ ⊢[PRAAx] ZT.eq (y * y + v * v) (τ * τ))
    (hE : Γ ⊢[PRAAx] ZT.eq (w * τ * E) (ZT.natLit 2 * X * x * τ - ZT.natLit 2 * Y * y * w))
    (hK : Γ ⊢[PRAAx] ZT.eq (w * τ * K) (X * u * τ + Y * v * w)) :
    Γ ⊢[PRAAx] ZT.eq
      (ZT.sq (w * τ) * (ZT.natLit 4 * ZT.sq (X + Y) - ZT.sq E - ZT.natLit 4 * ZT.sq K))
      (ZT.natLit 8 * X * Y * (w * τ * (w * τ + x * y - u * v))) := by
  ipra_lc (-(ZT.toZ Γ w * ZT.toZ Γ τ * ZT.toZ Γ E + (2 * ZT.toZ Γ X * ZT.toZ Γ x * ZT.toZ Γ τ - 2 * ZT.toZ Γ Y * ZT.toZ Γ y * ZT.toZ Γ w))) * ZT.toZ_eq hE +
    (-4 * (ZT.toZ Γ w * ZT.toZ Γ τ * ZT.toZ Γ K + (ZT.toZ Γ X * ZT.toZ Γ u * ZT.toZ Γ τ + ZT.toZ Γ Y * ZT.toZ Γ v * ZT.toZ Γ w))) * ZT.toZ_eq hK +
    (-4 * ZT.toZ Γ X ^ 2 * ZT.toZ Γ τ ^ 2) * ZT.toZ_eq h1 + (-4 * ZT.toZ Γ Y ^ 2 * ZT.toZ Γ w ^ 2) * ZT.toZ_eq h2

/-- The Bretschneider defect is nonnegative: `0 ≤ 2 w τ (w τ + x y − u v)`. -/
theorem bretschneider_defect {x u w y v τ : ZT n}
    (h1 : Γ ⊢[PRAAx] ZT.eq (x * x + u * u) (w * w)) (h2 : Γ ⊢[PRAAx] ZT.eq (y * y + v * v) (τ * τ)) :
    Γ ⊢[PRAAx] zle (ZT.natLit 0) (ZT.natLit 2 * (w * τ * (w * τ + x * y - u * v))) := by
  ipra_zle (ZT.toZ Γ (x * τ + y * w) ^ 2 + ZT.toZ Γ (u * τ - v * w) ^ 2) with (-ZT.toZ Γ τ ^ 2) * ZT.toZ_eq h1 +
    (-ZT.toZ Γ w ^ 2) * ZT.toZ_eq h2

end LeanProofs.IPRA.Geometry.QuadrilateralIdentities
