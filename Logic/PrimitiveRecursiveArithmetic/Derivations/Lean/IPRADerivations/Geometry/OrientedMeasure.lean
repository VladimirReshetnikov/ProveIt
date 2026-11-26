import IPRADerivations.Geometry.EuclideanSpace

/-!
# Oriented area and volume: the boundary identities of a dissection

Packet: `geometry/euclidean_geometry_ipra_2026-11-22`, `chapters/polygons.tex`, Theorem `poly:shoelace`, and
`chapters/solids.tex`, Theorems `sol:volume` and `sol:prism`. Points have integer-term coordinates; `det` is the
planar determinant of `Geometry/TriangleCentres` and `trip` the triple product of `Geometry/EuclideanSpace`. The
identities on which the dissection arguments rest, as iPRA derivations:

* `triangle_shoelace`: "The doubled oriented area of a triangle `ABC` is
  `[B − A, C − A] = [A, B] + [B, C] + [C, A]`";
* `edge_cancel`: "Every internal edge contributes `[X, Y] + [Y, X] = 0`";
* `edge_subdivide`: "Inserting `Q = (1 − t) P_i + t P_{i+1}` replaces `[P_i, P_{i+1}]` by
  `[P_i, Q] + [Q, P_{i+1}]`, the same value", with `t = τ/m` cleared:
  `[P, (m − τ) P + τ R] + [(m − τ) P + τ R, R] = m [P, R]`;
* `edge_translate`: "Adding a common translation `a` changes each summand by `[a, P_{i+1}] − [a, P_i]`" (which
  telescopes around a closed boundary; `Geometry/PathShoelace` has the coded sum);
* `four_face`: "Multilinearity gives the four-face identity
  `[B − A, C − A, D − A] = [B, C, D] − [A, C, D] + [A, B, D] − [A, B, C]`";
* `prism_tetra_1`, `prism_tetra_2`, `prism_tetra_3`: the three tetrahedra `{A, B, C, C + u}`,
  `{A, B, B + u, C + u}`, `{A, A + u, B + u, C + u}` of the triangular prism: "Each has absolute determinant
  `|[B − A, C − A, u]|`", with signs `+`, `−`, `+` in this vertex order.

Not derived: the summation over a coded dissection, the disjointness of the three tetrahedra, and the volume
formulas with square roots (base area times height).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.OrientedMeasure

open_ipra
open LeanProofs.IPRA.Geometry.TriangleCentres (det)
open LeanProofs.IPRA.Geometry.EuclideanSpace (cx trip)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local macro "geo" : tactic =>
  `(tactic| (apply ZT.derive; simp only [det, cx, trip, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg,
    ZT.toZ_sq, ZT.toZ_natLit, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]; ring))

/-! ## Area -/

/-- `[B − A, C − A] = [A, B] + [B, C] + [C, A]`. -/
theorem triangle_shoelace (a₁ a₂ b₁ b₂ c₁ c₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (det (b₁ - a₁) (b₂ - a₂) (c₁ - a₁) (c₂ - a₂))
      (det a₁ a₂ b₁ b₂ + det b₁ b₂ c₁ c₂ + det c₁ c₂ a₁ a₂) := by
  geo

/-- An edge traversed in both directions cancels: `[X, Y] + [Y, X] = 0`. -/
theorem edge_cancel (x₁ x₂ y₁ y₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (det x₁ x₂ y₁ y₂ + det y₁ y₂ x₁ x₂) (ZT.natLit 0) := by
  geo

/-- Subdividing an edge: `[P, (m − τ) P + τ R] + [(m − τ) P + τ R, R] = m [P, R]`. -/
theorem edge_subdivide (p₁ p₂ r₁ r₂ m τ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (det p₁ p₂ ((m - τ) * p₁ + τ * r₁) ((m - τ) * p₂ + τ * r₂) +
        det ((m - τ) * p₁ + τ * r₁) ((m - τ) * p₂ + τ * r₂) r₁ r₂)
      (m * det p₁ p₂ r₁ r₂) := by
  geo

/-- Translating an edge: `[P + a, Q + a] = [P, Q] + [a, Q] − [a, P]`. -/
theorem edge_translate (p₁ p₂ q₁ q₂ a₁ a₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (det (p₁ + a₁) (p₂ + a₂) (q₁ + a₁) (q₂ + a₂))
      (det p₁ p₂ q₁ q₂ + det a₁ a₂ q₁ q₂ - det a₁ a₂ p₁ p₂) := by
  geo

/-! ## Volume -/

/-- The four-face identity `[B − A, C − A, D − A] = [B, C, D] − [A, C, D] + [A, B, D] − [A, B, C]`. -/
theorem four_face (a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ d₁ d₂ d₃ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (trip (b₁ - a₁) (b₂ - a₂) (b₃ - a₃) (c₁ - a₁) (c₂ - a₂) (c₃ - a₃) (d₁ - a₁) (d₂ - a₂) (d₃ - a₃))
      (trip b₁ b₂ b₃ c₁ c₂ c₃ d₁ d₂ d₃ - trip a₁ a₂ a₃ c₁ c₂ c₃ d₁ d₂ d₃ +
        trip a₁ a₂ a₃ b₁ b₂ b₃ d₁ d₂ d₃ - trip a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃) := by
  geo

/-- The tetrahedron `{A, B, C, C + u}` of the prism, with `b = B − A`, `c = C − A`: `[b, c, c + u] = [b, c, u]`. -/
theorem prism_tetra_1 (b₁ b₂ b₃ c₁ c₂ c₃ u₁ u₂ u₃ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (trip b₁ b₂ b₃ c₁ c₂ c₃ (c₁ + u₁) (c₂ + u₂) (c₃ + u₃))
      (trip b₁ b₂ b₃ c₁ c₂ c₃ u₁ u₂ u₃) := by
  geo

/-- The tetrahedron `{A, B, B + u, C + u}`: `[b, b + u, c + u] = −[b, c, u]`. -/
theorem prism_tetra_2 (b₁ b₂ b₃ c₁ c₂ c₃ u₁ u₂ u₃ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (trip b₁ b₂ b₃ (b₁ + u₁) (b₂ + u₂) (b₃ + u₃) (c₁ + u₁) (c₂ + u₂) (c₃ + u₃))
      (-trip b₁ b₂ b₃ c₁ c₂ c₃ u₁ u₂ u₃) := by
  geo

/-- The tetrahedron `{A, A + u, B + u, C + u}`: `[u, b + u, c + u] = [b, c, u]`. -/
theorem prism_tetra_3 (b₁ b₂ b₃ c₁ c₂ c₃ u₁ u₂ u₃ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (trip u₁ u₂ u₃ (b₁ + u₁) (b₂ + u₂) (b₃ + u₃) (c₁ + u₁) (c₂ + u₂) (c₃ + u₃))
      (trip b₁ b₂ b₃ c₁ c₂ c₃ u₁ u₂ u₃) := by
  geo

end LeanProofs.IPRA.Geometry.OrientedMeasure
