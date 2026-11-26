import IPRADerivations.Core.CertificateTactics

/-!
# Coordinates of the regular solids: edges, radii and supporting planes

Packet: `geometry/euclidean_geometry_ipra_2026-11-22`, `chapters/solids.tex`, Theorem `sol:realizations`
("Exact realizations of all five types"). Points have three integer-term coordinates; `dt` is the dot product
and `nm` the squared norm. The golden ratio is a free term `φ`, and `φ⁻¹` is written `φ − 1`; the relation
`φ² = φ + 1` has no integer solution, so it is not assumed: it appears as the explicit term `φ² − φ − 1`. As
iPRA derivations:

* `tetrahedron_edge`, `cube_edge`, `octahedron_edge`, `cube_radius`, `octahedron_radius`: "The tetrahedron has
  four equilateral faces of squared edge length 8; the cube has six squares of squared edge length 4; the
  octahedron has eight equilateral triangles of squared edge length 2. Their vertex squared radii are
  `3, 3, 1`";
* `icosahedron_radius`: "all vertex squared radii are `φ + 2`"; `icosahedron_edge₁`, `icosahedron_edge₂`,
  `icosahedron_edge₃`, `icosahedron_edge₄`: "All three pairwise distances in either triple are 2", for the
  triples `(0, 1, φ), (1, φ, 0), (φ, 0, 1)` and `(0, 1, φ), (1, φ, 0), (−1, φ, 0)`;
* `icosahedron_support₁`, `icosahedron_support₂`, `icosahedron_support₃`, `icosahedron_support₄`: the normals
  `(1, 1, 1)` and `(0, φ, φ⁻¹)` have "supporting value `φ²`" at the vertices of their triples;
* `dodecahedron_support₁`, `dodecahedron_support₂`, `dodecahedron_support₃`: the normal `(0, φ, 1)` has value
  `φ²` at `(1, 1, 1)`, `(φ⁻¹, φ, 0)` and `(0, φ⁻¹, φ)`; `dodecahedron_edge`, `dodecahedron_diagonal`: the
  side `(1, 1, 1), (φ⁻¹, φ, 0)` of that pentagon has squared length `8 − 4φ` and the diagonal
  `(1, 1, 1), (−φ⁻¹, φ, 0)` has squared length `4`.

Not derived: the inequalities placing the other vertices strictly inside each supporting plane (for the
dodecahedron these are in `Geometry/Dodecahedron`, over `ℤ[φ]`), and the combinatorial incidences.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.RegularSolidCoordinates

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The dot product in space. -/
def dt (a₁ a₂ a₃ b₁ b₂ b₃ : ZT n) : ZT n := a₁ * b₁ + a₂ * b₂ + a₃ * b₃

/-- The squared norm in space. -/
def nm (a₁ a₂ a₃ : ZT n) : ZT n := a₁ * a₁ + a₂ * a₂ + a₃ * a₃

/-- The defect `φ² − φ − 1` of the golden relation. -/
def gold (φ : ZT n) : ZT n := φ * φ - φ - ZT.natLit 1

attribute [local ipra_defs] dt nm gold

local notation "𝟎" => (ZT.natLit 0 : ZT n)
local notation "𝟏" => (ZT.natLit 1 : ZT n)

/-! ## Tetrahedron, cube and octahedron -/

/-- The tetrahedron edge `(1, 1, 1), (1, −1, −1)` has squared length `8`. -/
theorem tetrahedron_edge :
    Γ ⊢[PRAAx] ZT.eq (nm (𝟏 - 𝟏) (𝟏 - (-𝟏)) (𝟏 - (-𝟏))) (ZT.natLit 8) := by
  ipra_lc

/-- The cube edge `(1, 1, 1), (1, 1, −1)` has squared length `4`. -/
theorem cube_edge :
    Γ ⊢[PRAAx] ZT.eq (nm (𝟏 - 𝟏) (𝟏 - 𝟏) (𝟏 - (-𝟏))) (ZT.natLit 4) := by
  ipra_lc

/-- The octahedron edge `(1, 0, 0), (0, 1, 0)` has squared length `2`. -/
theorem octahedron_edge :
    Γ ⊢[PRAAx] ZT.eq (nm (𝟏 - 𝟎) (𝟎 - 𝟏) (𝟎 - 𝟎)) (ZT.natLit 2) := by
  ipra_lc

/-- The vertices `(±1, ±1, ±1)` of the cube and of the tetrahedron have squared radius `3`. -/
theorem cube_radius :
    Γ ⊢[PRAAx] ZT.eq (nm 𝟏 𝟏 (-𝟏)) (ZT.natLit 3) := by
  ipra_lc

/-- The vertices of the octahedron have squared radius `1`. -/
theorem octahedron_radius :
    Γ ⊢[PRAAx] ZT.eq (nm 𝟎 (-𝟏) 𝟎) (ZT.natLit 1) := by
  ipra_lc

/-! ## The icosahedron -/

/-- `|(0, 1, φ)|² = φ + 2` on the golden relation. -/
theorem icosahedron_radius (φ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (nm 𝟎 𝟏 φ) (φ + ZT.natLit 2 + gold φ) := by
  ipra_lc

/-- `|(0, 1, φ) − (1, φ, 0)|² = 4` on the golden relation. -/
theorem icosahedron_edge₁ (φ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (nm (𝟎 - 𝟏) (𝟏 - φ) (φ - 𝟎)) (ZT.natLit 4 + ZT.natLit 2 * gold φ) := by
  ipra_lc

/-- `|(0, 1, φ) − (φ, 0, 1)|² = 4` on the golden relation. -/
theorem icosahedron_edge₂ (φ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (nm (𝟎 - φ) (𝟏 - 𝟎) (φ - 𝟏)) (ZT.natLit 4 + ZT.natLit 2 * gold φ) := by
  ipra_lc

/-- `|(1, φ, 0) − (φ, 0, 1)|² = 4` on the golden relation. -/
theorem icosahedron_edge₃ (φ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (nm (𝟏 - φ) (φ - 𝟎) (𝟎 - 𝟏)) (ZT.natLit 4 + ZT.natLit 2 * gold φ) := by
  ipra_lc

/-- `|(1, φ, 0) − (−1, φ, 0)|² = 4`. -/
theorem icosahedron_edge₄ (φ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (nm (𝟏 - (-𝟏)) (φ - φ) (𝟎 - 𝟎)) (ZT.natLit 4) := by
  ipra_lc

/-- The normal `(1, 1, 1)` at `(0, 1, φ)`: `φ²` on the golden relation. -/
theorem icosahedron_support₁ (φ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (dt 𝟏 𝟏 𝟏 𝟎 𝟏 φ) (φ * φ - gold φ) := by
  ipra_lc

/-- The normal `(0, φ, φ⁻¹)` at `(0, 1, φ)`: exactly `φ²`. -/
theorem icosahedron_support₂ (φ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (dt 𝟎 φ (φ - 𝟏) 𝟎 𝟏 φ) (φ * φ) := by
  ipra_lc

/-- The normal `(0, φ, φ⁻¹)` at `(1, φ, 0)`: exactly `φ²`. -/
theorem icosahedron_support₃ (φ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (dt 𝟎 φ (φ - 𝟏) 𝟏 φ 𝟎) (φ * φ) := by
  ipra_lc

/-- The normal `(0, φ, φ⁻¹)` at `(−1, φ, 0)`: exactly `φ²`. -/
theorem icosahedron_support₄ (φ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (dt 𝟎 φ (φ - 𝟏) (-𝟏) φ 𝟎) (φ * φ) := by
  ipra_lc

/-! ## A face of the dodecahedron -/

/-- The normal `(0, φ, 1)` at `(1, 1, 1)`: `φ²` on the golden relation. -/
theorem dodecahedron_support₁ (φ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (dt 𝟎 φ 𝟏 𝟏 𝟏 𝟏) (φ * φ - gold φ) := by
  ipra_lc

/-- The normal `(0, φ, 1)` at `(φ⁻¹, φ, 0)`: exactly `φ²`. -/
theorem dodecahedron_support₂ (φ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (dt 𝟎 φ 𝟏 (φ - 𝟏) φ 𝟎) (φ * φ) := by
  ipra_lc

/-- The normal `(0, φ, 1)` at `(0, φ⁻¹, φ)`: exactly `φ²`. -/
theorem dodecahedron_support₃ (φ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (dt 𝟎 φ 𝟏 𝟎 (φ - 𝟏) φ) (φ * φ) := by
  ipra_lc

/-- The side `(1, 1, 1), (φ⁻¹, φ, 0)`: squared length `8 − 4φ` on the golden relation. -/
theorem dodecahedron_edge (φ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (nm (𝟏 - (φ - 𝟏)) (𝟏 - φ) (𝟏 - 𝟎))
      (ZT.natLit 8 - ZT.natLit 4 * φ + ZT.natLit 2 * gold φ) := by
  ipra_lc

/-- The diagonal `(1, 1, 1), (−φ⁻¹, φ, 0)`: squared length `4` on the golden relation. -/
theorem dodecahedron_diagonal (φ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (nm (𝟏 - (-(φ - 𝟏))) (𝟏 - φ) (𝟏 - 𝟎)) (ZT.natLit 4 + ZT.natLit 2 * gold φ) := by
  ipra_lc

end LeanProofs.IPRA.Geometry.RegularSolidCoordinates
