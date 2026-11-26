import IPRADerivations.Geometry.CuboidAlgebra

/-!
# The boundary-balancing regime of the cuboid diameter

Packet: `geometry/cuboid_surface_geodesics_2026-11-19`, Theorem `thm:diam-summary`, Case II ("Boundary-balancing
regime"): with `H = √((B+C)² − 2A(C−B) − A²)`, `τ = (B + C − H)/2`, the pair `P = (A/2, τ, 0)`,
`Q_0 = (A/2, B − τ, C)` has `D² = B² + 3C² + 2B(A + C) − 2CH` (`eq:boundary-D`). The fixed-vertex gap
`eq:fixed-gap`, `R² − L_0² = A(C − B)K/(2C²)`, is `CuboidAlgebra.vertex_factor`.

For the point `P` (`x = A/2`, `y = τ`), the two competing unfolding lengths of `lem:five`,
`d_1² = (A + C)² + (B − 2y)²` and `d_3² = (C + x + y)² + (A + B − x − y)²`, both equal `D²` once `H` satisfies its
defining relation `H² = (B + C)² − 2A(C − B) − A²`; this is the balancing. Cleared by `4` (`2τ = B + C − H`,
`2x = A`), over integer terms:

* `boundary_d1`: `4(A + C)² + 4(B − (B + C − H))² = 4D²`;
* `boundary_d3`: `(2C + A + (B + C − H))² + (2A + 2B − A − (B + C − H))² = 4D²`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.CuboidGeodesicAlgebra

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `4D² = 4(B² + 3C² + 2B(A + C) − 2CH)`. -/
abbrev D4 (A B C H : ZT n) : ZT n :=
  ZT.natLit 4 * (B * B + ZT.natLit 3 * (C * C) + ZT.natLit 2 * B * (A + C) - ZT.natLit 2 * C * H)

/-- `eq:boundary-D` through `d_1`. -/
theorem boundary_d1 {A B C H : ZT n}
    (hH : Γ ⊢[PRAAx] ZT.eq (H * H) ((B + C) * (B + C) - ZT.natLit 2 * A * (C - B) - A * A)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit 4 * ((A + C) * (A + C)) + ZT.natLit 4 * ((B - (B + C - H)) * (B - (B + C - H))))
      (D4 A B C H) := by
  have e := ZT.toZ_eq hH
  refine ZT.derive ?_
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit] at e ⊢
  push_cast at e ⊢
  linear_combination 4 * e

/-- The balancing `d_3 = D` at `P = (A/2, τ, 0)`. -/
theorem boundary_d3 {A B C H : ZT n}
    (hH : Γ ⊢[PRAAx] ZT.eq (H * H) ((B + C) * (B + C) - ZT.natLit 2 * A * (C - B) - A * A)) :
    Γ ⊢[PRAAx] ZT.eq ((ZT.natLit 2 * C + A + (B + C - H)) * (ZT.natLit 2 * C + A + (B + C - H)) +
        (ZT.natLit 2 * A + ZT.natLit 2 * B - A - (B + C - H)) * (ZT.natLit 2 * A + ZT.natLit 2 * B - A - (B + C - H)))
      (D4 A B C H) := by
  have e := ZT.toZ_eq hH
  refine ZT.derive ?_
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit] at e ⊢
  push_cast at e ⊢
  linear_combination 2 * e

end LeanProofs.IPRA.Geometry.CuboidGeodesicAlgebra
