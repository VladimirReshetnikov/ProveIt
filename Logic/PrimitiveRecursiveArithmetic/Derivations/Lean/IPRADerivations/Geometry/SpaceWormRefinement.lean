import IPRADerivations.Core.OrderCertificates

/-!
# The algebra of the refined space-worm bounds

Packet: `geometry/space_worm_refinement_2026-11-19` (`sections/upper.tex`, `sections/lower.tex`).

* `prism_test` (upper bound, the turned prism): with `p = th` and `1 = h²(9 + t²)` written homogeneously,
  `(a p X + b h)² − d²(1 − 9p²y²) = h²(A t² + B t + D)` for `A = (aX)² + 9d²y² − d²`, `B = 2aXb`,
  `D = b² − 9d²`: squaring the vertex test reduces it to the sign of the quadratic `A t² + B t + D`;
* `cone_identity` (the added volume): `s² + s s'(H − z) = 1 − 9Hz` for `s² = 1 − 9z²`, `s s' = −9z`;
* `edge_tests` (lower bound, the excess areas): for `U = xY − hX` and `T = h(X − x) + (d − x)(Y − h)`,
  `U + T = d(Y − h)`, and `h(X − x + a(Y − h)) = T + (ah − (d − x))(Y − h)`;
* `ellipse_bound` (lower bound, the offsets): if the broken path through `C` with focal distances
  `r₁ = √(u² + h²)`, `r₂ = √(v² + h²)` (`d = u + v`, `2X − d = u − v`) has length `r₁ + r₂ ≤ ℓ`, then `C` lies
  in the ellipse of foci `O, B` and major axis `ℓ`: `(u − v)²(ℓ² − d²) + 4h²ℓ² ≤ ℓ²(ℓ² − d²)`, i.e. the
  paper's `X₀ ≤ (ℓ/2)√(1 − 4h²/(ℓ² − d²))`. The slack factors as `(ℓ² − σ²)(ℓ² − δ²)` with `σ = r₁ + r₂`,
  `δ = r₁ − r₂` (the two roots in `ℓ²` of the ellipse equation through `C`), which is
  `e(2σ + e)(2r₂ + e)(2r₁ + e)` for `ℓ = σ + e`, a product of natural numbers.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.SpaceWormRefinement

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The squared vertex test of the turned prism, homogeneous in `h`. -/
theorem prism_test (a b d X y t h : ZT n) :
    Γ ⊢[PRAAx] ZT.eq ((a * (t * h) * X + b * h) * (a * (t * h) * X + b * h) -
        d * d * (h * h * (ZT.natLit 9 + t * t) - ZT.natLit 9 * (t * h) * (t * h) * (y * y)))
      (h * h * (((a * X) * (a * X) + ZT.natLit 9 * (d * d) * (y * y) - d * d) * (t * t) +
        ZT.natLit 2 * (a * X) * b * t + (b * b - ZT.natLit 9 * (d * d)))) := by
  ipra_lc

/-- `s² + s s'(H − z) = 1 − 9Hz` for `s² = 1 − 9z²`, `s s' = −9z`. -/
theorem cone_identity (H z : ZT n) :
    Γ ⊢[PRAAx] ZT.eq ((ZT.natLit 1 - ZT.natLit 9 * (z * z)) + -(ZT.natLit 9 * z) * (H - z))
      (ZT.natLit 1 - ZT.natLit 9 * H * z) := by
  ipra_lc

/-- The two outside tests of the upper half and the oblique-width split. -/
theorem edge_tests (x h d X Y a : ZT n) :
    (Γ ⊢[PRAAx] ZT.eq ((x * Y - h * X) + (h * (X - x) + (d - x) * (Y - h))) (d * (Y - h))) ∧
    (Γ ⊢[PRAAx] ZT.eq (h * (X - x + a * (Y - h)))
      ((h * (X - x) + (d - x) * (Y - h)) + (a * h - (d - x)) * (Y - h))) := by
  refine ⟨ZT.derive ?_, ZT.derive ?_⟩ <;>
    (simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul]; ring)

/-- The ellipse of the broken path: `(u − v)²(ℓ² − d²) + 4h²ℓ² ≤ ℓ²(ℓ² − d²)` for `d = u + v`, cleared of
signs. -/
theorem ellipse_bound {u v h r₁ r₂ l : PTm n} (h₁ : Γ ⊢[PRAAx] r₁ * r₁ ≐ u * u + h * h)
    (h₂ : Γ ⊢[PRAAx] r₂ * r₂ ≐ v * v + h * h) (hl : Γ ⊢[PRAAx] le (r₁ + r₂) l) :
    Γ ⊢[PRAAx] le ((u * u + v * v) * (l * l) + num 2 * u * v * ((u + v) * (u + v)) +
        num 4 * (h * h) * (l * l) + l * l * ((u + v) * (u + v)))
      (l * l * (l * l) + num 2 * u * v * (l * l) + (u * u + v * v) * ((u + v) * (u + v))) := by
  have e₁ := natEq h₁
  have e₂ := natEq h₂
  ipra_le sl hl * (2 * (𝔟 r₁ + 𝔟 r₂) + sl hl) * (2 * 𝔟 r₂ + sl hl) * (2 * 𝔟 r₁ + sl hl) with
    (2 * (𝔟 l - 𝔟 r₁ - 𝔟 r₂) ^ 2 + 4 * (𝔟 l - 𝔟 r₁ - 𝔟 r₂) * 𝔟 r₁ + 4 * (𝔟 l - 𝔟 r₁ - 𝔟 r₂) * 𝔟 r₂ -
        3 * 𝔟 h ^ 2 + 𝔟 r₁ ^ 2 + 4 * 𝔟 r₁ * 𝔟 r₂ + 6 * 𝔟 r₂ ^ 2 - 𝔟 u ^ 2 - 2 * 𝔟 v ^ 2) * e₁ +
      (2 * (𝔟 l - 𝔟 r₁ - 𝔟 r₂) ^ 2 + 4 * (𝔟 l - 𝔟 r₁ - 𝔟 r₂) * 𝔟 r₁ + 4 * (𝔟 l - 𝔟 r₁ - 𝔟 r₂) * 𝔟 r₂ +
        3 * 𝔟 h ^ 2 + 4 * 𝔟 r₁ * 𝔟 r₂ + 𝔟 r₂ ^ 2 + 4 * 𝔟 u ^ 2 - 𝔟 v ^ 2) * e₂

end LeanProofs.IPRA.Geometry.SpaceWormRefinement
