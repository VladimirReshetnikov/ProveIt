import IPRADerivations.Geometry.TriangleCentres

/-!
# Intersection tests for lines and circles, and inversion of generalized circles

Packet: `geometry/euclidean_geometry_ipra_2026-11-22`, `chapters/circles.tex`, Theorems
`circ:line-intersection`, `circ:circle-intersection` and `circ:inversion-circle`. Points have two integer-term
coordinates, with `dot`, `det`, `nsq` of `Geometry/TriangleCentres`. As iPRA derivations:

* `line_circle_square`: (C1) "`a (|P + t v − O|² − ρ) = (a t + b)² − D`" for `a = |v|²`, `b = (P − O) · v`,
  `c = |P − O|² − ρ`, `D = b² − a c` (with `w = P − O`);
* `line_misses_circle`: "If `D < 0`, there is no intersection": a point of the line on the circle together with
  `D + 1 ≤ 0` is contradictory ("A square cannot equal a negative element");
* `line_foot`: for the foot `H = P − (b/a) v`, `|a (H − O)|² = a² |P − O|² − a b²`, so
  "`D = a (ρ − |H − O|²)`" after clearing `a`;
* `two_circle_axis`, `two_circle_first`, `two_circle_second`: (C9) with `d = O₂ − O₁`, `s = |d|²` and a term `τ`
  with `τ² = E = 4 s ρ₁ − (s + ρ₁ − ρ₂)²` (the root `√E`): the point `2 s (y − O₁) = (s + ρ₁ − ρ₂) d + τ J d`
  is on the radical axis and on both circles;
* `two_circle_square`: every common point `y` has `E = (2 [d, y − O₁])²`, so `E ≥ 0`: "The circles have no
  common point if `E < 0`";
* `two_circle_factor`: "`E = ((r₁ + r₂)² − δ²)(δ² − (r₁ − r₂)²)`";
* `inversion_circle`: (C16) for `N x = k y` with `N = |y|²`:
  `N² (λ |x|² + 2 a · x + b) = N (b N + 2 k a · y + λ k²)`.

Not derived: the exhaustion of the solutions (no zero divisors), and the case of equal centres.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.CircleIntersections

open_ipra
open LeanProofs.IPRA.Geometry.TriangleCentres (dot det nsq)

variable {n : ℕ} {Γ : List (Fm PTm n)}

attribute [local ipra_defs] dot det nsq

/-! ## A line and a circle -/

/-- (C1): `a (|w + t v|² − ρ) = (a t + b)² − (b² − a (|w|² − ρ))`. -/
theorem line_circle_square (w₁ w₂ v₁ v₂ t ρ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (nsq v₁ v₂ * (nsq (w₁ + t * v₁) (w₂ + t * v₂) - ρ))
      (ZT.sq (nsq v₁ v₂ * t + dot w₁ w₂ v₁ v₂) -
        (ZT.sq (dot w₁ w₂ v₁ v₂) - nsq v₁ v₂ * (nsq w₁ w₂ - ρ))) := by
  ipra_lc

/-- A negative discriminant: a point of the line on the circle is contradictory. -/
theorem line_misses_circle {w₁ w₂ v₁ v₂ t ρ : ZT n}
    (hon : Γ ⊢[PRAAx] ZT.eq (nsq (w₁ + t * v₁) (w₂ + t * v₂)) ρ)
    (hD : Γ ⊢[PRAAx] zle (ZT.sq (dot w₁ w₂ v₁ v₂) - nsq v₁ v₂ * (nsq w₁ w₂ - ρ) + ZT.natLit 1)
      (ZT.natLit 0)) (φ : Fm PTm n) : Γ ⊢[PRAAx] φ := by
  ipra_absurd (ZT.toZ Γ (nsq v₁ v₂ * t + dot w₁ w₂ v₁ v₂) ^ 2 + zsl hD) with
    (-1 : Groth (Q Γ)) * ZT.toZ_eq (line_circle_square (Γ := Γ) w₁ w₂ v₁ v₂ t ρ) +
    (ZT.toZ Γ v₁ * ZT.toZ Γ v₁ + ZT.toZ Γ v₂ * ZT.toZ Γ v₂) * ZT.toZ_eq hon

/-- The foot of the centre on the line: `|a w − b v|² = a² |w|² − a b²`. -/
theorem line_foot (w₁ w₂ v₁ v₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (nsq (nsq v₁ v₂ * w₁ - dot w₁ w₂ v₁ v₂ * v₁) (nsq v₁ v₂ * w₂ - dot w₁ w₂ v₁ v₂ * v₂))
      (nsq v₁ v₂ * nsq v₁ v₂ * nsq w₁ w₂ - nsq v₁ v₂ * (dot w₁ w₂ v₁ v₂ * dot w₁ w₂ v₁ v₂)) := by
  ipra_lc

/-! ## Two circles -/

/-- The point of (C9) is on the radical axis. -/
theorem two_circle_axis (d₁ d₂ ρ₁ ρ₂ τ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (dot ((nsq d₁ d₂ + ρ₁ - ρ₂) * d₁ - τ * d₂) ((nsq d₁ d₂ + ρ₁ - ρ₂) * d₂ + τ * d₁) d₁ d₂)
      ((nsq d₁ d₂ + ρ₁ - ρ₂) * nsq d₁ d₂) := by
  ipra_lc

/-- The point of (C9) is on the first circle. -/
theorem two_circle_first {d₁ d₂ ρ₁ ρ₂ τ : ZT n}
    (hτ : Γ ⊢[PRAAx] ZT.eq (τ * τ)
      (ZT.natLit 4 * nsq d₁ d₂ * ρ₁ - ZT.sq (nsq d₁ d₂ + ρ₁ - ρ₂))) :
    Γ ⊢[PRAAx] ZT.eq
      (nsq ((nsq d₁ d₂ + ρ₁ - ρ₂) * d₁ - τ * d₂) ((nsq d₁ d₂ + ρ₁ - ρ₂) * d₂ + τ * d₁))
      (ZT.natLit 4 * nsq d₁ d₂ * nsq d₁ d₂ * ρ₁) := by
  ipra_lc (ZT.toZ Γ d₁ * ZT.toZ Γ d₁ + ZT.toZ Γ d₂ * ZT.toZ Γ d₂) * ZT.toZ_eq hτ

/-- The point of (C9) is on the second circle. -/
theorem two_circle_second {d₁ d₂ ρ₁ ρ₂ τ : ZT n}
    (hτ : Γ ⊢[PRAAx] ZT.eq (τ * τ)
      (ZT.natLit 4 * nsq d₁ d₂ * ρ₁ - ZT.sq (nsq d₁ d₂ + ρ₁ - ρ₂))) :
    Γ ⊢[PRAAx] ZT.eq
      (nsq ((nsq d₁ d₂ + ρ₁ - ρ₂) * d₁ - τ * d₂ - ZT.natLit 2 * nsq d₁ d₂ * d₁)
        ((nsq d₁ d₂ + ρ₁ - ρ₂) * d₂ + τ * d₁ - ZT.natLit 2 * nsq d₁ d₂ * d₂))
      (ZT.natLit 4 * nsq d₁ d₂ * nsq d₁ d₂ * ρ₂) := by
  ipra_lc (ZT.toZ Γ d₁ * ZT.toZ Γ d₁ + ZT.toZ Γ d₂ * ZT.toZ Γ d₂) * ZT.toZ_eq hτ

/-- A common point `y` of the two circles (`w = y − O₁`): `E = (2 [d, w])²`. -/
theorem two_circle_square {d₁ d₂ w₁ w₂ ρ₁ ρ₂ : ZT n}
    (h1 : Γ ⊢[PRAAx] ZT.eq (nsq w₁ w₂) ρ₁) (h2 : Γ ⊢[PRAAx] ZT.eq (nsq (w₁ - d₁) (w₂ - d₂)) ρ₂) :
    Γ ⊢[PRAAx] ZT.eq
      (ZT.natLit 4 * nsq d₁ d₂ * ρ₁ - ZT.sq (nsq d₁ d₂ + ρ₁ - ρ₂))
      (ZT.sq (ZT.natLit 2 * det d₁ d₂ w₁ w₂)) := by
  ipra_lc (-4 * (ZT.toZ Γ d₁ * ZT.toZ Γ d₁ + ZT.toZ Γ d₂ * ZT.toZ Γ d₂) + (2 * (ZT.toZ Γ w₁ * ZT.toZ Γ d₁ + ZT.toZ Γ w₂ * ZT.toZ Γ d₂) + (ZT.toZ Γ d₁ * ZT.toZ Γ d₁ + ZT.toZ Γ d₂ * ZT.toZ Γ d₂) + ZT.toZ Γ ρ₁ - ZT.toZ Γ ρ₂)) * ZT.toZ_eq h1 -
    (2 * (ZT.toZ Γ w₁ * ZT.toZ Γ d₁ + ZT.toZ Γ w₂ * ZT.toZ Γ d₂) + (ZT.toZ Γ d₁ * ZT.toZ Γ d₁ + ZT.toZ Γ d₂ * ZT.toZ Γ d₂) + ZT.toZ Γ ρ₁ - ZT.toZ Γ ρ₂) * ZT.toZ_eq h2

/-- `4 δ² r₁² − (δ² + r₁² − r₂²)² = ((r₁ + r₂)² − δ²)(δ² − (r₁ − r₂)²)`. -/
theorem two_circle_factor (r₁ r₂ δ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (ZT.natLit 4 * (δ * δ) * (r₁ * r₁) - ZT.sq (δ * δ + r₁ * r₁ - r₂ * r₂))
      ((ZT.sq (r₁ + r₂) - δ * δ) * (δ * δ - ZT.sq (r₁ - r₂))) := by
  ipra_lc

/-! ## Inversion -/

/-- (C16): for `N x = k y`, `N = |y|²`: `N² (λ |x|² + 2 a · x + b) = N (b N + 2 k a · y + λ k²)`. -/
theorem inversion_circle {x₁ x₂ y₁ y₂ a₁ a₂ k lam b : ZT n}
    (hx1 : Γ ⊢[PRAAx] ZT.eq (nsq y₁ y₂ * x₁) (k * y₁))
    (hx2 : Γ ⊢[PRAAx] ZT.eq (nsq y₁ y₂ * x₂) (k * y₂)) :
    Γ ⊢[PRAAx] ZT.eq
      (nsq y₁ y₂ * nsq y₁ y₂ * (lam * nsq x₁ x₂ + ZT.natLit 2 * dot a₁ a₂ x₁ x₂ + b))
      (nsq y₁ y₂ * (b * nsq y₁ y₂ + ZT.natLit 2 * k * dot a₁ a₂ y₁ y₂ + lam * (k * k))) := by
  ipra_lc (ZT.toZ Γ lam * ((ZT.toZ Γ y₁ * ZT.toZ Γ y₁ + ZT.toZ Γ y₂ * ZT.toZ Γ y₂) * ZT.toZ Γ x₁ + ZT.toZ Γ k * ZT.toZ Γ y₁) + 2 * (ZT.toZ Γ y₁ * ZT.toZ Γ y₁ + ZT.toZ Γ y₂ * ZT.toZ Γ y₂) * ZT.toZ Γ a₁) * ZT.toZ_eq hx1 +
    (ZT.toZ Γ lam * ((ZT.toZ Γ y₁ * ZT.toZ Γ y₁ + ZT.toZ Γ y₂ * ZT.toZ Γ y₂) * ZT.toZ Γ x₂ + ZT.toZ Γ k * ZT.toZ Γ y₂) + 2 * (ZT.toZ Γ y₁ * ZT.toZ Γ y₁ + ZT.toZ Γ y₂ * ZT.toZ Γ y₂) * ZT.toZ Γ a₂) * ZT.toZ_eq hx2

end LeanProofs.IPRA.Geometry.CircleIntersections
