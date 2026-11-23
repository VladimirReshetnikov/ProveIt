import IPRADerivations.Geometry.TriangleCentres
import IPRADerivations.Combinatorics.FisherInequality

/-!
# Convexity of the disc, the power of a point, common points and the rational parametrization

Packet: `geometry/euclidean_geometry_ipra_2026-11-22`, `chapters/circles.tex`, Theorems `circ:convexity`,
`circ:power`, Corollary `circ:three-common` and Theorem `circ:parameter`. Points have two integer-term
coordinates, vectors are taken from the centre, and `ρ` is the squared radius. As iPRA derivations:

* `chord_convex`, `chord_inside`: (C4) with integer weights `r, s` in place of `1 − t, t`:
  `|r a + s b|² = (r + s)² ρ − r s |b − a|²`, hence `≤ (r + s)² ρ` for `r, s ≥ 0`;
* `tangent_gap`, `tangent_side`: "`|X − A|² = 2ρ − 2 (X − O) · (A − O)`", hence `(X − O) · (A − O) ≤ ρ`: the
  circle lies in the closed half-plane of its tangent;
* `power_product`, `power_sum`: for two points `P + t v`, `P + u v` of the circle,
  `(t − u)(|v|² t u − Pow(P)) = 0` and `(t − u)(|v|² (t + u) + 2 (P − O) · v) = 0`, the two Vieta relations of
  (C5) before the cancellation of `t − u`;
* `tangent_power`: (C6) "`|P − O|² = |P − T|² + ρ`" for a tangent at `T`;
* `three_common₁`, `three_common₂`: three common points `x, y, z` of two circles have
  `2 [y − x, z − x] (O′ − O) = 0`: if they are not collinear, the centres agree;
* `parameter_on_circle`: (C14) with `t = m / k`: `|(k² − m²) a + 2 m k J a|² = (k² + m²)² |a|²`;
* `parameter_inverse₁`, `parameter_inverse₂`: the inverse, with `k = ρ + a · x` and `m = [a, x]` (`pk`, `pm`):
  `(k² − m²) a + 2 m k J a = (k² + m²) x` for every point `x` of the circle.

Not derived: the cancellations of nonzero factors, and the uniqueness of the parameter.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.CirclePower

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Geometry.TriangleCentres (dot det nsq)
open LeanProofs.IPRA.Combinatorics.FisherInequality (znn_of_pos_mul)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The parameter denominator `k = ρ + a · x`. -/
def pk (a₁ a₂ x₁ x₂ ρ : ZT n) : ZT n := ρ + dot a₁ a₂ x₁ x₂

/-- The parameter numerator `m = [a, x]`. -/
def pm (a₁ a₂ x₁ x₂ : ZT n) : ZT n := det a₁ a₂ x₁ x₂

local notation:max "ζ" t:max => ZT.toZ Γ t

local macro "gsimp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [pk, pm, dot, det, nsq, zsl_def, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg,
    ZT.toZ_sq, ZT.toZ_natLit, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] $[$loc]?)

local macro "geo" : tactic => `(tactic| (apply ZT.derive; gsimp; ring))

/-! ## Convexity -/

/-- (C4): `|r a + s b|² = (r + s)² ρ − r s |b − a|²`. -/
theorem chord_convex {a₁ a₂ b₁ b₂ ρ : ZT n} (r s : ZT n)
    (ha : Γ ⊢[PRAAx] ZT.eq (nsq a₁ a₂) ρ) (hb : Γ ⊢[PRAAx] ZT.eq (nsq b₁ b₂) ρ) :
    Γ ⊢[PRAAx] ZT.eq (nsq (r * a₁ + s * b₁) (r * a₂ + s * b₂))
      (ZT.sq (r + s) * ρ - r * s * nsq (b₁ - a₁) (b₂ - a₂)) := by
  have ea := ZT.toZ_eq ha
  have eb := ZT.toZ_eq hb
  apply ZT.derive
  gsimp at ea eb ⊢
  linear_combination (ζ r * ζ r + ζ r * ζ s) * ea + (ζ s * ζ s + ζ r * ζ s) * eb

/-- A point of a chord is inside the closed disc. -/
theorem chord_inside {a₁ a₂ b₁ b₂ ρ r s : ZT n}
    (hr : Γ ⊢[PRAAx] zle (ZT.natLit 0) r) (hs : Γ ⊢[PRAAx] zle (ZT.natLit 0) s)
    (ha : Γ ⊢[PRAAx] ZT.eq (nsq a₁ a₂) ρ) (hb : Γ ⊢[PRAAx] ZT.eq (nsq b₁ b₂) ρ) :
    Γ ⊢[PRAAx] zle (nsq (r * a₁ + s * b₁) (r * a₂ + s * b₂)) (ZT.sq (r + s) * ρ) := by
  have c := ZT.toZ_eq (chord_convex r s ha hb)
  refine zle_of_comb (zsl hr * zsl hs * (ZT.toZ Γ (b₁ - a₁) ^ 2 + ZT.toZ Γ (b₂ - a₂) ^ 2)) ?_
    (nn_mul (nn_mul (nn_zsl _) (nn_zsl _)) (nn_add (nn_zsq _) (nn_zsq _)))
  gsimp at c ⊢
  linear_combination (-1 : Groth (Q Γ)) * c

/-- `|X − A|² = 2ρ − 2 (X − O) · (A − O)`. -/
theorem tangent_gap {x₁ x₂ a₁ a₂ ρ : ZT n}
    (hx : Γ ⊢[PRAAx] ZT.eq (nsq x₁ x₂) ρ) (ha : Γ ⊢[PRAAx] ZT.eq (nsq a₁ a₂) ρ) :
    Γ ⊢[PRAAx] ZT.eq (nsq (x₁ - a₁) (x₂ - a₂)) (ZT.natLit 2 * (ρ - dot x₁ x₂ a₁ a₂)) := by
  have ex := ZT.toZ_eq hx
  have ea := ZT.toZ_eq ha
  apply ZT.derive
  gsimp at ex ea ⊢
  linear_combination ex + ea

/-- The circle lies on one side of its tangent: `(X − O) · (A − O) ≤ ρ`. -/
theorem tangent_side {x₁ x₂ a₁ a₂ ρ : ZT n}
    (hx : Γ ⊢[PRAAx] ZT.eq (nsq x₁ x₂) ρ) (ha : Γ ⊢[PRAAx] ZT.eq (nsq a₁ a₂) ρ) :
    Γ ⊢[PRAAx] zle (dot x₁ x₂ a₁ a₂) ρ := by
  have c := ZT.toZ_eq (tangent_gap hx ha)
  have h2 : Γ ⊢[PRAAx] zle (ZT.natLit 0) (ZT.natLit 2 * (ρ - dot x₁ x₂ a₁ a₂)) := by
    refine zle_of_comb (ZT.toZ Γ (x₁ - a₁) ^ 2 + ZT.toZ Γ (x₂ - a₂) ^ 2) ?_ (nn_add (nn_zsq _) (nn_zsq _))
    gsimp at c ⊢
    linear_combination (-1 : Groth (Q Γ)) * c
  have one_two : Γ ⊢[PRAAx] zle (ZT.natLit 1) (ZT.natLit 2) := by
    refine zle_of_comb 1 ?_ nn_one
    gsimp
    ring
  have k := znn_of_pos_mul one_two h2
  refine zle_of_comb (zsl k) ?_ (nn_zsl _)
  gsimp
  ring

/-! ## The power of a point -/

/-- (C5): `(t − u)(|v|² t u − Pow(P)) = 0` for two points of the circle on a line through `P`. -/
theorem power_product {w₁ w₂ v₁ v₂ t u ρ : ZT n}
    (ht : Γ ⊢[PRAAx] ZT.eq (nsq (w₁ + t * v₁) (w₂ + t * v₂)) ρ)
    (hu : Γ ⊢[PRAAx] ZT.eq (nsq (w₁ + u * v₁) (w₂ + u * v₂)) ρ) :
    Γ ⊢[PRAAx] ZT.eq ((t - u) * (nsq v₁ v₂ * (t * u) - (nsq w₁ w₂ - ρ))) (ZT.natLit 0) := by
  have et := ZT.toZ_eq ht
  have eu := ZT.toZ_eq hu
  apply ZT.derive
  gsimp at et eu ⊢
  linear_combination ζ u * et - ζ t * eu

/-- The sum of the two parameters: `(t − u)(|v|² (t + u) + 2 (P − O) · v) = 0`. -/
theorem power_sum {w₁ w₂ v₁ v₂ t u ρ : ZT n}
    (ht : Γ ⊢[PRAAx] ZT.eq (nsq (w₁ + t * v₁) (w₂ + t * v₂)) ρ)
    (hu : Γ ⊢[PRAAx] ZT.eq (nsq (w₁ + u * v₁) (w₂ + u * v₂)) ρ) :
    Γ ⊢[PRAAx] ZT.eq ((t - u) * (nsq v₁ v₂ * (t + u) + ZT.natLit 2 * dot w₁ w₂ v₁ v₂)) (ZT.natLit 0) := by
  have et := ZT.toZ_eq ht
  have eu := ZT.toZ_eq hu
  apply ZT.derive
  gsimp at et eu ⊢
  linear_combination et - eu

/-- (C6): `|P − O|² = |P − T|² + ρ` for a tangent at `T` (`p = P − T`, `r = T − O`). -/
theorem tangent_power {p₁ p₂ r₁ r₂ ρ : ZT n}
    (hr : Γ ⊢[PRAAx] ZT.eq (nsq r₁ r₂) ρ) (hp : Γ ⊢[PRAAx] ZT.eq (dot p₁ p₂ r₁ r₂) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (nsq (p₁ + r₁) (p₂ + r₂)) (nsq p₁ p₂ + ρ) := by
  have er := ZT.toZ_eq hr
  have ep := ZT.toZ_eq hp
  apply ZT.derive
  gsimp at er ep ⊢
  linear_combination er + 2 * ep

/-! ## Three common points -/

/-- Three common points of two circles: `2 [y − x, z − x] (O′ − O)₁ = 0`. -/
theorem three_common₁ {x₁ x₂ y₁ y₂ z₁ z₂ o₁ o₂ q₁ q₂ ρ σ : ZT n}
    (hx1 : Γ ⊢[PRAAx] ZT.eq (nsq (x₁ - o₁) (x₂ - o₂)) ρ) (hy1 : Γ ⊢[PRAAx] ZT.eq (nsq (y₁ - o₁) (y₂ - o₂)) ρ)
    (hz1 : Γ ⊢[PRAAx] ZT.eq (nsq (z₁ - o₁) (z₂ - o₂)) ρ) (hx2 : Γ ⊢[PRAAx] ZT.eq (nsq (x₁ - q₁) (x₂ - q₂)) σ)
    (hy2 : Γ ⊢[PRAAx] ZT.eq (nsq (y₁ - q₁) (y₂ - q₂)) σ)
    (hz2 : Γ ⊢[PRAAx] ZT.eq (nsq (z₁ - q₁) (z₂ - q₂)) σ) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit 2 * det (y₁ - x₁) (y₂ - x₂) (z₁ - x₁) (z₂ - x₂) * (q₁ - o₁))
      (ZT.natLit 0) := by
  have ex1 := ZT.toZ_eq hx1
  have ey1 := ZT.toZ_eq hy1
  have ez1 := ZT.toZ_eq hz1
  have ex2 := ZT.toZ_eq hx2
  have ey2 := ZT.toZ_eq hy2
  have ez2 := ZT.toZ_eq hz2
  apply ZT.derive
  gsimp at ex1 ey1 ez1 ex2 ey2 ez2 ⊢
  linear_combination (ζ z₂ - ζ x₂) * (ey1 - ex1 - (ey2 - ex2)) - (ζ y₂ - ζ x₂) * (ez1 - ex1 - (ez2 - ex2))

/-- Three common points of two circles: `2 [y − x, z − x] (O′ − O)₂ = 0`. -/
theorem three_common₂ {x₁ x₂ y₁ y₂ z₁ z₂ o₁ o₂ q₁ q₂ ρ σ : ZT n}
    (hx1 : Γ ⊢[PRAAx] ZT.eq (nsq (x₁ - o₁) (x₂ - o₂)) ρ) (hy1 : Γ ⊢[PRAAx] ZT.eq (nsq (y₁ - o₁) (y₂ - o₂)) ρ)
    (hz1 : Γ ⊢[PRAAx] ZT.eq (nsq (z₁ - o₁) (z₂ - o₂)) ρ) (hx2 : Γ ⊢[PRAAx] ZT.eq (nsq (x₁ - q₁) (x₂ - q₂)) σ)
    (hy2 : Γ ⊢[PRAAx] ZT.eq (nsq (y₁ - q₁) (y₂ - q₂)) σ)
    (hz2 : Γ ⊢[PRAAx] ZT.eq (nsq (z₁ - q₁) (z₂ - q₂)) σ) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit 2 * det (y₁ - x₁) (y₂ - x₂) (z₁ - x₁) (z₂ - x₂) * (q₂ - o₂))
      (ZT.natLit 0) := by
  have ex1 := ZT.toZ_eq hx1
  have ey1 := ZT.toZ_eq hy1
  have ez1 := ZT.toZ_eq hz1
  have ex2 := ZT.toZ_eq hx2
  have ey2 := ZT.toZ_eq hy2
  have ez2 := ZT.toZ_eq hz2
  apply ZT.derive
  gsimp at ex1 ey1 ez1 ex2 ey2 ez2 ⊢
  linear_combination (ζ y₁ - ζ x₁) * (ez1 - ex1 - (ez2 - ex2)) - (ζ z₁ - ζ x₁) * (ey1 - ex1 - (ey2 - ex2))

/-! ## The rational parametrization -/

/-- (C14) with `t = m / k`: the parametrized point is on the circle. -/
theorem parameter_on_circle (a₁ a₂ k m : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (nsq ((k * k - m * m) * a₁ - ZT.natLit 2 * m * k * a₂) ((k * k - m * m) * a₂ + ZT.natLit 2 * m * k * a₁))
      (ZT.sq (k * k + m * m) * nsq a₁ a₂) := by
  geo

/-- The inverse of (C14), first coordinate. -/
theorem parameter_inverse₁ {a₁ a₂ x₁ x₂ ρ : ZT n}
    (ha : Γ ⊢[PRAAx] ZT.eq (nsq a₁ a₂) ρ) (hx : Γ ⊢[PRAAx] ZT.eq (nsq x₁ x₂) ρ) :
    Γ ⊢[PRAAx] ZT.eq
      ((pk a₁ a₂ x₁ x₂ ρ * pk a₁ a₂ x₁ x₂ ρ - pm a₁ a₂ x₁ x₂ * pm a₁ a₂ x₁ x₂) * a₁ -
        ZT.natLit 2 * pm a₁ a₂ x₁ x₂ * pk a₁ a₂ x₁ x₂ ρ * a₂)
      ((pk a₁ a₂ x₁ x₂ ρ * pk a₁ a₂ x₁ x₂ ρ + pm a₁ a₂ x₁ x₂ * pm a₁ a₂ x₁ x₂) * x₁) := by
  have ea := ZT.toZ_eq ha
  have ex := ZT.toZ_eq hx
  apply ZT.derive
  gsimp at ea ex ⊢
  linear_combination
    (-(ζ x₁ * ζ x₁ + ζ x₂ * ζ x₂) * ζ a₁ + (2 * (ζ a₁ * ζ x₁ + ζ a₂ * ζ x₂) + ζ ρ) * ζ x₁) * ea +
      (-ζ ρ * ζ a₁ - (ζ a₁ * ζ a₁ + ζ a₂ * ζ a₂) * ζ x₁) * ex

/-- The inverse of (C14), second coordinate. -/
theorem parameter_inverse₂ {a₁ a₂ x₁ x₂ ρ : ZT n}
    (ha : Γ ⊢[PRAAx] ZT.eq (nsq a₁ a₂) ρ) (hx : Γ ⊢[PRAAx] ZT.eq (nsq x₁ x₂) ρ) :
    Γ ⊢[PRAAx] ZT.eq
      ((pk a₁ a₂ x₁ x₂ ρ * pk a₁ a₂ x₁ x₂ ρ - pm a₁ a₂ x₁ x₂ * pm a₁ a₂ x₁ x₂) * a₂ +
        ZT.natLit 2 * pm a₁ a₂ x₁ x₂ * pk a₁ a₂ x₁ x₂ ρ * a₁)
      ((pk a₁ a₂ x₁ x₂ ρ * pk a₁ a₂ x₁ x₂ ρ + pm a₁ a₂ x₁ x₂ * pm a₁ a₂ x₁ x₂) * x₂) := by
  have ea := ZT.toZ_eq ha
  have ex := ZT.toZ_eq hx
  apply ZT.derive
  gsimp at ea ex ⊢
  linear_combination
    (-(ζ x₁ * ζ x₁ + ζ x₂ * ζ x₂) * ζ a₂ + (2 * (ζ a₁ * ζ x₁ + ζ a₂ * ζ x₂) + ζ ρ) * ζ x₂) * ea +
      (-ζ ρ * ζ a₂ - (ζ a₁ * ζ a₁ + ζ a₂ * ζ a₂) * ζ x₂) * ex

end LeanProofs.IPRA.Geometry.CirclePower
